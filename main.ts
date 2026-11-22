// main.ts is mend, the CLI SPEC.md specifies. Node 22, the standard library alone;
// run it as `node main.ts [options] [PATCH]`.
//
// Architecture (Builder B): the three text formats (unified, SEARCH/REPLACE, V4A) are only
// parsers. Each parser turns its format into the same list of EditOp objects, and ONE
// apply engine executes every EditOp: one indexed matcher (section 5), one line
// replacer (context lines come from the file, tier-2 re-indent) and one position
// resolver per format (nearest for unified, exactly-once for SEARCH/REPLACE,
// first-at-or-after-cursor for V4A). JSON edits (section 9) keep the starter's
// exact-string behaviour. Parse happens for the whole patch before any edit runs,
// so a parse error is always reported before any file is looked at (section 2).
// Safety of every path an edit names is checked before anything else about it
// (section 10). A failed edit changes nothing and later edits still run; when any
// edit failed nothing is written (section 10).

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  /** Successful move edits, in patch order: [old path, new path]. */
  readonly moves: Array<[string, string]> = [];
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

type Edit = (tree: Tree) => void;

/** One file's lines with its own line break and whether it ends with one (section 3). */
interface FileState {
  lines: string[];
  br: string;
  finalBreak: boolean;
}

function splitFile(text: string): FileState {
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  if (text === '') return { lines: [], br, finalBreak: false };
  const parts = text.split(br);
  const finalBreak = text.endsWith(br);
  if (finalBreak) parts.pop();
  return { lines: parts, br, finalBreak };
}

function joinFile(st: FileState): string {
  if (st.lines.length === 0) return '';
  return st.lines.join(st.br) + (st.finalBreak ? st.br : '');
}

function leadingWs(line: string): string {
  const m = /^[ \t]*/.exec(line);
  return m === null ? '' : m[0];
}

/** A line as tier t of section 5 sees it. */
function normLine(line: string, tier: number): string {
  if (tier === 0) return line;
  if (tier === 1) return line.replace(/[ \t]+$/, '');
  return line.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
}

/**
 * All occurrences of O in `lines` at one tier, found through an index built once
 * over the file's current lines: the key of a window of O's length, mapped to the
 * positions where it occurs. Occurrences may overlap. Only positions at or after
 * `minPos` count, and for an end-of-file chunk only ones ending at the last line.
 */
function occurrencesAt(lines: string[], o: string[], tier: number, minPos: number, eofOnly: boolean): number[] {
  const k = o.length;
  const key = o.map((l) => normLine(l, tier)).join('\u0000');
  const index = new Map<string, number[]>();
  for (let i = 0; i + k <= lines.length; i += 1) {
    if (i < minPos) continue;
    if (eofOnly && i + k !== lines.length) continue;
    const w = lines.slice(i, i + k).map((l) => normLine(l, tier)).join('\u0000');
    const arr = index.get(w);
    if (arr === undefined) index.set(w, [i]);
    else arr.push(i);
  }
  return index.get(key) ?? [];
}

/** The first tier (0, then 1, then 2; only 0 with --strict) at which O occurs. */
function findTier(lines: string[], o: string[], strict: boolean, minPos: number, eofOnly: boolean): { tier: number; positions: number[] } | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    const positions = occurrencesAt(lines, o, t, minPos, eofOnly);
    if (positions.length > 0) return { tier: t, positions };
  }
  return null;
}

/**
 * The lines that replace a matched occurrence. A context line (ctxMap[j] >= 0) is
 * written as the file's own matched line, never the patch's. At tier 2 every other
 * line is re-indented: P, the leading spaces/tabs of O's first line, is replaced
 * by F, those of the file's first matched line. At tiers 0 and 1 lines are as-is.
 * ctxMap[j] is the index into O of N[j] when N[j] is a context line, else -1.
 */
function buildReplacement(o: string[], n: string[], ctxMap: number[], fileLines: string[], pos: number, tier: number): string[] {
  const out: string[] = [];
  const p = o.length > 0 ? leadingWs(o[0]) : '';
  const f = pos < fileLines.length ? leadingWs(fileLines[pos]!) : '';
  for (let j = 0; j < n.length; j += 1) {
    const ci = ctxMap[j]!;
    if (ci >= 0) {
      out.push(fileLines[pos + ci]!);
      continue;
    }
    let line = n[j]!;
    if (tier === 2 && line !== '' && line.trim() !== '' && line.startsWith(p)) line = f + line.slice(p.length);
    out.push(line);
  }
  return out;
}

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const br = nl > 0 && before[nl - 1] === '\r' ? '\r\n' : '\n';
      const lines = before === '' ? [] : before.split(br);
      const final = before !== '' && before.endsWith(br);
      if (final) lines.pop();
      if (line < 0 || line > lines.length) throw new Fail('no-match', p);
      lines.splice(line, 0, ...add);
      tree.now.set(p, lines.length === 0 ? '' : lines.join(br) + (final ? br : ''));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

/* ------------------------------------------------------------------ */
/* Unified diffs (section 6), parsed into EditOps, applied by the    */
/* one shared engine above.                                          */
/* ------------------------------------------------------------------ */

/** One body line of a hunk: context, old (-), new (+), or a backslash line. */
interface BodyLine {
  kind: 'ctx' | 'old' | 'new' | 'bs';
  text: string;
}

interface Hunk {
  /** A: the 1-based old start from the @@ header. */
  a: number;
  body: BodyLine[];
  /** O: context and - lines, in body order. */
  o: string[];
  /** N: context and + lines, in body order. */
  n: string[];
  /** ctxMap[j]: index into O of N[j] when N[j] is a context line, else -1. */
  ctxMap: number[];
  /** True when a \ line follows the hunk's last context or + line. */
  noEol: boolean;
}

interface UnifiedSection {
  oldPath: string | null; // null: /dev/null (no file)
  newPath: string | null;
  newFile: boolean;
  deletedFile: boolean;
  hunks: Hunk[];
}

/** The path after `--- ` / `+++ `: text after four chars, up to first tab, trimmed, a/ or b/ removed. */
function unifiedPath(line: string): string {
  let p = line.slice(4).split('\t')[0]!.trim();
  if (p.startsWith('a/') || p.startsWith('b/')) p = p.slice(2);
  return p;
}

function parseDiffGit(line: string): { old: string; nw: string } | null {
  const parts = line.slice('diff --git '.length).split(/\s+/);
  if (parts.length !== 2 || !parts[0]!.startsWith('a/') || !parts[1]!.startsWith('b/')) return null;
  return { old: parts[0]!.slice(2), nw: parts[1]!.slice(2) };
}

const HUNK_RE = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/;

function isBodyLine(l: string): boolean {
  return l === '' || l[0] === ' ' || l[0] === '-' || l[0] === '+' || l[0] === '\\';
}

/** Collect a hunk body starting at `start`; empty lines at its end are not part of it. */
function collectHunkBody(lines: string[], start: number): { body: BodyLine[]; next: number } {
  const raw: BodyLine[] = [];
  let i = start;
  while (i < lines.length) {
    const l = lines[i]!;
    // The body ends at a `--- ` line followed by a `+++ ` line (a new section),
    // even though such a line starts with `-`.
    if (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) break;
    if (!isBodyLine(l)) break;
    if (l === '') raw.push({ kind: 'ctx', text: '' });
    else if (l[0] === ' ') raw.push({ kind: 'ctx', text: l.slice(1) });
    else if (l[0] === '-') raw.push({ kind: 'old', text: l.slice(1) });
    else if (l[0] === '+') raw.push({ kind: 'new', text: l.slice(1) });
    else raw.push({ kind: 'bs', text: l });
    i += 1;
  }
  // Empty lines at the end of a body are not part of it: drop trailing
  // zero-length patch lines (kept as context lines with empty text).
  while (raw.length > 0) {
    const last = raw[raw.length - 1]!;
    if (last.kind === 'ctx' && last.text === '' && lines[i - 1] === '') {
      raw.pop();
      i -= 1;
    } else break;
  }
  return { body: raw, next: i };
}

function makeHunk(a: number, body: BodyLine[]): Hunk {
  const o: string[] = [];
  const n: string[] = [];
  const ctxMap: number[] = [];
  for (const b of body) {
    if (b.kind === 'ctx') {
      ctxMap.push(o.length);
      o.push(b.text);
      n.push(b.text);
    } else if (b.kind === 'old') {
      o.push(b.text);
    } else if (b.kind === 'new') {
      ctxMap.push(-1);
      n.push(b.text);
    }
  }
  let noEol = false;
  for (let k = body.length - 1; k >= 0; k -= 1) {
    const b = body[k]!;
    if (b.kind === 'ctx' || b.kind === 'new') {
      noEol = k + 1 < body.length && body[k + 1]!.kind === 'bs';
      break;
    }
  }
  return { a, body, o, n, ctxMap, noEol };
}

function parseUnified(lines: string[], strict: boolean): Edit[] {
  interface SecWork {
    headerOld: string | null;
    headerNew: string | null;
    renameFrom: string | null;
    renameTo: string | null;
    diffOld: string | null;
    diffNew: string | null;
    newFile: boolean;
    deletedFile: boolean;
    hasHeaderPair: boolean;
    hunks: Hunk[];
  }
  const sections: SecWork[] = [];
  let sec: SecWork | null = null;
  let inHeader = false;
  let i = 0;
  const openSection = (diffOld: string | null, diffNew: string | null): SecWork => {
    const s: SecWork = { headerOld: null, headerNew: null, renameFrom: null, renameTo: null, diffOld, diffNew, newFile: false, deletedFile: false, hasHeaderPair: false, hunks: [] };
    sections.push(s);
    sec = s;
    inHeader = true;
    return s;
  };
  while (i < lines.length) {
    const line = lines[i]!;
    const ln = i + 1;
    if (line.startsWith('diff --git ')) {
      const m = parseDiffGit(line);
      if (m === null) throw new Exit2(`error: parse ${ln}`);
      openSection(m.old, m.nw);
      i += 1;
      continue;
    }
    if (line.startsWith('@@')) {
      const m = HUNK_RE.exec(line);
      if (m === null) throw new Exit2(`error: parse ${ln}`);
      if (sec === null) throw new Exit2(`error: parse ${ln}`);
      const got = collectHunkBody(lines, i + 1);
      sec.hunks.push(makeHunk(parseInt(m[1]!, 10), got.body));
      inHeader = false;
      i = got.next;
      continue;
    }
    if (line.startsWith('--- ')) {
      const next = lines[i + 1];
      if (next === undefined || !next.startsWith('+++ ')) {
        // Inside a section's header a --- line must be followed by +++.
        if (sec !== null && inHeader) throw new Exit2(`error: parse ${ln + 1}`);
        i += 1;
        continue;
      }
      if (sec !== null && inHeader && !sec.hasHeaderPair) {
        sec.headerOld = unifiedPath(line);
        sec.headerNew = unifiedPath(next);
        sec.hasHeaderPair = true;
        i += 2;
        continue;
      }
      const s = openSection(null, null);
      s.headerOld = unifiedPath(line);
      s.headerNew = unifiedPath(next);
      s.hasHeaderPair = true;
      i += 2;
      continue;
    }
    if (sec !== null && inHeader) {
      if (line.startsWith('rename from ')) sec.renameFrom = line.slice('rename from '.length).trim();
      else if (line.startsWith('rename to ')) sec.renameTo = line.slice('rename to '.length).trim();
      else if (line === 'new file mode' || line.startsWith('new file mode ')) sec.newFile = true;
      else if (line === 'deleted file mode' || line.startsWith('deleted file mode ')) sec.deletedFile = true;
      // index, old/new mode, similarity/dissimilarity index, Index: and any
      // other header line are ignored.
      i += 1;
      continue;
    }
    // Outside bodies, lines that are not part of a section header are ignored.
    i += 1;
  }
  return sections.map((w) => {
    const rawOld = w.headerOld ?? w.renameFrom ?? w.diffOld;
    const rawNew = w.headerNew ?? w.renameTo ?? w.diffNew;
    const oldPath = rawOld === undefined || rawOld === null || rawOld === '/dev/null' ? null : rawOld;
    const newPath = rawNew === undefined || rawNew === null || rawNew === '/dev/null' ? null : rawNew;
    const secOut: UnifiedSection = { oldPath, newPath, newFile: w.newFile, deletedFile: w.deletedFile, hunks: w.hunks };
    return unifiedSectionEdit(secOut, strict);
  });
}

/** Apply one hunk to a working FileState; d is the running length drift of this section. */
function applyHunk(st: FileState, h: Hunk, d: number, path: string, strict: boolean): number {
  if (h.o.length > 0) {
    const found = findTier(st.lines, h.o, strict, 0, false);
    if (found === null) throw new Fail('no-match', path);
    const target = h.a - 1 + d;
    let best = found.positions[0]!;
    for (const pos of found.positions) {
      if (Math.abs(pos - target) < Math.abs(best - target)) best = pos;
    }
    const rep = buildReplacement(h.o, h.n, h.ctxMap, st.lines, best, found.tier);
    if (best + h.o.length === st.lines.length) st.finalBreak = !h.noEol;
    st.lines.splice(best, h.o.length, ...rep);
  } else {
    const at = Math.min(Math.max(h.a + d, 0), st.lines.length);
    if (at === st.lines.length) st.finalBreak = !h.noEol;
    st.lines.splice(at, 0, ...h.n);
  }
  return d + (h.n.length - h.o.length);
}

function unifiedSectionEdit(sec: UnifiedSection, strict: boolean): Edit {
  return (tree) => {
    const isCreate = sec.oldPath === null || sec.newFile;
    const isDelete = !isCreate && (sec.newPath === null || sec.deletedFile);
    if (isCreate) {
      const p = sec.newPath;
      if (p === null) return; // both paths /dev/null: nothing to create
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      const plus: string[] = [];
      for (const h of sec.hunks) for (const b of h.body) if (b.kind === 'new') plus.push(b.text);
      let finalBreak = true;
      // The last + line of the section: a \ line right after it means no break.
      outer: for (let hi = sec.hunks.length - 1; hi >= 0; hi -= 1) {
        const h = sec.hunks[hi]!;
        for (let k = h.body.length - 1; k >= 0; k -= 1) {
          if (h.body[k]!.kind === 'new') {
            finalBreak = !(k + 1 < h.body.length && h.body[k + 1]!.kind === 'bs');
            break outer;
          }
        }
      }
      tree.now.set(p, plus.length === 0 ? '' : plus.join('\n') + (finalBreak ? '\n' : ''));
      return;
    }
    if (isDelete) {
      const p = sec.oldPath;
      if (p === null) return;
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) === null) throw new Fail('missing', p);
      tree.now.set(p, null);
      return;
    }
    const oldP = sec.oldPath!;
    const newP = sec.newPath!;
    const isMove = oldP !== newP;
    if (!safe(oldP)) throw new Fail('unsafe', oldP);
    if (isMove && !safe(newP)) throw new Fail('unsafe', newP);
    const before = tree.get(oldP);
    if (before === null) throw new Fail('missing', oldP);
    if (isMove && tree.get(newP) !== null) throw new Fail('exists', newP);
    const st = splitFile(before);
    let d = 0;
    for (const h of sec.hunks) d = applyHunk(st, h, d, oldP, strict);
    const out = joinFile(st);
    if (isMove) {
      tree.now.set(newP, out);
      tree.now.set(oldP, null);
      tree.moves.push([oldP, newP]);
    } else {
      tree.now.set(oldP, out);
    }
  };
}

/* ------------------------------------------------------------------ */
/* SEARCH/REPLACE blocks (section 7).                                */
/* ------------------------------------------------------------------ */

interface SrBlock {
  path: string;
  oldLines: string[];
  newLines: string[];
}

function parseSearchReplace(lines: string[], strict: boolean): Edit[] {
  const blocks: SrBlock[] = [];
  let prevEnd = -1;
  let prevPath: string | null = null;
  let i = 0;
  while (i < lines.length) {
    if (lines[i]!.trimEnd() !== '<<<<<<< SEARCH') {
      i += 1;
      continue;
    }
    const s = i;
    let path: string | null = null;
    for (let j = s - 1; j > prevEnd; j -= 1) {
      const l = lines[j]!;
      if (blank(l)) continue;
      if (l.trim().startsWith('```')) continue;
      path = l.trim();
      break;
    }
    if (path === null) path = prevPath;
    if (path === null) throw new Exit2(`error: parse ${s + 1}`);
    let eq = -1;
    for (let j = s + 1; j < lines.length; j += 1) {
      if (lines[j]!.trimEnd() === '=======') {
        eq = j;
        break;
      }
    }
    let end = -1;
    if (eq >= 0) {
      for (let j = eq + 1; j < lines.length; j += 1) {
        if (lines[j]!.trimEnd() === '>>>>>>> REPLACE') {
          end = j;
          break;
        }
      }
    }
    if (eq < 0 || end < 0) throw new Exit2(`error: parse ${s + 1}`);
    blocks.push({ path, oldLines: lines.slice(s + 1, eq), newLines: lines.slice(eq + 1, end) });
    prevPath = path;
    prevEnd = end;
    i = end + 1;
  }
  return blocks.map((b) => srBlockEdit(b, strict));
}

function srBlockEdit(b: SrBlock, strict: boolean): Edit {
  return (tree) => {
    if (!safe(b.path)) throw new Fail('unsafe', b.path);
    if (b.oldLines.length === 0) {
      if (tree.get(b.path) !== null) throw new Fail('exists', b.path);
      tree.now.set(b.path, b.newLines.length === 0 ? '' : b.newLines.join('\n') + '\n');
      return;
    }
    const before = tree.get(b.path);
    if (before === null) throw new Fail('missing', b.path);
    const st = splitFile(before);
    const found = findTier(st.lines, b.oldLines, strict, 0, false);
    if (found === null) throw new Fail('no-match', b.path);
    if (found.positions.length > 1) throw new Fail('ambiguous', b.path);
    const pos = found.positions[0]!;
    const rep = buildReplacement(b.oldLines, b.newLines, b.newLines.map(() => -1), st.lines, pos, found.tier);
    st.lines.splice(pos, b.oldLines.length, ...rep);
    tree.now.set(b.path, joinFile(st));
  };
}

/* ------------------------------------------------------------------ */
/* V4A patches (section 8).                                          */
/* ------------------------------------------------------------------ */

interface V4aChunk {
  anchor: string | null;
  o: string[];
  n: string[];
  ctxMap: number[];
  eof: boolean;
}

interface V4aSection {
  kind: 'add' | 'delete' | 'update';
  path: string;
  lineNo: number;
  /** Add File lines, in order. */
  addLines: string[];
  moveTo: string | null;
  chunks: V4aChunk[];
}

const SECTION_PREFIX: Array<[string, 'add' | 'delete' | 'update']> = [
  ['*** Add File: ', 'add'],
  ['*** Delete File: ', 'delete'],
  ['*** Update File: ', 'update'],
];

function parseV4a(lines: string[], strict: boolean): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = -1;
  for (let k = lines.length - 1; k >= 0; k -= 1) {
    if (!blank(lines[k]!)) {
      last = k;
      break;
    }
  }
  if (lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  interface RawSection {
    kind: 'add' | 'delete' | 'update';
    path: string;
    lineNo: number;
    raw: Array<{ text: string; num: number }>;
  }
  const rawSections: RawSection[] = [];
  let cur: RawSection | null = null;
  for (let i = first + 1; i < last; i += 1) {
    const line = lines[i]!;
    const ln = i + 1;
    if (blank(line)) {
      if (cur !== null) cur.raw.push({ text: line, num: ln });
      continue;
    }
    let matched: RawSection | null = null;
    for (const [prefix, kind] of SECTION_PREFIX) {
      if (line.startsWith(prefix)) {
        matched = { kind, path: line.slice(prefix.length).trim(), lineNo: ln, raw: [] };
        break;
      }
    }
    if (matched !== null) {
      rawSections.push(matched);
      cur = matched;
      continue;
    }
    if (cur === null) throw new Exit2(`error: parse ${ln}`);
    cur.raw.push({ text: line, num: ln });
  }
  const sections: V4aSection[] = rawSections.map((rs) => {
    // Blank lines at the end of a section are not part of it.
    while (rs.raw.length > 0 && blank(rs.raw[rs.raw.length - 1]!.text)) rs.raw.pop();
    if (rs.kind === 'add') {
      const addLines: string[] = [];
      for (const r of rs.raw) {
        if (r.text === '') addLines.push('');
        else if (r.text.startsWith('+')) addLines.push(r.text.slice(1));
        else throw new Exit2(`error: parse ${r.num}`);
      }
      return { kind: 'add', path: rs.path, lineNo: rs.lineNo, addLines, moveTo: null, chunks: [] };
    }
    if (rs.kind === 'delete') {
      for (const r of rs.raw) throw new Exit2(`error: parse ${r.num}`);
      return { kind: 'delete', path: rs.path, lineNo: rs.lineNo, addLines: [], moveTo: null, chunks: [] };
    }
    // Update File: optional Move to first, then chunks.
    let moveTo: string | null = null;
    let idx = 0;
    if (rs.raw.length > 0 && rs.raw[0]!.text.startsWith('*** Move to: ')) {
      moveTo = rs.raw[0]!.text.slice('*** Move to: '.length).trim();
      idx = 1;
    }
    const chunks: V4aChunk[] = [];
    let chunk: { anchor: string | null; body: Array<{ text: string; num: number }>; eof: boolean } | null = null;
    const closeChunk = (): void => {
      if (chunk === null) return;
      const o: string[] = [];
      const n: string[] = [];
      const ctxMap: number[] = [];
      for (const b of chunk.body) {
        const t = b.text;
        if (t === '' || t[0] === ' ') {
          ctxMap.push(o.length);
          o.push(t === '' ? '' : t.slice(1));
          n.push(t === '' ? '' : t.slice(1));
        } else if (t[0] === '-') {
          o.push(t.slice(1));
        } else if (t[0] === '+') {
          ctxMap.push(-1);
          n.push(t.slice(1));
        }
      }
      chunks.push({ anchor: chunk.anchor, o, n, ctxMap, eof: chunk.eof });
      chunk = null;
    };
    for (; idx < rs.raw.length; idx += 1) {
      const r = rs.raw[idx]!;
      const t = r.text;
      if (t.startsWith('@@')) {
        closeChunk();
        const anchor = t.slice(2).trim();
        chunk = { anchor: anchor === '' ? null : anchor, body: [], eof: false };
        continue;
      }
      if (t === '*** End of File') {
        if (chunk === null) throw new Exit2(`error: parse ${r.num}`);
        chunk.eof = true;
        closeChunk();
        continue;
      }
      if (t === '' || t[0] === ' ' || t[0] === '-' || t[0] === '+') {
        if (chunk === null) {
          if (chunks.length > 0) throw new Exit2(`error: parse ${r.num}`);
          chunk = { anchor: null, body: [], eof: false };
        }
        chunk.body.push(r);
        continue;
      }
      throw new Exit2(`error: parse ${r.num}`);
    }
    closeChunk();
    if (chunks.length === 0 && moveTo === null) throw new Exit2(`error: parse ${rs.lineNo}`);
    return { kind: 'update', path: rs.path, lineNo: rs.lineNo, addLines: [], moveTo, chunks };
  });
  return sections.map((s) => v4aSectionEdit(s, strict));
}

function v4aSectionEdit(s: V4aSection, strict: boolean): Edit {
  return (tree) => {
    if (!safe(s.path)) throw new Fail('unsafe', s.path);
    if (s.kind === 'add') {
      if (tree.get(s.path) !== null) throw new Fail('exists', s.path);
      tree.now.set(s.path, s.addLines.length === 0 ? '' : s.addLines.join('\n') + '\n');
      return;
    }
    if (s.kind === 'delete') {
      if (tree.get(s.path) === null) throw new Fail('missing', s.path);
      tree.now.set(s.path, null);
      return;
    }
    const newPath = s.moveTo;
    if (newPath !== null && !safe(newPath)) throw new Fail('unsafe', newPath);
    const before = tree.get(s.path);
    if (before === null) throw new Fail('missing', s.path);
    if (newPath !== null && tree.get(newPath) !== null) throw new Fail('exists', newPath);
    const st = splitFile(before);
    let cursor = 0;
    for (const chunk of s.chunks) {
      if (chunk.anchor !== null) {
        const foundAnchor = findTier(st.lines, [chunk.anchor], strict, cursor, false);
        if (foundAnchor === null) throw new Fail('no-match', s.path);
        cursor = foundAnchor.positions[0]! + 1;
      }
      if (chunk.o.length === 0) {
        const at = chunk.eof ? st.lines.length : cursor;
        st.lines.splice(at, 0, ...chunk.n);
        cursor = at + chunk.n.length;
        continue;
      }
      const found = findTier(st.lines, chunk.o, strict, cursor, chunk.eof);
      if (found === null) throw new Fail('no-match', s.path);
      const pos = found.positions[0]!;
      const rep = buildReplacement(chunk.o, chunk.n, chunk.ctxMap, st.lines, pos, found.tier);
      st.lines.splice(pos, chunk.o.length, ...rep);
      cursor = pos + rep.length;
    }
    const out = joinFile(st);
    if (newPath !== null) {
      tree.now.set(newPath, out);
      tree.now.set(s.path, null);
      tree.moves.push([s.path, newPath]);
    } else {
      tree.now.set(s.path, out);
    }
  };
}

/* ------------------------------------------------------------------ */
/* Invocation, output and exit codes (sections 1, 2 and 10).         */
/* ------------------------------------------------------------------ */

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    if (kind === 'json') edits = jsonEdits(text, lines);
    else if (kind === 'unified') edits = parseUnified(lines, strict);
    else if (kind === 'search-replace') edits = parseSearchReplace(lines, strict);
    else edits = parseV4a(lines, strict);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    const movesBefore = tree.moves.length;
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      tree.moves.length = movesBefore;
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  // Rows: one per changed path in byte order, with R replacing a move's D+A pair.
  const rPairs: Array<[string, string]> = [];
  for (const [oldP, newP] of tree.moves) {
    if (tree.original(oldP) !== null && tree.get(oldP) === null && tree.original(newP) === null && tree.get(newP) !== null) rPairs.push([oldP, newP]);
  }
  const rOlds = new Set(rPairs.map((p) => p[0]));
  const rNews = new Set(rPairs.map((p) => p[1]));
  const rows: Array<{ key: string; line: string }> = [];
  for (const p of [...tree.now.keys()]) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    if (rOlds.has(p) || rNews.has(p)) continue;
    rows.push({ key: p, line: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}` });
  }
  for (const [o, n] of rPairs) rows.push({ key: n, line: `R ${o} -> ${n}` });
  rows.sort((a, b) => Buffer.compare(Buffer.from(a.key), Buffer.from(b.key)));
  if (!check) {
    for (const p of [...tree.now.keys()].sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)))) {
      const was = tree.original(p);
      const now = tree.now.get(p)!;
      if (was === now) continue;
      if (now === null) rmSync(p, { force: true });
      else {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, now);
      }
    }
  }
  return { code: 0, out: [...rows.map((r) => r.line), `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`] };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
