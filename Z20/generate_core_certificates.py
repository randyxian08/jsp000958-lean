#!/usr/bin/env python3
"""Untrusted proof generator. Output Lean terms must be kernel checked.

Input certificates: ipitchford/z20-cochromatic, pinned below. Mathematical
reduction and original SAT certificates belong to their credited authors.
This program trims pure-RUP LRAT by proof dependency, independently replays
unit propagation, and attaches two explicit disjoint homogeneous 4-sets to
every retained input clause. No graph claim is inferred from hashes alone.
"""
from __future__ import annotations
import hashlib
import itertools
import json
import sys
import urllib.request
from pathlib import Path

PIN = "3c7e520fdc0615f5c700761c2b1e5108dcc836e7"
BASE = f"https://raw.githubusercontent.com/ipitchford/z20-cochromatic/{PIN}/certificates/"
GRAPHS = ["OsHHirKdlp[IFVI|KpqfR", "Ov?IXZIhlRWjUXL[iphst"]
EXPECTED = ["cbfea7b0b2cb712ad8b4f8b129f74c7f010e879064414eaef76e74aa88be3f44", "d3d96a3c2a719c753242673b81aabc3977c5e435bb5996b4c58c85a82d11dc5a"]

def get(name: str, directory: Path) -> bytes:
    p = directory / name
    if not p.exists():
        with urllib.request.urlopen(BASE + name, timeout=90) as response:
            p.write_bytes(response.read())
    return p.read_bytes()

def read_cnf(data: bytes):
    lines = [line for line in data.decode().splitlines() if line.strip() and not line.startswith('c')]
    h = lines.pop(0).split()
    assert h[:2] == ['p', 'cnf']
    clauses, c = [], []
    for x in map(int, ' '.join(lines).split()):
        if x == 0:
            clauses.append(tuple(c)); c = []
        else:
            assert 0 < abs(x) <= int(h[2]); c.append(x)
    assert not c and len(clauses) == int(h[3])
    return int(h[2]), clauses

def trim_lrat(data: bytes, initial):
    records, last_empty, seen = {}, None, set(range(1, len(initial) + 1))
    for line in data.decode().splitlines():
        a = line.split()
        if not a: continue
        ident = int(a[0])
        if a[1] == 'd': continue
        xs = list(map(int, a[1:])); stop = xs.index(0)
        clause, hints = tuple(xs[:stop]), xs[stop+1:]
        assert hints and hints[-1] == 0
        hints = tuple(hints[:-1])
        assert ident not in seen and all(h > 0 and h in seen for h in hints), (ident, hints)
        records[ident] = (clause, hints); seen.add(ident)
        if not clause: last_empty = ident
    assert last_empty is not None, 'No empty clause'
    needed, todo = set(), [last_empty]
    while todo:
        ident = todo.pop()
        if ident in needed: continue
        needed.add(ident)
        if ident > len(initial): todo.extend(records[ident][1])
    originals = sorted(i for i in needed if i <= len(initial))
    derivations = [i for i in records if i in needed]
    mapping = {old: new for new, old in enumerate(originals + derivations, 1)}
    clauses = [initial[i-1] for i in originals]
    steps = [(mapping[i], records[i][0], tuple(mapping[j] for j in records[i][1])) for i in derivations]
    replay(clauses, steps)
    return originals, clauses, steps

def replay(clauses, steps):
    db = {i: c for i, c in enumerate(clauses, 1)}
    for ident, clause, hints in steps:
        assert ident not in db
        assignment = {}
        contradiction = False
        for lit in clause:
            var, val = abs(lit), lit < 0
            if var in assignment and assignment[var] != val: contradiction = True
            assignment[var] = val
        for h in hints:
            assert h in db
            if contradiction: break
            c = db[h]
            if any(abs(l) in assignment and assignment[abs(l)] == (l > 0) for l in c):
                raise AssertionError(('Satisfied RUP hint', ident, h))
            free = [l for l in c if abs(l) not in assignment]
            assert len(free) <= 1, ('Non-unit RUP hint', ident, h, free)
            if not free: contradiction = True
            else: assignment[abs(free[0])] = free[0] > 0
        assert contradiction, ('RUP did not derive a contradiction', ident)
        db[ident] = clause
    assert steps and not steps[-1][1]

def decode_graph6(text):
    n = ord(text[0]) - 63
    bits = [((ord(c)-63) >> b) & 1 for c in text[1:] for b in range(5, -1, -1)]
    edges = [[False]*n for _ in range(n)]
    for k, (j, i) in enumerate((j, i) for j in range(1, n) for i in range(j)):
        edges[i][j] = edges[j][i] = bool(bits[k])
    return edges

def symbolic(core):
    # ('c', bool) or ('v', DIMACS one-based variable)
    s = [[('c', False) for _ in range(20)] for _ in range(20)]
    for u in range(20):
        for w in range(u+1, 20):
            if w < 4: a = ('c', True)
            elif u >= 4: a = ('c', core[u-4][w-4])
            else: a = ('v', 1+16*u+(w-4))
            s[u][w] = s[w][u] = a
    return s

def condition(s, vertices, color):
    req = {}
    for u, w in itertools.combinations(vertices, 2):
        kind, a = s[u][w]
        if kind == 'c':
            if a != color: return None
        else:
            if a in req: assert req[a] == color
            req[a] = color
    return req

def find_witnesses(s, clauses):
    needed = set(map(frozenset, clauses))
    conditions = []
    for vs in itertools.combinations(range(20), 4):
        for color in (False, True):
            req = condition(s, vs, color)
            if req is not None: conditions.append((sum(1 << v for v in vs), vs, color, req))
    witnesses = {}
    for a, b in itertools.combinations(conditions, 2):
        if a[0] & b[0]: continue
        req = a[3] | b[3]
        assert all(v not in a[3] or a[3][v] == c for v,c in b[3].items())
        clause = frozenset(-v if c else v for v,c in req.items())
        if clause in needed:
            witnesses[clause] = (a[1], b[1], a[2], b[2])
    assert needed <= witnesses.keys(), ('Missing witnesses', len(needed - witnesses.keys()))
    result = [witnesses[frozenset(c)] for c in clauses]
    for c, (a,b,ca,cb) in zip(clauses, result):
        assert len(set(a)) == len(set(b)) == 4 and not set(a) & set(b)
        falsified = {abs(l): l < 0 for l in c}
        for vs,color in ((a,ca),(b,cb)):
            for u,w in itertools.permutations(vs, 2):
                kind, x = s[u][w]
                assert (x if kind == 'c' else falsified[x]) == color
    return result

def lean_list(xs): return '[' + ', '.join(xs) + ']'
def vec(xs): return '![' + ', '.join(map(str, xs)) + ']'
def atom(a): return f'.fixed {str(a[1]).lower()}' if a[0] == 'c' else f'.variable {a[1]-1}'
def literal(l): return f'.{"pos" if l > 0 else "neg"} {abs(l)-1}'
def rule(c, w):
    a,b,ca,cb = w
    return '⟨' + ', '.join([lean_list([literal(l) for l in c]), vec(a), vec(b), str(ca).lower(), str(cb).lower()]) + '⟩'

def generate(project: Path, logs: Path):
    raw = logs / 'original-core-certificates'; raw.mkdir(parents=True, exist_ok=True)
    summaries = []
    for core in range(2):
        cnf = get(f'z20_core{core}.cnf', raw)
        assert hashlib.sha256(cnf).hexdigest() == EXPECTED[core]
        lrat = get(f'core{core}.lrat', raw)
        nvars, initial = read_cnf(cnf)
        ids, clauses, steps = trim_lrat(lrat, initial)
        s = symbolic(decode_graph6(GRAPHS[core]))
        witnesses = find_witnesses(s, clauses)
        directory = project / 'JSP000622' / f'Core{core}'
        directory.mkdir(parents=True, exist_ok=True)
        (directory/'core.cnf').write_text(f'p cnf {nvars} {len(clauses)}\n' + ''.join(' '.join(map(str,c))+' 0\n' for c in clauses))
        (directory/'core.lrat').write_text(''.join(f'{i} '+ ' '.join(map(str,c))+' 0 '+' '.join(map(str,h))+' 0\n' for i,c,h in steps))
        ns = f'JSP000622.Core{core}'
        head = f'namespace {ns}\nopen JSP000622.Certificate\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
        (directory/'Symbols.lean').write_text('import JSP000622.CertificateKernel\n' + head + 'def symbols : Symbols 20 :=\n  '+vec([vec([atom(a) for a in row]) for row in s])+f'\nend {ns}\n')
        chunks = []
        for start in range(0, len(clauses), 32):
            name = f'Chunk{len(chunks):04}'
            rname = f'rules{len(chunks):04}'
            content = f'import JSP000622.Core{core}.Symbols\n'+head
            content += f'def {rname} : List (PairRule 20) :=\n  [\n    '
            content += ',\n    '.join(rule(c,w) for c,w in zip(clauses[start:start+32], witnesses[start:start+32]))+'\n  ]\n'
            content += f'theorem {rname}_valid : ∀ r ∈ {rname}, r.Valid symbols := by decide\nend {ns}\n'
            (directory/f'{name}.lean').write_text(content)
            chunks.append((name,rname))
        imports = ''.join(f'import JSP000622.Core{core}.{name}\n' for name,_ in chunks)
        content = imports+head
        content += 'def rules : List (PairRule 20) := '+ ' ++ '.join(r for _,r in chunks)+'\n'
        content += 'theorem valid : ∀ r ∈ rules, r.Valid symbols := by\n'
        content += '  intro r hr\n  simp only [rules, List.mem_append] at hr\n'
        content += '  rcases hr with '+' | '.join('h' for _ in chunks)+'\n'
        for _,r in chunks: content += f'  · exact {r}_valid r h\n'
        content += 'theorem unsat : (rules.map PairRule.clause).proof [] :=\n'
        content += f'  checked_from_lrat (include_str "Core{core}/core.cnf") (include_str "Core{core}/core.lrat")\n'
        content += 'theorem packing (G : SimpleGraph (Fin 20)) (v : Sat.Valuation)\n'
        content += '    (h : Realizes G symbols v) : TwoFours G :=\n'
        content += '  twoFours_of_refutation symbols rules valid unsat G v h\n'
        content += f'#print axioms packing\nend {ns}\n'
        (project/'JSP000622'/f'Core{core}.lean').write_text(content)
        summary = {'core':core, 'original_clauses':len(initial), 'retained_input_clauses':len(clauses), 'retained_RUP_steps':len(steps), 'semantic_pair_witnesses':len(witnesses), 'RUP_replay':'PASSED', 'witness_replay':'PASSED', 'lean_status':'NOT_YET_RUN', 'source_commit':PIN, 'original_cnf_sha256':EXPECTED[core], 'original_lrat_sha256':hashlib.sha256(lrat).hexdigest(), 'retained_original_clause_ids':ids}
        summaries.append(summary)
        print(json.dumps({k:v for k,v in summary.items() if k != 'retained_original_clause_ids'}), flush=True)
    (logs/'core-generation.json').write_text(json.dumps(summaries,indent=2))

if __name__ == '__main__':
    if len(sys.argv) != 3: raise SystemExit('usage: generate_core_certificates.py PROJECT LOG_DIRECTORY')
    generate(Path(sys.argv[1]), Path(sys.argv[2]))
