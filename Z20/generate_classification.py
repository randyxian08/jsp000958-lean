#!/usr/bin/env python3
"""Untrusted finite Ramsey classification generator; all outputs require Lean replay.

The graph atlas and SAT enumeration are used only to find representatives and
witnesses. Coverage is established separately by a checked UNSAT proof after
blocking all found models. Every blocking clause carries an explicit isomorphism.
"""
from __future__ import annotations
import itertools
import json
import subprocess
import sys
from pathlib import Path
import networkx as nx
from pysat.solvers import Solver
from generate_core_certificates import trim_lrat, replay, decode_graph6, GRAPHS, atom, vec, literal, lean_list


def matrix(g, n):
    return [[u != v and g.has_edge(u,v) for v in range(n)] for u in range(n)]

def dense_code(a):
    n=len(a)
    return sum(1 << (u*n+v) for u in range(n) for v in range(u+1,n) if a[u][v])

def graph(a):
    n=len(a); g=nx.Graph(); g.add_nodes_from(range(n))
    g.add_edges_from((u,v) for u in range(n) for v in range(u+1,n) if a[u][v]); return g

def r34(a):
    n=len(a)
    return not any(all(a[u][v] for u,v in itertools.combinations(vs,2)) for vs in itertools.combinations(range(n),3)) and not any(all(not a[u][v] for u,v in itertools.combinations(vs,2)) for vs in itertools.combinations(range(n),4))

def catalogs():
    seven=[matrix(g,7) for g in nx.graph_atlas_g() if len(g)==7 and r34(matrix(g,7))]
    seven.sort(key=dense_code)
    assert len(seven)==9, ('seven candidates',len(seven))
    eight=[]
    for a in seven:
        for mask in range(128):
            b=[row+[bool(mask>>u&1)] for u,row in enumerate(a)]
            b.append([bool(mask>>u&1) for u in range(7)]+[False])
            if r34(b) and not any(nx.is_isomorphic(graph(b),graph(c)) for c in eight): eight.append(b)
    eight.sort(key=dense_code)
    assert len(eight)==3, ('eight candidates',len(eight))
    return seven,eight

def universal_symbols(n):
    s=[[('c',False) for _ in range(n)] for _ in range(n)]; pairs=[]
    for u in range(n):
        for v in range(u+1,n):
            pairs.append((u,v)); s[u][v]=s[v][u]=('v',len(pairs))
    return s,pairs

def class16_symbols(a,b):
    s=[[('c',False) for _ in range(16)] for _ in range(16)]; pairs=[]
    for u in range(16):
        for v in range(u+1,16):
            if u==0: x=('c',v<8)
            elif v<8: x=('c',a[u-1][v-1])
            elif u>=8: x=('c',not b[u-8][v-8])
            else: pairs.append((u,v)); x=('v',len(pairs))
            s[u][v]=s[v][u]=x
    assert len(pairs)==56
    return s,pairs

def forbidden_rules(s,k,l):
    rules={}; n=len(s)
    for color,size in ((True,k),(False,l)):
        for vs in itertools.combinations(range(n),size):
            clause=[]; possible=True
            for u,v in itertools.combinations(vs,2):
                tag,x=s[u][v]
                if tag=='c':
                    if x!=color: possible=False; break
                else: clause.append(-x if color else x)
            if possible:
                c=tuple(sorted(clause,key=lambda x:(abs(x),x)))
                rules.setdefault(c,('forbidden',vs,color))
    return rules

def all_relabelings(a):
    n=len(a); pairs=list(itertools.combinations(range(n),2)); models={}
    for p in itertools.permutations(range(n)):
        mask=sum(1<<i for i,(u,v) in enumerate(pairs) if a[p[u]][p[v]])
        models.setdefault(mask, p)
    return models

def isomorphism(a, targets):
    g=graph(a)
    for b in targets:
        gm=nx.algorithms.isomorphism.GraphMatcher(g,graph(b))
        if gm.is_isomorphic():
            p=[gm.mapping[u] for u in range(len(a))]
            assert len(set(p))==len(a)
            assert all(a[u][v]==b[p[u]][p[v]] for u in range(len(a)) for v in range(len(a)))
            return dense_code(b),p
    raise AssertionError('A model is not isomorphic to any proposed target')

def solve_and_prove(name, nvars, rules, folder, converter):
    folder.mkdir(parents=True,exist_ok=True)
    clauses=list(rules)
    cnf=folder/'full.cnf'; drup=folder/'full.drup'; lrat=folder/'full.lrat'
    cnf.write_text(f'p cnf {nvars} {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses))
    with Solver(name='g3',bootstrap_with=clauses,with_proof=True) as solver:
        assert solver.solve() is False, ('Uncovered model',name,solver.get_model())
        proof=solver.get_proof()
    drup.write_text('\n'.join(proof)+'\n')
    subprocess.run([str(converter),str(cnf),str(drup),str(lrat)],check=True,timeout=600)
    ids, reduced, steps=trim_lrat(lrat.read_bytes(),clauses)
    reduced_rules=[rules[clauses[i-1]] for i in ids]
    (folder/'certificate.cnf').write_text(f'p cnf {nvars} {len(reduced)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in reduced))
    (folder/'certificate.lrat').write_text(''.join(f'{i} '+' '.join(map(str,c))+' 0 '+' '.join(map(str,h))+' 0\n' for i,c,h in steps))
    print(json.dumps({'name':name,'full_inputs':len(clauses),'retained_inputs':len(reduced),'RUP_steps':len(steps),'RUP_replay':'PASSED'}),flush=True)
    return reduced,reduced_rules,steps

def witness_lean(w):
    if w[0]=='forbidden': return f'.forbidden {len(w[1])} {vec(w[1])} {str(w[2]).lower()}'
    return f'.isomorphic {w[1]} {vec(w[2])}'

def check_witness(s,c,w,k,l,targets):
    assignment={abs(x):x<0 for x in c}
    def edge(u,v):
        tag,a=s[u][v]
        if tag=='c': return a
        assert a in assignment
        return assignment[a]
    if w[0]=='forbidden':
        vs,color=w[1:]
        assert len(set(vs))==len(vs)==(k if color else l)
        assert all(edge(u,v)==color for u,v in itertools.permutations(vs,2))
    else:
        code,p=w[1:]; n=len(s)
        assert code in targets and sorted(p)==list(range(n))
        assert all(edge(u,v)==bool(code>>(min(p[u],p[v])*n+max(p[u],p[v]))&1) for u,v in itertools.permutations(range(n),2))

def emit(project,name,s,k,l,targets,clauses,witnesses,folder,pairs,universal=False):
    n=len(s); ns='JSP000622.'+name
    path=project/'JSP000622'/Path(name.replace('.','/')); path.mkdir(parents=True,exist_ok=True)
    for f in ('certificate.cnf','certificate.lrat'): (path/f).write_bytes((folder/f).read_bytes())
    head=f'namespace {ns}\nopen JSP000622.Certificate\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
    text='import JSP000622.ClassificationKernel\n'+head
    text+=f'def symbols : Symbols {n} :=\n  '+vec([vec([atom(a) for a in row]) for row in s])+'\n'
    text+='def targets : List ℕ := '+lean_list(list(map(str,targets)))+'\n'
    text+=f'end {ns}\n'; (path/'Data.lean').write_text(text)
    chunks=[]
    for start in range(0,len(clauses),32):
        number=len(chunks); mod=f'Chunk{number:04}'; rn=f'rules{number:04}'
        text=f'import JSP000622.{name}.Data\n'+head
        text+=f'def {rn} : List (ClassRule {n}) := [\n'
        text+=',\n'.join('  ⟨'+lean_list([literal(x) for x in c])+', '+witness_lean(w)+'⟩' for c,w in zip(clauses[start:start+32],witnesses[start:start+32]))+'\n]\n'
        text+=f'theorem {rn}_valid : ∀ r ∈ {rn}, r.Valid symbols {k} {l} targets := by decide\nend {ns}\n'
        (path/f'{mod}.lean').write_text(text); chunks.append((mod,rn))
    text=''.join(f'import JSP000622.{name}.{m}\n' for m,_ in chunks)+head
    text+=f'def rules : List (ClassRule {n}) := '+' ++ '.join(r for _,r in chunks)+'\n'
    text+=f'theorem valid : ∀ r ∈ rules, r.Valid symbols {k} {l} targets := by\n'
    text+='  intro r hr\n  simp only [rules, List.mem_append] at hr\n'
    if len(chunks)>1:
        text+='  rcases hr with '+' | '.join('h' for _ in chunks)+'\n'
        text+=''.join(f'  · exact {r}_valid r h\n' for _,r in chunks)
    else: text+=f'  exact {chunks[0][1]}_valid r hr\n'
    rel=path.name
    text+='theorem unsat : Sat.Fmla.proof (rules.map ClassRule.clause) [] :=\n'
    text+=f'  checked_from_lrat (include_str "{rel}/certificate.cnf") (include_str "{rel}/certificate.lrat")\n'
    text+=f'theorem classify (G : SimpleGraph (Fin {n})) (v : Sat.Valuation)\n'
    text+=f'    (h : Realizes G symbols v) (free : G.CliqueFree {k} ∧ G.IndepSetFree {l}) : Classified G targets :=\n'
    text+=f'  classified_of_refutation symbols {k} {l} targets rules valid unsat G v h free\n'
    if universal:
        text+=f'def valuation (G : SimpleGraph (Fin {n})) : Sat.Valuation\n'
        text+=''.join(f'  | {i} => G.Adj {u} {v}\n' for i,(u,v) in enumerate(pairs))+'  | _ => False\n'
        text+=f'theorem realizes (G : SimpleGraph (Fin {n})) : Realizes G symbols (valuation G) := by\n'
        text+='  intro a b h\n  fin_cases a <;> fin_cases b <;> simp_all [symbols, valuation, Atom.eval, SimpleGraph.adj_comm]\n'
        text+=f'theorem complete (G : SimpleGraph (Fin {n})) (free : G.CliqueFree {k} ∧ G.IndepSetFree {l}) : Classified G targets :=\n'
        text+='  classify G (valuation G) (realizes G) free\n#print axioms complete\n'
    text+=f'#print axioms classify\nend {ns}\n'
    path.with_suffix('.lean').write_text(text)

def main(project,logs,converter):
    seven,eight=catalogs(); cores=[decode_graph6(x) for x in GRAPHS]
    report={'seven_codes':[dense_code(a) for a in seven],'eight_codes':[dense_code(a) for a in eight],'core_codes':[dense_code(a) for a in cores],'cases':[],'lean_status':'NOT_YET_RUN'}
    root=logs/'classification'; root.mkdir(parents=True,exist_ok=True)
    for n,cat,name in ((7,seven,'R34Seven'),(8,eight,'R34Eight')):
        s,pairs=universal_symbols(n); rules=forbidden_rules(s,3,4)
        models=0
        for a in cat:
            for mask,p in all_relabelings(a).items():
                c=tuple(-i-1 if mask>>i&1 else i+1 for i in range(len(pairs)))
                assert c not in rules
                rules[c]=('isomorphic',dense_code(a),p); models+=1
        folder=root/name
        cs,ws,steps=solve_and_prove(name,len(pairs),rules,folder,converter)
        for c,w in zip(cs,ws): check_witness(s,c,w,3,4,[dense_code(a) for a in cat])
        emit(project,name,s,3,4,[dense_code(a) for a in cat],cs,ws,folder,pairs,universal=True)
        report['cases'].append({'name':name,'models':models,'retained_inputs':len(cs),'RUP_steps':len(steps)})
        (logs/'classification-generation.json').write_text(json.dumps(report,indent=2))
    for i,a in enumerate(seven):
        for j,b in enumerate(eight):
            name=f'Class16.Case{i}{j}'; s,pairs=class16_symbols(a,b); rules=forbidden_rules(s,4,4)
            model_count=0
            with Solver(name='g3',bootstrap_with=list(rules)) as solver:
                while solver.solve():
                    model=set(solver.get_model()); bits=[v+1 in model for v in range(len(pairs))]
                    g=[[False]*16 for _ in range(16)]
                    for u in range(16):
                        for v in range(u+1,16):
                            tag,x=s[u][v]; g[u][v]=g[v][u]=bool(x) if tag=='c' else bits[x-1]
                    target,p=isomorphism(g,cores)
                    clause=tuple(-v-1 if bits[v] else v+1 for v in range(len(bits)))
                    assert clause not in rules
                    rules[clause]=('isomorphic',target,p); solver.add_clause(clause); model_count+=1
            folder=root/f'Case{i}{j}'
            cs,ws,steps=solve_and_prove(name,56,rules,folder,converter)
            for c,w in zip(cs,ws): check_witness(s,c,w,4,4,report['core_codes'])
            emit(project,name,s,4,4,report['core_codes'],cs,ws,folder,pairs)
            report['cases'].append({'name':name,'models':model_count,'retained_inputs':len(cs),'RUP_steps':len(steps)})
            (logs/'classification-generation.json').write_text(json.dumps(report,indent=2))
    print(json.dumps({'classification_complete_computation':True,'sixteen_models':sum(x['models'] for x in report['cases'] if x['name'].startswith('Class16')),'lean_status':'NOT_YET_RUN'}),flush=True)

if __name__=='__main__':
    if len(sys.argv)!=4: raise SystemExit('usage: generate_classification.py PROJECT LOGS RUP_CONVERTER')
    main(Path(sys.argv[1]),Path(sys.argv[2]),Path(sys.argv[3]).resolve())
