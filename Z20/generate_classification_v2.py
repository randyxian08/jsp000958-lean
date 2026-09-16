#!/usr/bin/env python3
"""Certificate generation only; mathematical soundness lives in the Lean kernels.

Version 2 proves small-catalog coverage by induction over all one-vertex
extensions. Every possible extension is either explicitly forbidden or carries
an explicit isomorphism. This avoids trusting canonical labelling and avoids
replaying every labelled seven/eight-vertex graph separately.
"""
from __future__ import annotations
import itertools
import json
import sys
from pathlib import Path
import networkx as nx
from pysat.solvers import Solver
from generate_classification import (matrix, dense_code, graph, r34, catalogs,
    class16_symbols, forbidden_rules, isomorphism, solve_and_prove,
    emit, check_witness)
from generate_core_certificates import decode_graph6, GRAPHS, lean_list


def extension_symbols(a):
    n=len(a)
    s=[[('c',False) for _ in range(n+1)] for _ in range(n+1)]
    for u in range(n):
        for v in range(n): s[u][v]=('c',a[u][v])
        s[u][n]=s[n][u]=('v',u+1)
    return s


def extension_witness(a,mask,targets):
    n=len(a)
    b=[row+[bool(mask>>u&1)] for u,row in enumerate(a)]
    b.append([bool(mask>>u&1) for u in range(n)]+[False])
    for size,color in ((3,True),(4,False)):
        for vs in itertools.combinations(range(n+1),size):
            if all(b[u][v]==color for u,v in itertools.combinations(vs,2)):
                return ('forbidden',vs,color)
    code,p=isomorphism(b,targets)
    return ('isomorphic',code,p)


def catalog_induction(project,allcats,case_names):
    directory=project/'JSP000622/R34Catalog'
    directory.mkdir(parents=True,exist_ok=True)
    ns='JSP000622.R34Catalog'
    text='import JSP000622.ExtensionKernel\nnamespace '+ns+'\n'
    for n,cat in enumerate(allcats):
        text+=f'def catalog{n} : List ℕ := '+lean_list([str(dense_code(a)) for a in cat])+'\n'
    text+='end '+ns+'\n'
    (directory/'Data.lean').write_text(text)
    text='import JSP000622.R34Catalog.Data\nnamespace '+ns+'\nopen JSP000622.Certificate\n'
    text+='theorem complete0 (G : SimpleGraph (Fin 0)) (_ : G.CliqueFree 3 ∧ G.IndepSetFree 4) : Classified G catalog0 := classified_zero G\n'
    text+='end '+ns+'\n'; (directory/'Level0.lean').write_text(text)
    for n in range(9):
        names=case_names[n]
        text=f'import JSP000622.R34Catalog.Level{n}\n'
        text+=''.join(f'import JSP000622.{name}\n' for name in names)
        text+='namespace '+ns+'\nopen JSP000622.Certificate\n'
        text+=f'theorem complete{n+1} (G : SimpleGraph (Fin {n+1}))\n'
        text+=f'    (free : G.CliqueFree 3 ∧ G.IndepSetFree 4) : Classified G catalog{n+1} := by\n'
        text+=f'  refine classified_step catalog{n} catalog{n+1} complete{n} ?_ G free\n'
        text+='  intro code hcode H v hr freeH\n'
        text+=f'  simp only [catalog{n}, List.mem_cons, List.mem_singleton] at hcode\n'
        text+='  rcases hcode with '+' | '.join('rfl' for _ in names)+'\n'
        for name in names:
            text+=f'  · exact JSP000622.{name}.classify H v\n'
            text+=f'      (by simpa only [JSP000622.{name}.symbols_eq_extension] using hr) freeH\n'
        text+=f'#print axioms complete{n+1}\nend '+ns+'\n'
        (directory/f'Level{n+1}.lean').write_text(text)
    for n,label in ((7,'Seven'),(8,'Eight'),(9,'Nine')):
        text=f'import JSP000622.R34Catalog.Level{n}\nnamespace JSP000622.R34{label}\nopen JSP000622.Certificate\n'
        text+=f'abbrev targets : List ℕ := R34Catalog.catalog{n}\n'
        text+=f'theorem complete (G : SimpleGraph (Fin {n})) (free : G.CliqueFree 3 ∧ G.IndepSetFree 4) : Classified G targets :=\n'
        text+=f'  R34Catalog.complete{n} G free\n#print axioms complete\nend JSP000622.R34{label}\n'
        (project/'JSP000622'/f'R34{label}.lean').write_text(text)


def main(project,logs,converter):
    seven,eight=catalogs()
    atlas=nx.graph_atlas_g()
    allcats=[]
    for n in range(8):
        cat=[matrix(g,n) for g in atlas if len(g)==n and r34(matrix(g,n))]
        cat.sort(key=dense_code); allcats.append(cat)
    assert [len(c) for c in allcats]==[1,1,2,3,6,9,15,9]
    assert list(map(dense_code,allcats[7]))==list(map(dense_code,seven))
    allcats.extend([eight,[]])
    cores=[decode_graph6(x) for x in GRAPHS]
    report={'version':2,'catalog_sizes':[len(c) for c in allcats],
        'seven_codes':[dense_code(a) for a in seven],
        'eight_codes':[dense_code(a) for a in eight],
        'core_codes':[dense_code(a) for a in cores],
        'cases':[],'lean_status':'NOT_YET_RUN'}
    root=logs/'classification'; root.mkdir(parents=True,exist_ok=True)
    names_by_level=[]
    for n in range(9):
        names=[]
        for i,a in enumerate(allcats[n]):
            name=f'R34Steps.Level{n}Case{i}'
            names.append(name)
            s=extension_symbols(a)
            targets=allcats[n+1]; codes=[dense_code(b) for b in targets]
            rules={}
            for mask in range(1<<n):
                c=tuple(-u-1 if mask>>u&1 else u+1 for u in range(n))
                rules[c]=extension_witness(a,mask,targets)
            folder=root/f'Level{n}Case{i}'
            cs,ws,steps=solve_and_prove(name,n,rules,folder,converter)
            assert len(cs)==1<<n, 'Every complete-assignment clause is necessary'
            for c,w in zip(cs,ws): check_witness(s,c,w,3,4,codes)
            emit(project,name,s,3,4,codes,cs,ws,folder,[])
            data=project/'JSP000622/R34Steps'/f'Level{n}Case{i}'/'Data.lean'
            text=data.read_text().replace('import JSP000622.ClassificationKernel','import JSP000622.ExtensionKernel')
            marker=f'end JSP000622.{name}\n'
            lemma=f'theorem symbols_eq_extension : symbols = extensionSymbols {n} {dense_code(a)} := by\n'
            lemma+=f'  funext a b\n  exact (show ∀ a b : Fin {n+1}, symbols a b = extensionSymbols {n} {dense_code(a)} a b from by decide) a b\n'
            text=text.replace(marker,lemma+marker); data.write_text(text)
            report['cases'].append({'name':name,'kind':'vertex_extension','assignments':1<<n,'retained_inputs':len(cs),'RUP_steps':len(steps)})
        names_by_level.append(names)
    assert sum(x['assignments'] for x in report['cases'])==3299
    catalog_induction(project,allcats,names_by_level)
    for i,a in enumerate(seven):
        for j,b in enumerate(eight):
            name=f'Class16.Case{i}{j}'
            s,pairs=class16_symbols(a,b); rules=forbidden_rules(s,4,4)
            model_count=0
            with Solver(name='g3',bootstrap_with=list(rules)) as solver:
                while solver.solve():
                    model=set(solver.get_model())
                    bits=[v+1 in model for v in range(len(pairs))]
                    g=[[False]*16 for _ in range(16)]
                    for u in range(16):
                        for v in range(u+1,16):
                            tag,x=s[u][v]
                            g[u][v]=g[v][u]=bool(x) if tag=='c' else bits[x-1]
                    target,p=isomorphism(g,cores)
                    clause=tuple(-v-1 if bits[v] else v+1 for v in range(len(bits)))
                    assert clause not in rules
                    rules[clause]=('isomorphic',target,p)
                    solver.add_clause(clause); model_count+=1
            folder=root/f'Case{i}{j}'
            cs,ws,steps=solve_and_prove(name,56,rules,folder,converter)
            for c,w in zip(cs,ws): check_witness(s,c,w,4,4,report['core_codes'])
            emit(project,name,s,4,4,report['core_codes'],cs,ws,folder,pairs)
            report['cases'].append({'name':name,'kind':'sixteen_vertex','models':model_count,'retained_inputs':len(cs),'RUP_steps':len(steps)})
    assert len(report['cases'])==76
    (logs/'classification-generation.json').write_text(json.dumps(report,indent=2))
    print(json.dumps({'version':2,'catalog_extensions':3299,
        'sixteen_models':sum(x.get('models',0) for x in report['cases']),
        'finite_certificate_modules':len(report['cases']),
        'RUP_and_semantic_replay':'PASSED','lean_status':'NOT_YET_RUN'}),flush=True)

if __name__=='__main__':
    if len(sys.argv)!=4: raise SystemExit('usage: generate_classification_v2.py PROJECT LOGS RUP_CONVERTER')
    main(Path(sys.argv[1]),Path(sys.argv[2]),Path(sys.argv[3]).resolve())
