#!/usr/bin/env python3
"""Untrusted generator of finite equality and isomorphism witnesses.
All emitted equalities, injectivity facts and adjacency correspondences use
ordinary Lean `decide`, not native_decide or an imported external assertion.
"""
from __future__ import annotations
import json
import sys
from pathlib import Path
import networkx as nx
from generate_classification import dense_code, graph
from generate_core_certificates import decode_graph6, GRAPHS, vec, lean_list


def generate(project: Path, report_file: Path):
    report=json.loads(report_file.read_text())
    seven=report['seven_codes']; eight=report['eight_codes']; cores=report['core_codes']
    assert len(seven)==9 and len(eight)==3 and len(cores)==2
    matrices=[decode_graph6(s) for s in GRAPHS]
    assert cores==[dense_code(a) for a in matrices]
    directory=project/'JSP000622'; directory.mkdir(parents=True,exist_ok=True)
    text='import JSP000622.ClassificationKernel\nimport Mathlib.Data.Fin.VecNotation\n\n'
    text+='namespace JSP000622.FiniteData\nopen JSP000622.Certificate\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
    for i,c in enumerate(cores): text+=f'def code{i} : ℕ := {c}\n'
    text+='def cores : List ℕ := [code0, code1]\n'
    text+='def small7 : List ℕ := '+lean_list(list(map(str,seven)))+'\n'
    text+='def small8 : List ℕ := '+lean_list(list(map(str,eight)))+'\n'
    targets=[]; witnesses=[]
    for i,a in enumerate(matrices):
        comp=nx.complement(graph(a)); chosen=None
        for j,b in enumerate(matrices):
            gm=nx.algorithms.isomorphism.GraphMatcher(comp,graph(b))
            if gm.is_isomorphic():
                chosen=(j,[gm.mapping[u] for u in range(16)]); break
        assert chosen is not None
        j,p=chosen; targets.append(j); witnesses.append({'core':i,'complement_target':j,'permutation':p})
        assert sorted(p)==list(range(16))
        assert all((u!=v and not a[u][v])==matrices[j][p[u]][p[v]] for u in range(16) for v in range(16))
        text+=f'noncomputable def complementIso{i} : (codeGraph 16 code{i})ᶜ ≃g codeGraph 16 code{j} := by\n'
        text+=f'  let p : Fin 16 → Fin 16 := {vec(p)}\n'
        text+='  have hp : Function.Injective p := by decide\n'
        text+='  let e : Equiv.Perm (Fin 16) := Equiv.ofBijective p ⟨hp, Finite.surjective_of_injective hp⟩\n'
        text+='  refine { toEquiv := e, map_rel_iff\' := ?_ }\n'
        text+='  intro a b\n'
        prop=f'(codeGraph 16 code{j}).Adj (p a) (p b) ↔ (codeGraph 16 code{i})ᶜ.Adj a b'
        text+=f'  change {prop}\n'
        text+=f'  exact (show ∀ a b : Fin 16, {prop} from by decide) a b\n'
    text+='theorem complement_closed (c : ℕ) (hc : c ∈ cores) : Classified (codeGraph 16 c)ᶜ cores := by\n'
    text+='  simp only [cores, List.mem_cons, List.mem_singleton] at hc\n  rcases hc with rfl | rfl\n'
    for i,j in enumerate(targets):
        text+=f'  · exact ⟨code{j}, by simp [cores], ⟨complementIso{i}⟩⟩\n'
    text+='#print axioms complement_closed\nend JSP000622.FiniteData\n'
    (directory/'FiniteData.lean').write_text(text)
    (report_file.parent/'complement-witnesses.json').write_text(json.dumps(witnesses,indent=2))

    text='import JSP000622.Templates\nimport JSP000622.FiniteData\n'
    for i in range(9):
        for j in range(3): text+=f'import JSP000622.Class16.Case{i}{j}\n'
    text+='\nnamespace JSP000622.FiniteBridges\nopen JSP000622.Certificate\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
    for i,a in enumerate(seven):
        for j,b in enumerate(eight):
            text+=f'theorem symbols_{i}{j} : Class16.Case{i}{j}.symbols = template16 {a} {b} := by\n'
            text+='  funext u v\n'
            text+=f'  exact (show ∀ u v : Fin 16, Class16.Case{i}{j}.symbols u v = template16 {a} {b} u v from by decide) u v\n'
    text+='theorem classify_normalized (a : ℕ) (ha : a ∈ FiniteData.small7)\n'
    text+='    (b : ℕ) (hb : b ∈ FiniteData.small8) (G : SimpleGraph (Fin 16))\n'
    text+='    (v : Sat.Valuation) (h : Realizes G (template16 a b) v)\n'
    text+='    (free : G.CliqueFree 4 ∧ G.IndepSetFree 4) : Classified G FiniteData.cores := by\n'
    text+='  simp only [FiniteData.small7, List.mem_cons, List.mem_singleton] at ha\n'
    text+='  simp only [FiniteData.small8, List.mem_cons, List.mem_singleton] at hb\n'
    text+='  rcases ha with '+' | '.join('rfl' for _ in seven)+'\n'
    for i in range(9):
        text+='  · rcases hb with rfl | rfl | rfl\n'
        for j in range(3):
            text+=f'    · exact Class16.Case{i}{j}.classify G v (by simpa only [symbols_{i}{j}] using h) free\n'
    text+='#print axioms classify_normalized\nend JSP000622.FiniteBridges\n'
    (directory/'Class16Templates.lean').write_text(text)

    text='import JSP000622.Templates\nimport JSP000622.FiniteData\nimport JSP000622.Core0\nimport JSP000622.Core1\n'
    text+='\nnamespace JSP000622.FiniteBridges\nopen JSP000622.Certificate\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
    for i in range(2):
        text+=f'theorem core_symbols_{i} : Core{i}.symbols = template20 FiniteData.code{i} := by\n'
        text+='  funext u v\n'
        text+=f'  exact (show ∀ u v : Fin 20, Core{i}.symbols u v = template20 FiniteData.code{i} u v from by decide) u v\n'
    text+='theorem packing_normalized (code : ℕ) (hc : code ∈ FiniteData.cores)\n'
    text+='    (G : SimpleGraph (Fin 20)) (v : Sat.Valuation)\n'
    text+='    (h : Realizes G (template20 code) v) : TwoFours G := by\n'
    text+='  simp only [FiniteData.cores, List.mem_cons, List.mem_singleton] at hc\n'
    text+='  rcases hc with rfl | rfl\n'
    for i in range(2):
        text+=f'  · exact Core{i}.packing G v (by simpa only [core_symbols_{i}] using h)\n'
    text+='#print axioms packing_normalized\nend JSP000622.FiniteBridges\n'
    (directory/'CoreTemplates.lean').write_text(text)
    print(json.dumps({'finite_template_identities':29,'complement_isomorphisms':witnesses,'lean_status':'NOT_YET_RUN'}),flush=True)

if __name__=='__main__':
    if len(sys.argv)!=3: raise SystemExit('usage: generate_bridges.py PROJECT CLASSIFICATION_REPORT')
    generate(Path(sys.argv[1]),Path(sys.argv[2]))
