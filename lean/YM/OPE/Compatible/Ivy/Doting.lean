import YM.OPE.Compatible.Gum.Pour
/-!
# Profile sets and entry list. Marks on TapeI. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Char
open Function Filter MeasureTheory Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open Next.Free Bloch PertExtension Series Asymptotics GaussianScore Radial Finset Flock Coin Lattice Laurent RG Precision Flume Script Page Planned.PrimaryIntegral295.Carrier Matrix JetS ScriptJ Shell
abbrev Phase := Fin 3
private lemma spin_grade (x:Phase): x=0∨x=1∨x=2:=by fin_cases x<;>decide
-- profiles fixed η. support append. dummy at 4
abbrev Meeting:=Finset Ask
def sizes : Ask→ℕ:=![3,3,4,2,0]
def Plans (i:Phase): Finset Meeting := (![{∅},{{0}},{{2},{3},{0,1}}] : Phase → Finset Meeting) i
def meter (u:Meeting):ℝ:=if u={0,1} then 1/2 else 1
lemma rows (i:Phase)(p:Meeting)(h:p∈ Plans i): (4:Ask)∉p:=by revert i p;decide -- dec normalization
lemma role (A:Meeting→ℝ)(i:Phase): (rich A).seq i.val=∑ p∈Plans i,meter p*A p:=by
     fin_cases i
     · norm_num [rich, JetS.seq, Plans, meter,show (∅:Meeting)≠{0,1} from by decide] -- Fin n simp
     · simp [rich, JetS.seq, Plans, meter,show ({0}:Meeting)≠{0,1} from by decide]
     change _=∑ i ∈({{2},{3},{0,1}}:Finset Meeting), _; rw [sum_insert (by decide : ({2}:Meeting) ∉ ({{3},{0,1}}:Finset _)),sum_insert (by decide : ({3}:Meeting)∉ ({{0,1}}:Finset _)),sum_singleton]; norm_num [meter, JetS.seq,rich,show ({2}:Meeting)≠{0,1} from by decide,show ({3}:Meeting)≠{0,1} from by decide];ring
structure Story (I:Type) where
     u : Script I 3
     v : Script I 4
     t : Script I 2
variable {I J:Type}
-- robust dependent branching by fin_cases tactic; use everything expose. indexFin vector.
def Paloma (p:Story I): ∀ i:Ask, Script I (0+ sizes i):=by
      intro i; refine Fin.cases p.u (fun i=> ?_) (motive:=fun i=> Script I (0+ sizes i)) i; refine Fin.cases p.u (fun i=> ?_) (motive:=fun i=>Script I (0+sizes i.succ)) i; refine Fin.cases p.v (fun i=> ?_) (motive:=fun i=>Script I (0+sizes i.succ.succ)) i; refine Fin.cases p.t (fun i=>?_) (motive:=fun i=>Script I (0+sizes i.succ.succ.succ)) i; exact 0
abbrev Canvas (p:Story I) (C:Row I I) (s:Meeting) (d:ℕ)(X: Script I d): Curtain I:= Shell.Hall C sizes (fun _=>0) (Paloma p) (fun _=>true) s d 0 (Shell.slice (finCongr (Nat.zero_add d).symm) X)
lemma tallyT {d e:ℕ}(i: Phase)(s:Meeting)(h:s∈ Plans i)(he:d+i.val<e)(C:Row I I)(p:Story I)(X:Script I d): Canvas p C s d X e=0:=by
       apply rim_height
       unfold Rollup; simp only [add_zero]; have h: Mani sizes s ≤ i.val+2*s.card:= tax i s h; unfold Mani at h; omega
where tax (i:Phase)(s:Meeting)(h:s∈Plans i): Mani sizes s ≤ i.val+2*s.card := by revert i s; decide
-- row pack
variable {k d e l m:ℕ}
def Volume (P:Curtain I)(d:ℕ)(m:ℕ)(c:ℝ):Prop:= (∀ i:ℕ,d < i → P i=0) ∧ ∀ i:ℕ,soot m (P i) c
variable (p:Curtain I){c b:ℝ}
lemma Volume.bound (hp: Volume p d m c): Bins p:=fun i=>sootS (hp.2 i)
lemma Volume.add {q:Curtain I} (h:Volume p d k c)(hp:Volume q d k b): Volume (p+q) d k (c+b) :=by
      refine ⟨fun i hi=> by rw [Pi.add_apply,h.1 i hi,hp.1 i hi,add_zero],fun i=>Sack.splits (h.2 i) (hp.2 i) (fun i=>zero_le_one.trans (payer k i))⟩
lemma Volume.raise (h:Volume p d k c)(he:d≤ e)(hp:b≥c): Volume p e k b:=⟨fun i hi=>h.1 i (lt_of_le_of_lt he hi),fun i=> Sack.tips (h.2 i) hp⟩
lemma Volume.spread (x:ℝ)(h:Volume p d k c): Volume (x • p) d k (‖x‖*c):=⟨fun i hi=> by rw [Pi.smul_apply,h.1 i hi, smul_zero],fun i=> Sack.scale_line (h.2 i) x⟩
lemma Volume.sum (f:J→Curtain I)(p:J→ℝ)(s: Finset J)(h:∀ i∈s,Volume (f i) d k (p i)): Volume (∑ i∈s,f i) d k (∑ i∈s,p i) :=by
     refine ⟨fun i hi=> ?_,fun i=>?_⟩
     · rw [Finset.sum_apply]; exact Finset.sum_eq_zero fun j hj=> (h j hj).1 i hi
     rw [Finset.sum_apply]; exact Sack.finGather _ _ _ (fun j hj=> (h _ hj).2 i) (fun i=> zero_le_one.trans (payer k i))
-- generic reading horizon
variable [Fintype I]{n:Side} {x:Site n}
omit [Fintype I] in
lemma Volume.wax (h: Volume p d k c)(j:ℕ)(hx:d≤j)(a:deck I n): Flair p d a x=Flair p j a x:=by
    apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hx _)); intro z _ h'; rw [mem_range,not_lt] at h'; apply Eq.trans (congr_arg (fun t:Script I z=> Flume.Script.value x t a) (h.1 z h')); simp [Flume.Script.value,scribe]
end YM.OPE.Libra.Char
