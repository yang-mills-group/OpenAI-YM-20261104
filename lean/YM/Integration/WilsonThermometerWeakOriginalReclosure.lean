import YM.Integration.WilsonThermometerWeakOriginalShelves
import YM.MergeProof.West.Knight

/-! Simultaneous weak-course reclosure of the received physical table, retaining its
signed inherited marked rows, the old forced polynomial and the full true vacuum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakOriginalReclosure
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open Next.Rank Next.Rank.Edition Next.Rank.Spindle Configuration Rise
open Thirst Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm Cells Atlas Baler EntryWord Exponential
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {G:Gauge} {n:Side} {V ι κ κ':Type} [Fintype V] [DecidableEq V] [Fintype ι] [Fintype κ] [Fintype κ']
variable {d:V→ℕ} {F:(x:V)→Frame G (d x)} {η:Hol G} {P Q:Rep G n} {ζ:V→Site n}
variable (T:(x:V)→SectionData (F x)) (X:(x:V) → Coefficient (F x) n) (form:∀ x,(X x).Format 0 η P)
variable (s:V→Signed) (r:V→Prop) (vac:Neat n → Burst G n P.p.threshold)
variable (L:κ→Lifted G ζ P.p.threshold) (A:ι→SourceAt G ζ)
variable (file error:V→SourceAt G ζ) (forced:V→Strike G ζ Q.p.threshold) (far:V→Keepat n → SourceAt G ζ)

def carry:=Sum.elim A (fun t:V×Keepat n=>far t.1 t.2)
def entries:=Sum.elim (Sum.elim error (carry A far)) file
def strikes (lower:Q.p.threshold≤P.p.threshold):=
  Sum.elim forced (fun t=>dash P.p Q.p (carry A far t) lower)
def elders:=Sum.elim (elderX ζ X form s r vac (fun _=>1)) L

theorem original (lower:Q.p.threshold≤P.p.threshold)
    (sig:Siren G n Q.p.threshold) (W:κ'→Wickless G n Q.p.threshold)
    (vacuum:∀ U,Real.exp (P.exponent U)=Real.exp (Q.exponent U)*
      (∏ j,((W j).value U+1))*∏ j∈flags Q.p.threshold U,sig.value j U)
    (fired:∀ x,(forced x).fires=slot x)
    (emit:∀ x U,Poly.send (slot x) (dot (r x) ((X x).exponentialEntry 0 (T x) P (pull (s x) (ζ x) U)))=
      (file x).amount Q.p.threshold U+(error x).amount Q.p.threshold U+(forced x).occ U+
       ∑ z,(far x z).amount P.p.threshold U):
    credsX ζ T X form s r vac (fun _=>1) L A=
    dust Q (entries A file error far)
      (teat (elders X form s r vac L) (Sum.elim (fun i=>(W i).credit ζ) (strikes A forced far lower)) sig) := by
  let C:=carry A far
  let H:=entries A file error far
  let S:=strikes A forced far lower
  let B:=elders X form s r vac L
  have support i:(S i).fires.val.Nonempty:=by
    cases i with
    | inl i => change (forced i).fires.val.Nonempty;rw [fired];exact Finset.singleton_nonempty _
    | inr i => exact (C i).chosen
  funext U
  let a:=P.p.threshold;let b:=Q.p.threshold
  let Z (i:V):=Poly.send (slot i) (dot (r i) ((X i).exponentialEntry 0 (T i) P (pull (s i) (ζ i) U)))
  have hs:(∑ i,Z i)=(∑ i,(file i).amount b U)+(∑ i,(error i).amount b U)+(∑ i,(forced i).occ U)+
      ∑ t:V×Keepat n,(far t.1 t.2).amount a U:=by
    rw [Fintype.sum_prod_type,←Finset.sum_add_distrib,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _=>emit i U)
  have paid:(∑ i,(C i).amount b U)+(∑ i,(dash P.p Q.p (C i) lower).occ U)=∑ i,(C i).amount a U:=by
    rw [←Finset.sum_add_distrib];apply Finset.sum_congr rfl;intro i _
    exact (dash_amount ..).symm
  have old:(∑ i,(A i).amount a U)+(∑ t:V×Keepat n,(far t.1 t.2).amount a U)=∑ i,(C i).amount a U:=
    (Fintype.sum_sum_type (f:=fun i=>(C i).amount a U)).symm
  have total:(∑ i,Z i)+(∑ i,(A i).amount a U)=(∑ i,(H i).amount b U)+(∑ i,(S i).occ U):=by
    rw [Fintype.sum_sum_type (f:=fun i=>(H i).amount b U),show (∑ i,(H (.inl i)).amount b U)=_ from Fintype.sum_sum_type _,
      Fintype.sum_sum_type (f:=fun i=>(S i).occ U)]
    change _=(((∑ i,(error i).amount b U)+(∑ i,(C i).amount b U))+(∑ i,(file i).amount b U))+
      ((∑ i,(forced i).occ U)+(∑ i,(dash P.p Q.p (C i) lower).occ U))
    rw [hs];linear_combination (norm:=abel) old-paid
  unfold credsX;simp only [one_mul]
  exact charge_por (H₁:=lower) S B H U (vacuum U) support total

end YM.Integration.WilsonThermometerWeakOriginalReclosure
end
