import YM.Integration.WilsonThermometerRegisteredCapturedRoster
import YM.Integration.WilsonThermometerRegisteredCapturedOffers
import YM.Integration.WilsonCapturedPrimarySoftPartition

/-! Original disjoint mark partitions prepay their common scalar Laurent pole. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredCapturedNames
open RG Marker Lattice Wilson QuadraticLocal QuadraticLocal.Earn Finset
open Comparison.RG02.Cumulants Multi
open WilsonThermometerRegisteredCapturedRoster WilsonThermometerRegisteredCapturedOffers
open WilsonCapturedPrimarySoftPartition
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {P:Earn.Passport n (Fin 3)} {R:Census (Fin 3)} {α ι:Type}
variable (X:ι→Earn.Row P R G α) {s:R.Mode} (q:(parts R).Mode) (h:q∈shards R s)
abbrev Names := (j:Fin q.val.card)→Keys X (block q j)
def roster (u:Names X q) := List.ofFn fun j=>X (u j).val

include h

theorem debit (a:Fin 3→ℕ) :
    ∑ j:Fin q.val.card, ∑v∈(block q j).val,a v = ∑v∈s.val,a v :=by
  rw [←(mem_filter.mp h).2]
  change _=∑v∈q.val.biUnion Hot.sites,a v
  rw [sum_biUnion (parts_wise q)]
  calc
    _=∑v:↥q.val,∑z∈v.val.sites,a z:=(index q).sum_comp _
    _=_:=Finset.sum_coe_sort q.val (fun t=>∑z∈t.sites,a z)

theorem arity : q.val.card≤3:=by
  have partition:=debit q h (fun _=>1)
  simp only [Finset.sum_const,smul_eq_mul,mul_one] at partition
  calc
    _=∑_j:Fin q.val.card,1:=by simp
    _≤∑j:Fin q.val.card,(block q j).val.card:= by
      apply Finset.sum_le_sum
      intro j _
      exact Finset.card_pos.mpr ⟨root q j,seated q j⟩
    _=s.val.card:=partition
    _≤3:=(Finset.card_le_univ _).trans_eq (Fintype.card_fin 3)

omit h in
private lemma sum_ofFn {k:ℕ} (f:Fin k→ℕ) : (List.ofFn f).sum=∑j,f j:=by
  induction k with
  | zero=>simp
  | succ k ih=>rw [List.ofFn_succ,Fin.sum_univ_succ,List.sum_cons,ih]

theorem original {σ:ℝ} {ord:ℕ} (ages:Fin 3→ℕ) (income:Issues X σ ord ages)
    (spent:∑v:Fin 3,ages v≤14) (u:Names X q):
    allowed (roster X q u)≤21+1 ∧ angularRank (roster X q u)≤3*ord+17 ∧ degree (roster X q u)≤3*ord :=by
  have loans(j:Fin q.val.card) : (X (u j).val).lamp.toll=∑v∈(block q j).val,ages v:=by
    simpa only [(u j).property] using (income.usable (u j).val).2
  have age:∑v∈s.val,ages v≤14:=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _=>Nat.zero_le _)).trans spent
  have debt : allowed (roster X q u)≤17:=by
    unfold allowed roster
    rw [List.map_ofFn,sum_ofFn]
    change ∑j,((X (u j).val).lamp.toll+1)≤17
    simp_rw [loans]
    rw [Finset.sum_add_distrib,debit q h ages]
    rw [show (∑_:Fin q.val.card,(1:ℕ))=q.val.card by simp]
    have count:=arity q h
    omega
  have degree_le : degree (roster X q u)≤3*ord:=by
    unfold degree roster
    rw [List.map_ofFn,sum_ofFn]
    calc
      _≤∑_j:Fin q.val.card,ord:= Finset.sum_le_sum (fun j _=>(income.usable (u j).val).1)
      _≤_:=by simpa using Nat.mul_le_mul_right ord (arity q h)
  exact ⟨by omega,(WilsonThermometerRegisteredCapturedRoster.rank_le _).trans (Nat.add_le_add degree_le debt),degree_le⟩
end YM.Integration.WilsonThermometerRegisteredCapturedNames
