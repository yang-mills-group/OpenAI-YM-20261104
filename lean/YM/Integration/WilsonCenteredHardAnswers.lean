import YM.Integration.WilsonCenteredHardMount
import YM.Integration.WilsonCenteredHardPartitions

/-! Each original admissible Wilson collection contributes its full
deposited hard face and its two distinct signed proper faces. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredHardAnswers
open Finset RG Lattice Wilson Marker QuadraticLocal Ac Planned.GuardedAtom Push.Local
open WilsonCenteredOriginalCaptureOwner WilsonCenteredCaptureSlots WilsonCenteredHardWallet WilsonCenteredHardMount
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {V X : Type} [DecidableEq V] {R : Census V} {o : V→Site n}
    {P : Rep G n} (H : Hard X P.p P.activities.forced P.activities.K o R)
    (K : Guard.Keeper P.p P.activities) (Z : Support n) (x : X) (U : Config G n)

def read (h : ℕ→ Config G n→ℂ) (U : Config G n) := ∑' F,gasMark P.p P.activities U F h

def once (s : R.Mode) (F : Finset ℕ) :=
  ∑i∈F,leg H s x i U*∏j∈F.erase i,(P.activities.K j U:ℂ)

theorem first_sum (s : R.Mode) (serial : ℕ×Finset ℕ ↪ ℕ) {b v : ℝ}
    (paid : ForceCost P.p P.activities (first H K Z s x serial) b) (quiet : P.activities.KBound P.p v) :
    HasSum (fun F=>if P.activities.admissible P.p U F then once H x U s F else 0)
      (read (P:=P) (first H K Z s x serial) U) := by
  have sum:=WilsonCenteredOccupiedHardRead.grouped (P:=P) (fun _:ℕ=>Z) unit U K serial (leg H s x)
    (fun _=>singleton_nonempty _) paid quiet
  apply sum.congr_fun
  intro F
  by_cases old : P.activities.admissible P.p U F
  · simp only [old,if_true,once]
    rw [tsum_eq_sum (s:=F) (fun i hi=>by simp [unit,hi])]
    apply sum_congr rfl
    intro i hi
    simp [unit,hi,sdiff_singleton_eq_erase]
  simp [old]

def distinct (a b : V) (F : Finset ℕ) :=
  WilsonCenteredHardPartitions.separate a b (fun i=>H.hard x i U) F

theorem second_sum (a b : V) (serial : (ℕ×ℕ)×Finset ℕ ↪ ℕ) {t v : ℝ}
    (paid : ForceCost P.p P.activities (second H K Z a b x serial) t) (quiet : P.activities.KBound P.p v) :
    HasSum (fun F=>if P.activities.admissible P.p U F then distinct H x U a b F else 0)
      (read (P:=P) (second H K Z a b x serial) U) := by
  have sum:=WilsonCenteredOccupiedHardRead.grouped (P:=P) (fun _:ℕ×ℕ=>Z) pair U K serial (mate H a b x)
    (fun z=>⟨z.1,mem_insert_self ..⟩) paid quiet
  apply sum.congr_fun
  intro F
  by_cases old : P.activities.admissible P.p U F
  · simp only [old,if_true]
    let t (z : ℕ×ℕ) := if pair z⊆F then mate H a b x z U*∏k∈F\pair z,(P.activities.K k U:ℂ) else 0
    symm
    change ∑' z,t z=_
    rw [tsum_eq_sum (s:=F×ˢF) (fun z outside=>?_),sum_product]
    swap
    · unfold t;split
      next contains=>exact (outside (mem_product.mpr ⟨contains (mem_insert_self ..),contains (mem_insert_of_mem (mem_singleton_self _))⟩)).elim
      rfl
    unfold distinct WilsonCenteredHardPartitions.separate
    apply sum_congr rfl
    intro i hi
    have cut : (∑j∈F,t (i,j))=∑j∈F.erase i,t (i,j) := by
      symm
      apply sum_subset (erase_subset i F)
      intro j hj missed
      have eq : j=i:=by by_contra diff;exact missed (mem_erase.mpr ⟨diff,hj⟩)
      subst j;simp [t,mate]
    rw [cut,Multi.first_of_prod,mul_sum]
    apply sum_congr rfl
    intro j hj
    have cond : pair (i,j)⊆F := insert_subset_iff.mpr ⟨hi,singleton_subset_iff.mpr (mem_of_mem_erase hj)⟩
    have diff : i≠j := (ne_of_mem_erase hj).symm
    have rest : F\pair (i,j)=(F.erase i).erase j := by
      ext k;simp [pair,not_or,and_assoc,and_comm,and_left_comm]
    simp only [t,if_pos cond,mate,if_neg diff,leg,rest,H.quiet,mul_assoc]
  simp [old]

end YM.Integration.WilsonCenteredHardAnswers
