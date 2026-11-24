import YM.Integration.WilsonCenteredWholeInventory
import YM.Integration.WilsonCenteredOccupiedHardSets

/-! In every original eligible collection the true hard packet is its full
sum of nonempty selected owner sets. This applies before the outer Wilson sum. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredHardSetRead
open Finset Wilson RG Lattice Marker QuadraticLocal Function
open WilsonCenteredOccupiedFamilies WilsonCenteredOccupiedHardSets
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {V X : Type} [DecidableEq V] {R : Census V} {o : V→Site n}
    {P : Rep G n} (H : Hard X P.p P.activities.forced P.activities.K o R)

def contribution (s : R.Mode) (x : X) (U : Config G n) (F I : Finset ℕ) : ℂ :=
  if I⊆F then (∏j∈I,dye s (H.hard x j U)).part s*(∏j∈F\I,(P.activities.K j U:ℂ)) else 0

theorem collection (s : R.Mode) (live : s≠R.quiet) (x : X) (U : Config G n) (F : Finset ℕ) :
    (Fusion.Attached.packet P.activities P.p (H.hard x) U F).part s =
    if P.activities.admissible P.p U F then ∑' I : Chosen, contribution H s x U F I.val else 0 :=by
  change _=if _ then ∑' I : {i : Finset ℕ // i.Nonempty},(contribution H s x U F) I.val else 0
  have supp : Function.support (contribution H s x U F) ⊆ {I|I.Nonempty} :=by
    intro I nonzero
    by_contra! empty
    have missing : I=∅ := Finset.not_nonempty_iff_eq_empty.mp empty
    subst I
    exact nonzero (by simp [contribution,Poly.one_part,live])
  have reindex : (∑' I : Chosen,contribution H s x U F I.val)=∑' I : Finset ℕ,contribution H s x U F I :=
    tsum_subtype_eq_of_support_subset supp
  rw [reindex,WilsonCenteredWholeInventory.collection]
  by_cases valid : P.activities.admissible P.p U F
  · simp only [WilsonCenteredWholeInventory.onHard,if_pos valid]
    rw [sum_filter,tsum_eq_sum (s:=F.powerset) (fun I missing=>by
      simp [contribution,show ¬I⊆F by simpa using missing])]
    apply sum_congr rfl
    intro I inside
    rw [contribution,if_pos (mem_powerset.mp inside)]
    by_cases capped : I.card ≤ s.val.card
    · simp [capped,mul_comm]
    rw [if_neg capped,vanish I _ (fun j=>WilsonCenteredOccupiedFamilies.quiet s (H.hard x j U)) s (Nat.lt_of_not_ge capped),zero_mul]
  simp [WilsonCenteredWholeInventory.onHard,valid]

end YM.Integration.WilsonCenteredHardSetRead
