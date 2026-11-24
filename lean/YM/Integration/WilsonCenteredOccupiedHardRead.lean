import YM.Integration.WilsonCenteredOwnerIntake
import YM.Integration.WilsonCenteredActualHardSum

/-! Group the complete original gas by its actual admissible collection and
the nonempty set of named occupied operands. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredOccupiedHardRead
open Finset Function Lattice Wilson RG Push.Local Planned.GuardedAtom
open WilsonCenteredOriginalCaptureOwner WilsonCenteredCaptureSlots WilsonCenteredCapturePush
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {P : Rep G n} {ι : Type}
    (T : ι→Support n) (I : ι→Finset ℕ) (U : Config G n)

def entry (z : Born P T I U) : Finset ℕ×ι := (z.2.val,z.1)

lemma injective : Injective (entry (P:=P) T I U) := by
  rintro ⟨i,⟨F,h⟩⟩ ⟨j,⟨H,k⟩⟩ w
  obtain rfl : F=H := congrArg Prod.fst w
  obtain rfl : i=j := congrArg Prod.snd w
  rfl

lemma lifted (z : Finset ℕ×ι) (live : (I z.2).Nonempty)
    (old : P.activities.admissible P.p U z.1) (own : I z.2⊆z.1) :
    ∃ q : Born P T I U,entry T I U q=z := by
  obtain ⟨i,seen⟩:=live
  exact ⟨⟨z.2,⟨z.1,old,own,i,mem_filter.mpr ⟨own seen,Or.inl seen⟩⟩⟩,rfl⟩

theorem grouped (K : Guard.Keeper P.p P.activities) (serial : ι×Finset ℕ ↪ ℕ)
    (f : ι→ Config G n→ℂ) (live : ∀ i,(I i).Nonempty) {a v : ℝ}
    (cash : ForceCost P.p P.activities (entered P K T I serial f) a)
    (quiet : P.activities.KBound P.p v) :
    HasSum (fun C=>if P.activities.admissible P.p U C then
        ∑' i,if I i⊆C then f i U*(∏ j∈C\I i,(P.activities.K j U:ℂ)) else 0 else 0)
      (∑' C,gasMark P.p P.activities U C (entered P K T I serial f)) := by
  let w (z : Finset ℕ×ι):=if P.activities.admissible P.p U z.1 ∧ I z.2⊆z.1 then
    f z.2 U*∏j∈z.1\I z.2,(P.activities.K j U:ℂ) else 0
  have actual:=WilsonCenteredActualHardSum.retained K T I serial f cash quiet U
  have zeroOut : ∀ z∉Set.range (entry (P:=P) T I U), w z=0 := by
    intro z out
    unfold w
    split
    next pair=>exact (out (lifted T I U z (live _) pair.1 pair.2)).elim
    rfl
  have all : HasSum w (∑' C,gasMark P.p P.activities U C (entered P K T I serial f)) := by
    apply ((injective T I U).hasSum_iff zeroOut).1
    apply actual.congr_fun
    intro q
    simp [w,entry,q.2.property.1,q.2.property.2.1]
  have byOld : HasSum (fun C=>∑' i,w (C,i)) (∑' C,gasMark P.p P.activities U C (entered P K T I serial f)) := by
    rw [←all.tsum_eq,all.summable.tsum_prod]
    exact all.summable.prod.hasSum
  apply byOld.congr_fun
  intro C
  by_cases h : P.activities.admissible P.p U C
  · simp [h,w]
  simp [h,w]

theorem original (K : Guard.Keeper P.p P.activities) (serial : ι×Finset ℕ ↪ ℕ)
    (f : ι→ Config G n→ℂ) (live : ∀ i,(I i).Nonempty) {a v : ℝ}
    (cash : ForceCost P.p P.activities (entered P K T I serial f) a)
    (quiet : P.activities.KBound P.p v) :
    (∑' C,gasMark P.p P.activities U C (entered P K T I serial f)) =
      ∑' C,if P.activities.admissible P.p U C then
        ∑' i,if I i⊆C then f i U*(∏ j∈C\I i,(P.activities.K j U:ℂ)) else 0 else 0 :=
  (grouped T I U K serial f live cash quiet).tsum_eq.symm

end YM.Integration.WilsonCenteredOccupiedHardRead
