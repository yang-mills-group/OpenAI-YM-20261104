import YM.Integration.WilsonCenteredWholeInventory
import YM.Integration.WilsonCenteredSoftInventory

/-! There are at most two choices for each participating physical mark, independent
of the other enrolled reporter names or the periodic volume. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredMaskPieces
open Finset RG Wilson Lattice Marker QuadraticLocal Push.Local
open WilsonCenteredSoftInventory
open scoped BigOperators Classical
variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
def splits (s : R.Mode) : Finset (R.Mode×R.Mode) :=univ.filter (fun z=>Poly.merges z.1 z.2 s)

omit [Fintype V] in
theorem valid {s : R.Mode} {z : R.Mode×R.Mode} (h : z∈splits s) : Poly.merges z.1 z.2 s :=
  (mem_filter.mp h).2

omit [Fintype V] in
theorem complement {s t u : R.Mode} (h : Poly.merges t u s) : u.val=s.val\t.val :=by
  ext v
  rw [mem_sdiff,←h.2,mem_union]
  exact ⟨fun a=>⟨Or.inr a,fun k=>disjoint_left.mp h.1 k a⟩, fun a=>a.1.resolve_left a.2⟩

omit [Fintype V] in
theorem size (s : R.Mode) : (splits s).card≤2^s.val.card :=by
  calc
    _ ≤ s.val.powerset.card :=by
      apply card_le_card_of_injOn (fun z : R.Mode×R.Mode=>z.1.val)
      · intro z hz
        change z.1.val∈s.val.powerset
        rw [mem_powerset,←(valid hz).2]
        exact subset_union_left
      intro z hz z' hz' eq
      change z.1.val=z'.1.val at eq
      apply Prod.ext (Subtype.ext eq)
      apply Subtype.ext
      rw [complement (valid hz),complement (valid hz'),eq]
    _ = _ :=card_powerset _

variable {G : Gauge} {n : Side} {P : Rep G n} {ι X : Type} {o : V→Site n}
theorem density (A : Gallery X ι o P R) (x : X) (U : Config G n) (s : R.Mode) :
    (A.density x U).part s =
      ∑z∈splits s,(Real.exp (P.exponent U):ℂ)*((Poly.pass (A.E.log x U)).part z.1*(A.gas x U).part z.2) :=by
  change ((Real.exp (P.exponent U):ℂ) • (Poly.pass (A.E.log x U)*A.gas x U)).part s=_
  rw [Poly.part_smul,←mul_sum,Poly.part_mul,splits,sum_filter,Fintype.sum_prod_type]

def quiet (P : Rep G n) (Z : Support n) : Receipt P Z (fun _=>1)
    (Real.exp ((P.p.supportExponent+2)*coverNumber P.p.B Z)) where
  Row :=Unit
  counted :=inferInstance
  ground :=fun _=>Z
  value :=fun _ _=>1
  price :=fun _=>1
  holds :=fun _=>Subset.rfl
  gauge :=fun _ _ _=>rfl
  borel :=fun _=>measurable_const
  uses :=fun _ _ _ _ _=>rfl
  nonnegative :=fun _=>zero_le_one
  cap :=fun _ _=>by simp
  cash :=⟨fun _=>mul_nonneg (Real.exp_pos _).le zero_le_one,(hasSum_fintype _).summable,by simp [reservedMass]⟩
  posted :=fun _=>by simp

end YM.Integration.WilsonCenteredMaskPieces
