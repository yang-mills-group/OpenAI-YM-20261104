import YM.Integration.WilsonMatrixTicketLanesNormalizedFleetVariation
import YM.Comparison.RG02.Cumulants.Parents

/-! The only quadratic change to the connected marked gas is its actual one-box numerator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesNormalizedFleetHard

open Function Finset Lattice RG Push Wilson Marker Extra.Trajectories MergeProof Accent
open WilsonMatrixTicketLanesNormalizedFleetLog
open scoped BigOperators Classical
variable {V : Type} [Fintype V] [DecidableEq V] {J : Census V} {G : Gauge} {n : Side}

/-- Sum over the original compatible covers, with one joint insertion and every unvaried box. -/
def numerator (R : Rep G n) (Z : Box n → Config G n → Poly J) (s : J.Mode) (U : Config G n) : ℂ :=
  ∑ b : Finset (Box n), if Pattern (flags R.p.threshold U) b then
    ∑ i ∈ b, (Z i U).part s * ∏ a ∈ b.erase i, profile R.activities
      (fun l => Complex.ofReal ∘ R.activities.K l) a U else 0

private theorem rest (R : Rep G n) (r : V → Box n → Config G n → ℂ) (U : Config G n) (i : Box n) :
    (bar R.activities J U i + Mach J (fun a => r a i U)).part J.quiet =
      profile R.activities (fun l => Complex.ofReal ∘ R.activities.K l) i U := by
  rw [Poly.part_plus,mute,add_zero]
  simp [bar,Poly.bead]

theorem raw (R : Rep G n) (r : V → Box n → Config G n → ℂ) (Z : Box n → Config G n → Poly J)
    (U : Config G n) (high : ∀ i, rises (Z i U)) (s : J.Mode) (small : s.val.card ≤ 2) :
    (hard R r Z U).part s - (hard R r (fun _ _ => (0 : Poly J)) U).part s = numerator R Z s U := by
  have eq := WilsonMatrixTicketLanesNormalizedFleetVariation.field
    (fun i => bar R.activities J U i + Mach J (fun a => r a i U)) (fun i => Z i U) high
    (flags R.p.threshold U) s small
  simpa only [hard,add_zero,numerator,WilsonMatrixTicketLanesNormalizedFleetVariation.variation,
    rest] using eq

theorem mixed (R : Rep G n) (r : V → Box n → Config G n → ℂ) (Z : Box n → Config G n → Poly J)
    (U : Config G n) (high : ∀ i, rises (Z i U)) (summable : Summable (fun l => R.activities.K l U))
    (pos : R.activities.gas R.p U ≠ 0) (a b : V) (ne : a ≠ b) (s : J.Mode) (seats : s.val = {a,b}) :
    (connected (divided (hard R r Z U))).part s -
      (connected (divided (hard R r (fun _ _ => (0 : Poly J)) U))).part s =
        numerator R Z s U / (R.activities.gas R.p U : ℂ) := by
  let H := hard R r Z U
  let K := hard R r (fun _ _ => (0 : Poly J)) U
  have small (t : J.Mode) (ht : t.val.card < 2) : H.part t = K.part t := by
    apply sub_eq_zero.mp
    have val := raw R r Z U high t (by omega)
    refine val.trans ?_
    apply Finset.sum_eq_zero
    intro f _
    split
    · refine Finset.sum_eq_zero fun i _ => ?_
      have zero : (Z i U).part t = 0 := by
        by_contra nz
        exact (not_le_of_gt ht) (high i t nz)
      rw [zero,zero_mul]
    · rfl
  have scalar : K.part J.quiet = (R.activities.gas R.p U : ℂ) := by
    dsimp only [K,hard]
    simp only [add_zero]
    exact stage₀ R.activities R.p U summable (rest R r U)
  have quiet : H.part J.quiet = (R.activities.gas R.p U : ℂ) :=
    (small _ (by simp [Census.quiet])).trans scalar
  have nz : (R.activities.gas R.p U : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr pos
  have idH : (divided H).part J.quiet = 1 := by rw [divided,Poly.part_smul,quiet,inv_mul_cancel₀ nz]
  have idK : (divided K).part J.quiet = 1 := by rw [divided,Poly.part_smul,scalar,inv_mul_cancel₀ nz]
  have singles (i : V) : (divided H).part (J.fire i) = (divided K).part (J.fire i) := by
    rw [divided,divided,Poly.part_smul,Poly.part_smul,quiet,scalar,
      small (J.fire i) (by simp [Census.fire])]
  change (connected (divided H)).part s - (connected (divided K)).part s = _
  rw [Comparison.RG02.Cumulants.twins a b s (divided H) idH ne seats,
    Comparison.RG02.Cumulants.twins a b s (divided K) idK ne seats,singles,singles,
    sub_sub_sub_cancel_right,divided,divided,Poly.part_smul,Poly.part_smul,quiet,scalar,←mul_sub]
  rw [show H.part s - K.part s = numerator R Z s U from raw R r Z U high s (by simp [seats,ne])]
  exact (div_eq_inv_mul ..).symm

end YM.Integration.WilsonMatrixTicketLanesNormalizedFleetHard
