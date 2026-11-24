import YM.Integration.WilsonLimitConstruction.FundedCensusVacuum
import YM.Integration.LocalComparisonPreReset

/-! The true high-order signed cluster remainder can occupy the unshifted
pre-reset source at any prescribed coupling. Comparison against a finite
rendering then has one explicit additive defect in the retained physical
action, with the original vacuum scalar and unchanged hard rows. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedCensusComparison

open Lattice Wilson RG RG.Shoot AnalyticBridge VerifiedReset Collection Push.SectorMeasure
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open IterationFour.Vacuum LocalComparison RG01Estimate RG01Estimate.CensusStep FundedCensusVacuum
open scoped BigOperators

variable {G : Gauge} {n : Side}

theorem rebase (X : Listing G n) (W : PathData G) (c : Clip) (p : BudgetPoint)
    (v : Collection.Source G n) (β b τ α : ℝ) (z : Config G n) :
    earlyValue X W c p v β τ α z = earlyValue X W c p v b τ 0 z *
      Real.exp (-(W.inChannels c p β z - W.inChannels c p b z + α * receipt W c p z)) := by
  have combine (a d k : ℝ) : Real.exp a * k * Real.exp d = Real.exp (a+d) * k := by
    rw [Real.exp_add]
    ring
  simp only [earlyValue,frozen,Rep.eval,Rep.exponent,neg_zero,zero_mul,Real.exp_zero,mul_one]
  rw [combine,combine]
  congr 2
  ring

variable {R : Run G} {N p m : ℕ} (S : Station R N p m) (r : ℕ)

def action (b : ℝ) (z : Config G (R.family.side m p)) : ℝ :=
  let W := R.alloy.B.kin.path N m
  let P := R.alloy.B.a.budget m
  let c := (R.alloy.B.a.params m).clip
  let X := ledger R.kit S.guide
  let K := kept R.kit S.guide S.guide S.identity r
  let β := (R.family.path.rep N p (m+1)).beta
  (X.read K).additive P z + (W.inChannels c P β z - W.inChannels c P b z) +
    R.alloy.B.kin.alpha N m * receipt W c P z

variable {r}

theorem density (hm : m < N) (hs : Account R.kit S.guide S.guide S.identity r)
    (O : Tree.Forest (R.alloy.B.a.clock.op m p).ratio) (b : ℝ)
    (z : Config G (R.family.side m p)) :
    let X := ledger R.kit S.guide
    let D := discarded R.kit S.guide S.guide S.identity r
    (R.family.path.rep N p m).eval z = earlyValue X (R.alloy.B.kin.path N m)
      (R.alloy.B.a.params m).clip (R.alloy.B.a.budget m) D b
      (Song.weighty S.guide Chi.canonical O) 0 z * Real.exp (-action S r b z) := by
  intro X D
  let W := R.alloy.B.kin.path N m
  let c := (R.alloy.B.a.params m).clip
  let P := R.alloy.B.a.budget m
  let β := (R.family.path.rep N p (m+1)).beta
  let τ := Song.weighty S.guide Chi.canonical O
  let α := R.alloy.B.kin.alpha N m
  let K := kept R.kit S.guide S.guide S.identity r
  have hx := hs.recorded.trans (add_comm _ _)
  calc
    _ = earlyValue X W c P (vacuum R.kit S.guide S.guide S.identity) β τ α z :=
      (congr_fun (R.makes.wilson.steps N p m hm).1 z).trans (hs.integral O z)
    _ = earlyValue X W c P D β τ α z * Real.exp (-(X.read K).additive P z) :=
      VacuumListing.reassemble P hs.high hs.low hx rfl β τ W c z
    _ = _ := by
      rw [rebase X W c P D β b τ α z,mul_assoc,← Real.exp_add]
      congr 2
      have rotate (x y a d : ℝ) : -(x-y+a) + -d = -(d + (x-y) + a) := by ring
      exact rotate (W.inChannels c P β z) (W.inChannels c P b z) (α * receipt W c P z)
        ((X.read K).additive P z)

/-- Exact comparison with every proposed list of summable packets and any
prescribed coupling. The outstanding discrepancy is the retained-action
difference shown in the exponent on the actual configuration. -/
theorem append (hm : m < N) (hs : Account R.kit S.guide S.guide S.identity r)
    (O : Tree.Forest (R.alloy.B.a.clock.op m p).ratio) (b : ℝ)
    (layers : List (Piece G (R.family.side m p))) (k : Piece G (R.family.side m p) → ℝ)
    (sums : ∀ w ∈ layers, ∀ z, Summable (fun i =>
      masked (R.alloy.B.a.budget m).threshold (w.packet.labels i).support (w.packet.action i) z))
    (z : Config G (R.family.side m p)) :
    let X := ledger R.kit S.guide
    let D := discarded R.kit S.guide S.guide S.identity r
    let P := R.alloy.B.a.budget m
    let Q := PreReset.append layers (R.alloy.B.kin.path N m) (R.alloy.B.a.params m).clip P X D
      b (Song.weighty S.guide Chi.canonical O) 0 k
    (R.family.path.rep N p m).eval z = Q.eval z *
      Real.exp (-(action S r b z - Render.renders k P z layers)) := by
  intro X D P Q
  have hp := PreReset.append_eval layers (R.alloy.B.kin.path N m) (R.alloy.B.a.params m).clip P
    X D b (Song.weighty S.guide Chi.canonical O) 0 k (R.alloy.B.support.cap N m hm.le)
    (PreReset.series_of_EBound hs.high.unweighted) sums z
  change Q.eval z = _ at hp
  simp only [Reset.supplied,neg_zero,zero_mul,Real.exp_zero,mul_one] at hp
  rw [density S hm hs O b z,hp,mul_assoc,← Real.exp_add]
  congr 2
  ring

end YM.Integration.WilsonLimitConstruction.FundedCensusComparison
end
