import YM.Comparison.RG02.Adjacent.Equivalent

/-! Finite jets on the original moving marked test with two measured clocks. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.MSFixedRatioClockComposition
open Function Filter Finset Comparison.RG02 Comparison.RG02.Adjacent
open Comparison.RG02.Moving Comparison.RG02.Moving.Path
open scoped Classical Topology ContDiff
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
def compose (K L : UnitCost) : UnitCost where
  rating t:=L.rating t*K.rating (L.enter t)
  origin:=by simp [UnitCost.borne,K.origin,L.origin]
  smooth:=L.smooth.mul ((show ContDiffAt ℝ ω K.rating (L.enter 0) by simpa using K.smooth).comp _ L.here)

theorem measured (K L : UnitCost) (W : Adjacent.Display X) {r : ℕ} {m : ℕ→ℤ}
    (h : Adjacent.Charge r m W) {i : ℕ} (hi : i≤r) :
    Adjacent.born (Adjacent.born W K 0 r) L 0 r i=Adjacent.born W (compose K L) 0 r i := by
  funext x
  let k : ℝ→X:=fun t=>L.inverseCurve.rating t • x
  let A:=Adjacent.born W K 0 r
  have hk : ContDiffAt ℝ ω k 0:=L.inverseCurve.smooth.smul contDiffAt_const
  have hs:=(Adjacent.curvedAt 0 r h K k hk).respite L
  have left : (fun t=>Adjacent.ages A 0 r t (L.rating t) x) =ᶠ[𝓝 0]
      (fun t=>Adjacent.cover A r (L.enter t) (k (L.enter t))) := by
    filter_upwards [L.rightInverse.stays] with t ht
    change L.inverseCurve.rating (t*L.rating t)=(L.rating t)⁻¹ at ht
    simp only [Adjacent.ages,zpow_zero,Complex.ofReal_one,one_mul,k,ht,UnitCost.enter]
  have right : (fun t=>Adjacent.ages W 0 r (L.enter t) (K.rating (L.enter t)) (k (L.enter t))) =ᶠ[𝓝 0]
      (fun t=>Adjacent.ages W 0 r t ((compose K L).rating t) x) := by
    filter_upwards [L.rightInverse.stays] with t ht
    change L.inverseCurve.rating (t*L.rating t)=(L.rating t)⁻¹ at ht
    simp only [Adjacent.ages,zpow_zero,Complex.ofReal_one,one_mul,k,ht,compose,smul_smul,
      mul_inv_rev,UnitCost.enter,mul_assoc]
  calc
    _ = motion _ i := Moving.Shift.mgerm left
    _ = motion _ i := hs.aligns i hi
    _ = _ := Moving.Shift.mgerm right
end YM.Integration.MSFixedRatioClockComposition
end
