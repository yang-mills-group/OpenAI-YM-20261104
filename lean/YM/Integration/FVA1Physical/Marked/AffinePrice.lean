import YM.Integration.FVA1Physical.Marked.AffineStep
import YM.RGComparison01.Splurge

/-! The combined non-seed/high-order price in physical units, on the
original anchored support and all regular derivative rows before reset. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Function Filter Lattice RG Wilson Pressure Tree Precision Push PriceCompiler RG.Supply Input Org
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato AnalyticBridge VerifiedReset Collection
open Progress.DirectedRecipe Height Roof Extra.Iteration Time ThroughLaunch Roost JointLoad
open ConnectedActivityE6 SectorMeasure Extra.Trajectories RG3.Script.Picnic
open AllOrder Transit WheelP Floe Floe.Step.PlanV Qlocal Qlocal.Parabola RGComparison01
open scoped BigOperators Classical Topology

theorem young_in_coupling {y β : ℝ} {k q : ℕ} (hy : 1 ≤ y) (hb : 0 < β) (band : β ≤ 2*y)
    (depth : q ≤ Burn.horizon k + 2) :
    Burn.young y k ≤ 2^q * (Coat.gStep β)^q := by
  have h₀ : 0 < y := zero_lt_one.trans_le hy
  have horizon : (q:ℝ) ≤ Burn.horizon k + 2 := by exact_mod_cast depth
  calc
    Burn.young y k ≤ y^(-(q/2:ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le hy
      rw [Burn.sale_eq]
      linarith
    _ = (Coat.gStep y)^q := by
      rw [show -(q/2:ℝ)=-(1/2:ℝ)*q by ring,Real.rpow_mul h₀.le,Real.rpow_neg h₀.le,
        Real.rpow_natCast,← Real.sqrt_eq_rpow]; rfl
    _ ≤ _ := by
      simpa only [mul_pow] using pow_le_pow_left₀ (Fare.gS y h₀).1.le (Geo.strip h₀ hb band) q

/-- Both error rows sit on the original addresses. The fixed-order bound
is uniform in the field, all anchored derivative directions and torus size;
the two terms are also exactly the perturbation exponent in Wet.restores. -/
theorem combined_affine_high {G : Gauge} {X : Metals G} {D : Rolls X.p} {A : Alloy X D}
    {F : Roost.Factor A} {m N : ℕ} {c f : Side} {R : Rep G f}
    {size : f.val=c.val*(A.B.a.S.block m).val} {H : Boulevard.Chartlet F.shape A N m size R}
    {q k : ℕ} {Ω : ℕ → Prop} {y slope : ℝ} (hy : 1 ≤ y) (hb : 0 < R.beta)
    (band : R.beta ≤ 2*y) (depth : q ≤ Burn.horizon k + 2)
    (nonneg : 0 ≤ Ocean.fee F m) (cheap : Ocean.fee F m ≤ slope)
    (paid : Ports.Wet F size H q Ω (Ocean.fee F m * Burn.young y k)) :
    let p := A.B.a.budget m
    Meadow.Budget p (Beam.marquee H p).reg
      ((Coast.inherited F size H Ω).logRead + (Coast.weeded F size H Ω q).logRead)
      ((slope+2) * (2^q * (Coat.gStep R.beta)^q)) := by
  obtain ⟨u,early,regular⟩ := Ports.budgetS paid.bills paid.tails
  refine ⟨u,fun o => Push.AbsoluteSums.budget_loosen (early o) ?_,regular⟩
  have invoice := young_in_coupling hy hb band depth
  have price : 0 ≤ 2^q*(Coat.gStep R.beta)^q := mul_nonneg (by positivity) (pow_nonneg (Fare.gS _ hb).1.le _)
  change (Ocean.fee F m)*(Burn.young y k) + 2*(2^q*(Coat.gStep R.beta)^q) ≤ _
  calc
    _ ≤ slope * (2^q*(Coat.gStep R.beta)^q)+2*(2^q*(Coat.gStep R.beta)^q) :=
      add_le_add ((mul_le_mul_of_nonneg_left invoice nonneg).trans (mul_le_mul_of_nonneg_right cheap price)) (le_refl _)
    _ = _ := by ring

end YM.Integration.FVA1Physical.Marked
