import YM.Integration.WilsonOriginalGroupInkDirections

/-! A bound on one homogeneous directional coefficient controls the complete ordered joint derivative. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMixedRadialPrice
open Function AllOrder.Fire PertExtension.Series
open scoped BigOperators Classical ContDiff
variable {X:Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

theorem original (f:X→ℝ) (ink:ℂ) (m:ℕ) (smooth:ContDiffAt ℝ ω f 0) {C:ℝ} (C0:0≤C)
    (read:∀z:X,‖z‖≤(m:ℝ)→|‖ink‖*Radial.jet f m z|≤C) (arg:Fin m→X)
    (unit:∀i,‖arg i‖≤1) : ‖iteratedFDeriv ℝ m (fun z=>ink*(f z:ℝ)) 0 arg‖
      ≤ WilsonMarkedAngularTestInvoice.fee m m*C:=by
  let H:X→ℝ:=fun z=>‖ink‖*Radial.jet f m z
  have rank:Rank X m H:=(AllOrder.Haiku.Project.maturity f m).scal _
  have wage:=WilsonMarkedAngularTestInvoice.linear (le_rfl:m≤ m) rank C0 read
  have price:=(((iteratedFDeriv ℝ m H 0).le_opNorm arg).trans
    (mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one (fun i _=>norm_nonneg _) (fun i _=>unit i)))).trans wage
  let re:ℝ→L[ℝ]ℝ:=(ContinuousLinearMap.id ℝ ℝ).smulRight ‖ink‖
  let co:ℝ→L[ℝ]ℂ:=(ContinuousLinearMap.id ℝ ℝ).smulRight ink
  have hre:H=re ∘ Radial.jet f m:=by
    funext z;change ‖ink‖*Radial.jet f m z=Radial.jet f m z*‖ink‖;ring
  have hco:(fun z=>ink*(f z:ℝ))=co ∘ f:=by
    funext z;change ink*_=(f z:ℝ) • ink;rw [Complex.real_smul];ring
  have hcast:=WilsonMarkedAngularTestInvoice.regular (AllOrder.Haiku.Project.maturity f m) m
  rw [hre,re.iteratedFDeriv_comp_left hcast.contDiffAt le_rfl,AllOrder.Haiku.Project.self f smooth m] at price
  rw [hco,co.iteratedFDeriv_comp_left (smooth.of_le (m:=m) le_top) le_rfl]
  change ‖(iteratedFDeriv ℝ m f 0 arg) • ink‖≤_
  change ‖(iteratedFDeriv ℝ m f 0 arg) • ‖ink‖‖≤_ at price
  simpa only [norm_smul,norm_norm] using price

end YM.Integration.WilsonOriginalMixedRadialPrice
