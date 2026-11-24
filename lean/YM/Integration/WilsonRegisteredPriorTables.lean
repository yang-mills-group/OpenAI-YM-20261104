import YM.Integration.WilsonRegisteredFiledOccurrence

/-! The Haar numerators of the earlier Ward variation on every genuine held field. -/

noncomputable section
namespace YM.Integration.WilsonRegisteredPriorTables
open Filter Finset Function Set MeasureTheory Lattice Wilson RG RG.Shoot Marker
open OPE.Therm Comparison.RG02 WilsonLimitConstruction WilsonInvariantActionPriorHearing WilsonInvariantActionRegisteredHearing
open private density_integral from YM.Integration.ActualWilsonConditionalRoots
open private five from YM.Integration.WilsonInvariantActionPriorHearing
open Function Filter Lattice Laurent Bloch Wilson RG Precision Exterior Tree PowerSeries Marker MeasureTheory
open IterationFour IterationFour.Vacuum Comparison.RG02 Comparison.RG02.Assembly
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank Stationary
open WilsonCoeffUV.Bank.Mosaic FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open WilsonLimitConstruction OriginalMarkedRunAction WilsonInvariantActionPriorHearing
open WilsonInvariantActionRegisteredHearing

open scoped ENNReal BigOperators Classical Topology
variable {G:Gauge} (R:Run G) {N per m:ℕ}
local notation "fine" => Config G (R.family.side (m+1) per)
local notation "coarse" => Config G (R.family.side m per)
local notation "Ω" => (coarse × fine)
local notation "P₁" => R.family.path.rep N per (m+1)
local notation "P₀" => R.family.path.rep N per m
local notation "Z" => partition G (R.family.side N per) (R.family.path.β N per N)
private def kernel (U:fine) (V:coarse):ℝ:=
  (R.family.path.levels.clock.op m per).density (R.family.path.β N per (m+1)) U V
local notation "K" => kernel R (N:=N)
local notation "μ" => prior G (R.family.side m per)
local notation "ν" => prior G (R.family.side (m+1) per)

def row (f:readings Ω) (V:coarse) : ℝ:=
  ∫U, K U V * (P₁).eval U * f.val (V,U) ∂ν

theorem slice (live:m<N) (f:readings Ω) (V:coarse):
    row R (N:=N) f V=(P₀).eval V*(conditional R live f).val V :=by
  have pos: (P₀).eval V≠0:=(Multi.AxisShift.chosen_positive R.makes.wilson (p:=per) live.le V).ne'
  symm
  change (P₀).eval V*(∫U,f.val (V,U) ∂ActualWilsonConditionalRoots.fibre R.family (N:=N) V)=_
  rw [ActualWilsonConditionalRoots.average R.family R.makes live]
  unfold actualAverage row
  rw [←integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun U=>by
    change (P₀).eval V*((K U V*(P₁).eval U/(P₀).eval V)*f.val (V,U))=_
    field_simp)

theorem raw (interior:m+1<N) (δ f:readings Ω) (V:coarse):
    row R (N:=N) (score R interior δ*f) V=∫U,K U V*δ.val (V,U)*f.val (V,U) ∂ν :=by
  apply integral_congr_ae
  refine ae_of_all _ (fun U=>?_)
  have pos : (P₁).eval U≠0:=(Multi.AxisShift.chosen_positive R.makes.wilson (p:=per) interior.le U).ne'
  change K U V*(P₁).eval U*(δ.val (V,U)/(P₁).eval U*f.val (V,U))=_
  field_simp

theorem earlier_haar (live:m<N) (f:readings coarse):
    earlier R (p:=per) live f=Z⁻¹*∫V,(P₀).eval V*f.val V ∂μ :=by
  let dens:=fun V:coarse=> dose (H:=R.family.path) (p:=per) m V N
  change (∫V,f.val V ∂(μ).withDensity (fun V=>ENNReal.ofReal (dens V)))=_
  rw [density_integral μ dens (dose_env (p:=per) R.makes.wilson live.le).meas
    (fun V=>(dose_positive (p:=per) R.makes.wilson live.le V).le),←integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun V=>by change ((P₀).eval V/Z)*f.val V=_;ring)

theorem deposited (live:m<N) (f:readings Ω):
    joint R (p:=per) live f=Z⁻¹*∫V,row R (N:=N) f V ∂μ :=by
  rw [joint,LinearMap.comp_apply,earlier_haar R live]
  simp only [slice R live]

private theorem collect {X Y:Type*} [CommRing X] [CommRing Y] [Algebra ℝ X] [Algebra ℝ Y]
    (E:Y→ₗ[ℝ]ℝ)(I:X→ₗ[ℝ]Y)(f h w:X):
    let α:=E (I f)
    let β:=E (I h)
    let c:=E (I (f*h))-α*β
    covariance E (I w) (covariance I f h)+cubic E (I w) (I f) (I h)=
      E (I w*(I (f*h)-α • I h-β • I f+(α*β-c) • 1)):=by
  dsimp only
  simp only [covariance,cubic,mul_add,mul_sub,map_sub,map_add,mul_smul_comm,mul_one,map_smul,smul_eq_mul]
  simp only [mul_left_comm,mul_comm]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem earlier_pair (live:m<N) (f h w:readings Ω):
    let I:=conditional R live
    let E:=earlier R (p:=per) live
    let α:=E (I f)
    let β:=E (I h)
    let c:=E (I (f*h))-α*β
    covariance E (I w) (covariance I f h)+cubic E (I w) (I f) (I h)=
      Z⁻¹*∫V,(row R (N:=N) w V/(P₀).eval V)*
        (row R (N:=N) (f*h) V-α*row R (N:=N) h V-β*row R (N:=N) f V+ (α*β-c)*(P₀).eval V) ∂μ :=by
  intro I E α β c
  let T:readings coarse:=I (f*h)-α • I h-β • I f+(α*β-c) • 1
  have joined:covariance E (I w) (covariance I f h)+cubic E (I w) (I f) (I h)=E (I w*T):=
    collect E I f h w
  rw [joined,earlier_haar R live]
  congr 1
  apply integral_congr_ae
  refine ae_of_all _ (fun V=>?_)
  simp only [slice R live]
  have pos: (P₀).eval V≠0:=(Multi.AxisShift.chosen_positive R.makes.wilson (p:=per) live.le V).ne'
  change (P₀).eval V*((I w).val V*(((I (f*h)).val V-α*(I h).val V)-β*(I f).val V+(α*β-c)*1))=_
  rw [mul_div_cancel_left₀ _ pos]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem all_five (live:m<N) (f h w:readings Ω):
    let J:=joint R (p:=per) live
    let α:=J f
    let β:=J h
    let c:=J (f*h)-α*β
    receipts R live f h w =
      Z⁻¹*∫V,(row R (N:=N) (f*h*w) V-α*row R (N:=N) (h*w) V-
        β*row R (N:=N) (f*w) V+(α*β-c)*row R (N:=N) w V) ∂μ :=by
  intro J α β c
  let T:readings Ω:=f*h*w-α • (h*w)-β • (f*w)+(α*β-c) • w
  have j:receipts R live f h w=cubic J f h w:=(five _ _ _ _ _).symm
  have combined:cubic J f h w=J T:=by
    simp only [T,cubic,c,α,β,map_add,map_sub,map_smul,smul_eq_mul]
    ring
  rw [j,combined,deposited R live]
  congr 1
  apply integral_congr_ae
  refine ae_of_all _ (fun V=>?_)
  simp only [slice R live,T,map_sub,map_add,map_smul]
  change (P₀).eval V*((((conditional R live) (f*h*w)).val V-α*((conditional R live) (h*w)).val V)-
    β*((conditional R live) (f*w)).val V+(α*β-c)*((conditional R live) w).val V)=_
  ring

end YM.Integration.WilsonRegisteredPriorTables
