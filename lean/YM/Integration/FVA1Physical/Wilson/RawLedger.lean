import YM.Integration.FVA1Physical.Wilson.FirstLedger

/-! Before centering, the physical phase integral differs from the absolute
RG02 vacuum reading by its explicit free determinant and tree-chart density.
This factor is independent of the coupling at every fixed coarse field. -/
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Set MeasureTheory RG Lattice YM.Wilson Tree Precision Marker
open FVA2.CityHistory FVA2.RayScatter FormalOPE.RG10.MultiGauge
open RGComparison.Core16 RGComparison.Core16.Spool RGComparison.Core16.Lumen
open RGComparison.Core16.Parcel RGComparison.Core16.Parcel.Oven
open PertExtension PertExtension.Series PertExtension.Series.Tested Comparison.RG02
open Next.SectorChange Next.SectorChange.Gaussian
open scoped Classical Topology ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G}
    {O : ChartRatio G} (K : Bulk.Kernel S p P O) (F : Forest S.ratio) (t : S.Choices)

/-- The Gaussian determinant, Haar density constant and leading coarse quadratic. -/
def rawScale (u : Pins G c) : ℝ :=
  Real.exp (-1) * (coat (K.covariance F t) * Integral.tab (F:=F) (O:=O) *
    Integral.calorie K F t 0 (axesP G c u))

theorem raw_phase_scalar {P₀ : Oven S.patch} (X : P₀.Form G) (u : Pins G c) {g : ℝ}
    (hg : 0 < g) :
    Fk.phaseAmt (Spool.lens (S := S) u X F) univ 1 g =
      rawScale K F t u * Bare.rho K F t (axesP G c u) g := by
  let x := axesP G c u
  let m := Next.Fluctuations.Sector.prefactor S G (Integral.temperature g)
  let I := ∫ y : Forge.Sky G F.Free,
    (Forge.Hut.seam S F (Oven.slice u g)).output g y ∂Forge.skillet G F.Free
  have ray : Integral.sample g x = Oven.slice u g := by
    unfold x Integral.sample
    rw [← (axesP G c).map_smul,direct_link]
    rfl
  have raw : S.push (Integral.temperature g) (bare (Integral.temperature g)) (Integral.sample g x) = m*I := by
    rw [ray]
    change S.push (g^2)⁻¹ (bare (g^2)⁻¹) (Oven.slice u g) = _
    rw [← inv_pow]
    exact Spool.quiet S u F K.branches
  let n := Fintype.card (F.Free × G.ColorIndex)
  have dim : Module.finrank ℝ (Fk.Panel G F.Free) = n := by
    simp [Fk.Panel,Module.finrank_pi_fintype,Gauge.Color,n,Fintype.card_prod]
  have phase : Fk.phaseAmt (Spool.lens (S := S) u X F) univ 1 g =
      Real.exp (-1) * ((g^n)⁻¹ * I) := by
    unfold Fk.phaseAmt
    simp only [Pi.one_apply,mul_one,setIntegral_univ,dim]
    rfl
  let D := coat (K.covariance F t)
  let a := Integral.tab (F:=F) (O:=O)
  let b := Integral.calorie K F t 0 x
  have hd : 0 < D := coat_pos (K.positive F t)
  have ha : 0 < a := pow_pos K.ratio.scale _
  have hb : 0 < b := Real.exp_pos _
  have hm : 0 < m := Next.Fluctuations.Sector.prefactor_pos _
  rw [phase]
  change _ = (Real.exp (-1) * (D * a * b)) *
    ((chartCost (K.covariance F t) g * (a * m * b))⁻¹ *
      S.push (Integral.temperature g) (bare (Integral.temperature g)) (Integral.sample g x))
  rw [chartCost_eq _ hg,raw]
  change _ = (Real.exp (-1) * (D * a * b)) * (((g^n * D) * (a * m * b))⁻¹ * (m * I))
  field_simp [hd.ne',ha.ne',hb.ne',hm.ne',hg.ne']

end YM.Integration.FVA1Physical.Wilson
