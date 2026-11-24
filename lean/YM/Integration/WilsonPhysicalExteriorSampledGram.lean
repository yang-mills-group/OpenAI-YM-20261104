import YM.Integration.WilsonPhysicalExteriorQuadratureClock
import YM.Integration.WilsonPhysicalExteriorSmoothPrice

/-! The original two-field MS far Gram on the fine regulator, with the
actual common origin average. Its order-zero matrix is again invertible
at every sufficiently late mesh; the stated errors are on the full named
matrix at each prescribed coupling order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorSampledGram
open Function Filter Set Finset Real Metric MeasureTheory Lattice RG RG16 Pert Pert.Position
open XSpace XSpace.Cirrus XSpace.Structure1 FVA2 FVA2.Register FVA2.Dframe MS MS.Land MS.Menus MS.Tone
open WilsonPhysicalExteriorMSQuadrature WilsonPhysicalExteriorQuadratureClock
open WilsonPhysicalExteriorActualSides WilsonPhysicalExteriorFirstCutScale Extra.FD
open scoped Topology BigOperators Classical
variable {G:Gauge}
local notation "B₀" => Press.portDeck G
variable (R:PhysicalNext.Repeat.Legato.Run G) (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (H:ℕ)
local notation "I" => Glyph B₀ H
local notation "Λ" => RG16.Lambda R.family.path.levels

def matrixOn (m:Mesh) (g:Test 2) (ν:ℝ) (k:ℕ) : Matrix I I ℂ :=
  fun a b=>WilsonPhysicalExteriorMSQuadrature.quadrature m g (fun z=>MSDeckProbeGram.raw M ![a,b] z ν k)

private theorem at_coordinates (ν:ℝ) (k:ℕ) (a b:I) (z:Points 2) :
    meteor ν M H z k (fill ![a,b])=MSDeckProbeGram.raw M ![a,b] z ν k :=
  ribbon ν M (t:=![a,b]) z k

private theorem entry {hG:G.Simple} (N:WilsonPrescription G)
    {S:Land.Prescription B₀} {dial:Bool} (issued:Main.Match N hG M S dial)
    (k:ℕ) (K:Set (Points 2)) (hc:IsCompact K) (sep:K⊆conf 2) (a b:I)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤log (Λ m)) {c c':ℝ} (h₁:1<c') (h₂:c'<c) (h₃:c<2)
    (lo:ℕ→ℕ) (h:ℕ) (budget q:ℝ) :
    ∀ᶠ j:ℕ in atTop,∀exterior physical:Bool,∀per≥WilsonPhysicalExteriorActualSides.floor R c lo j,
      ∀g:Test 2,tsupport g⊆K→∀u:ℝ,TestBudget.Bound g u→∀ν:ℝ,1+|ν|≤exp (budget*Λ j)→
      (ratio R c' j)^h*‖matrixOn M H (grid R c c' exterior physical (j,per)) g ν k a b-
        MSSeparatedTestGram.matrix M H ν k g a b‖≤u*exp (-q*Λ j) := by
  have buy:=WilsonPhysicalExteriorQuadratureClock.measured R N issued (fill ![a,b]) k K hc sep slow h₁ h₂ h₃ lo h budget q
  filter_upwards [buy] with j hj e s per hp g inK u gu ν hu
  have price:=hj e s per hp g inK u gu ν hu
  rw [Reg.CoverTest.indicative] at price
  simpa only [at_coordinates,matrixOn,MSSeparatedTestGram.matrix] using price

/-- Every entry of the entire genuine matrix on exactly the same mesh.
The cutoff already precedes the smooth probes and their real scales. -/
theorem whole {hG:G.Simple} (N:WilsonPrescription G)
    {S:Land.Prescription B₀} {dial:Bool} (issued:Main.Match N hG M S dial)
    (k:ℕ) (K:Set (Points 2)) (hc:IsCompact K) (sep:K⊆conf 2)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤log (Λ m)) {c c':ℝ} (h₁:1<c') (h₂:c'<c) (h₃:c<2)
    (lo:ℕ→ℕ) (h:ℕ) (budget q:ℝ) :
    ∀ᶠ j:ℕ in atTop,∀exterior physical:Bool,∀per≥WilsonPhysicalExteriorActualSides.floor R c lo j,
      ∀g:Test 2,tsupport g⊆K→∀u:ℝ,TestBudget.Bound g u→∀ν:ℝ,1+|ν|≤exp (budget*Λ j)→
      ∀a b:I,(ratio R c' j)^h*‖matrixOn M H (grid R c c' exterior physical (j,per)) g ν k a b-
        MSSeparatedTestGram.matrix M H ν k g a b‖≤u*exp (-q*Λ j) := by
  have buy:=Filter.eventually_all.mpr fun a:I=>Filter.eventually_all.mpr fun b:I=>
    entry R M H N issued k K hc sep a b slow h₁ h₂ h₃ lo h budget q
  filter_upwards [buy] with j hj e s per hp g inK u gu ν hu a b
  exact hj a b e s per hp g inK u gu ν hu

/-- A single positive normalized compact probe is presold at the requested
separated anchor. It measures an invertible matrix on every sufficiently
large original period and on the independent auxiliary regulator. -/
theorem detected {hG:G.Simple} (N:WilsonPrescription G)
    {S:Land.Prescription B₀} {dial:Bool} (issued:Main.Match N hG M S dial)
    {p:E4} (hp:(0:E4)≠p) (U:Set (Points 2)) (hu:U∈𝓝 (couple 0 p)) :
    ∃g:Test 2,tsupport g⊆U ∧ (∀z,(g z).im=0 ∧ 0≤(g z).re) ∧
      0<(g (couple 0 p)).re ∧ (∫z,g z)=1 ∧ IsUnit (MSSeparatedTestGram.matrix M H 0 0 g) ∧
      ∀(c c':ℝ), (∀m,((R.family.S.block m).val:ℝ)≤log (Λ m))→1<c'→c'<c→c<2→
      ∀lo:ℕ→ℕ,∀ᶠ j:ℕ in atTop,∀exterior physical:Bool,∀per≥WilsonPhysicalExteriorActualSides.floor R c lo j,
        IsUnit (matrixOn M H (grid R c c' exterior physical (j,per)) g 0 0) := by
  let V:Warehouse G:=⟨R.family.labels,R.family.params,R.family.localSection,R.makes.sections,fun d=>Next.Foundations.valuation G d⟩
  obtain ⟨g,sub,non,center,mass,hg,_,_⟩:=WilsonPhysicalExteriorSmoothPrice.purchased M H V hp U hu
  refine ⟨g,sub,non,center,mass,hg,?_⟩
  intro c c' slow h₁ h₂ h₃ lo
  let A:=MSSeparatedTestGram.matrix M H 0 0 g
  let J:=I×I
  let expand (s:J→ℂ):Matrix I I ℂ:=fun a b=>s (a,b)
  let values:J→ℂ:=fun ab=>A ab.1 ab.2
  have smooth : Continuous expand:=continuous_matrix fun a b=>continuous_apply (a,b)
  let live:={s:J→ℂ | (expand s).det≠0}
  have openLive:IsOpen live:=isOpen_ne_fun smooth.matrix_det continuous_const
  have inside:values∈live:=((Matrix.isUnit_iff_isUnit_det A).mp hg).ne_zero
  obtain ⟨δ,hδ,safe⟩:=Metric.isOpen_iff.mp openLive values inside
  obtain ⟨B,hB,fee⟩:=TestBudget.bound_fin g
  have price:=whole R M H N issued 0 (tsupport g) g.hasCompactSupport g.tsupport_subset slow h₁ h₂ h₃ lo 0 0 1
  have tends:Tendsto (fun j:ℕ=>B*exp (-(Λ j))) atTop (𝓝 0):=by
    simpa only [mul_zero,comp_apply] using (tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
      (Literal.lambda_leads R.family hG))).const_mul B
  filter_upwards [price,tends.eventually (gt_mem_nhds hδ)] with j hj small e s per hper
  let m:=grid R c c' e s (j,per)
  let now:J→ℂ:=fun ab=>matrixOn M H m g 0 0 ab.1 ab.2
  have dist:dist now values≤B*exp (-(Λ j)):=by
    rw [dist_eq_norm];apply (pi_norm_le_iff_of_nonneg (mul_nonneg hB.le (exp_pos _).le)).mpr
    intro ab
    dsimp only [Pi.sub_apply,now,values,A,m]
    simpa only [pow_zero,one_mul,zero_mul,neg_one_mul] using
      hj e s per hper g (Subset.rfl) B fee 0 (by simp) ab.1 ab.2
  have final:now∈live:=safe (dist.trans_lt small)
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr final)

end YM.Integration.WilsonPhysicalExteriorSampledGram
end
