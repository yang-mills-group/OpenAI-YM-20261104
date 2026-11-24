import YM.Integration.WilsonPhysicalExteriorRichFarGram
import YM.FVA2.O.Read.Fire

/-! The finite, measured tree matrix of the separately paid R-rich word
deposits, at the original two possible return clocks.  Its inverse stays in a
fixed bounded neighborhood before the cutoff, period and choice of marks. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorRichFarFrame
open Function Filter Set Finset Real MeasureTheory Metric Lattice RG RG16 Pert Pert.Position
open XSpace FVA2 FVA2.Register MS MS.Land MS.Menus MS.Rake MS.Tone
open PhysicalNext.Repeat.Legato WilsonPhysicalExteriorActualSides WilsonPhysicalExteriorRichFarGram
open scoped Topology BigOperators Classical
variable {G:Gauge} (R:Run G) (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
variable (Q:Prescription (Press.portDeck G)) (H:ℕ)
local notation "B₀" => Press.portDeck G
local notation "I" => Glyph B₀ H
local notation "Λ" => RG16.Lambda R.family.path.levels
local notation "T₀" => WilsonPhysicalExteriorFirstCutScale.ratio R

/-- All signed coefficients of the original R-rich deposited readings; every
column, split and engineering weight is that of the original finite book. -/
def series (g:Test 2) (c c':ℝ) (s:Bool) (u:ℕ→ℝ) (z:Point) : Matrix I I (PowerSeries ℂ):=fun a b=>
  PowerSeries.mk (fun k=>gram R Q H g c c' s (u z.1) k z.1 z.2 a b)

theorem slice (g:Test 2) (c c':ℝ) (s:Bool) (u:ℕ→ℝ) (z:Point) (k:ℕ) :
    FVA2.O.Read.Slate.slice k (series R Q H g c c' s u z)=gram R Q H g c c' s (u z.1) k z.1 z.2:=by
  ext a b
  exact PowerSeries.coeff_mk _ _

private theorem along {c:ℝ} {lo:ℕ→ℕ} {P:Point→Prop}
    (h:∀ᶠ j:ℕ in atTop,∀per≥WilsonPhysicalExteriorActualSides.floor R c lo j,P (j,per)) :
    ∀ᶠ z in channel R c lo,P z:=by
  rw [channel,eventually_inf_principal]
  filter_upwards [(tendsto_comap : Tendsto (Prod.fst:Point→ℕ) (comap Prod.fst atTop) atTop).eventually h] with z hz sep
  exact hz z.2 sep

/-- The actual measured zeroth Gram slice on every sufficiently late original
period is invertible; all its inverse entries have one finite price on that
same period.  The order of the received cutoff and the two real subtraction
clocks is preserved. -/
theorem tree {hG:G.Simple} (N:WilsonPrescription G) {S:Prescription B₀} {dial:Bool}
    (issued:Main.Match N hG M S dial) (rows:WilsonPhysicalExteriorFirstCutPrice.Rows R M Q)
    (g:Test 2) (good:∀z,(g z).im=0 ∧ 0≤(g z).re) (pop:Nonempty (tsupport g))
    (nondeg:IsUnit (MSSeparatedTestGram.matrix M H 0 0 g))
    (slow:∀m,((R.family.S.block m).val:ℝ)≤log (Λ m)) {c c':ℝ} (h₁:1<c') (h₂:c'<c) (h₃:c<2)
    (lo:ℕ→ℕ) (μ:ℝ) (s:Bool) (u:ℕ→ℝ) (take:∀j,u j=μ ∨ u j=μ+R.family.S.scale j) :
    ∃B:ℝ,0≤B ∧ ∀ᶠ z in channel R c lo,
      let A:=FVA2.O.Read.Slate.slice 0 (series R Q H g c c' s u z)
      IsUnit A ∧ ∀a b:I,‖A⁻¹ a b‖≤B:=by
  let R₀:=MSSeparatedTestGram.matrix M H 0 0 g
  let F:=fun z:Point=>gram R Q H g c c' s (u z.1) 0 z.1 z.2
  let V:Warehouse G:=⟨R.family.labels,R.family.params,R.family.localSection,R.makes.sections,fun d=>Next.Foundations.valuation G d⟩
  have approx:=WilsonPhysicalExteriorRichFarGram.measured R M Q H N issued rows g good pop slow h₁ h₂ h₃ lo μ 1 0 0
  have points (a b:I):∀ᶠ z in channel R c lo,‖F z a b-R₀ a b‖≤exp (-(Λ z.1)):=by
    apply along R
    filter_upwards [approx] with j hj per hper
    have w:=hj s per hper a b
    change ‖gram R Q H g c c' s (u j) 0 j per a b-R₀ a b‖ ≤ _
    rw [show R₀=MSSeparatedTestGram.matrix M H (u j+log (T₀ c' j)) 0 g from MSSeparatedTestGram.scale V M H _ _ g]
    rcases take j with hh|hh <;> rw [hh]
    · simpa only [pow_zero,one_mul,neg_one_mul] using w.1
    · simpa only [pow_zero,one_mul,neg_one_mul] using w.2
  have Λlim: Tendsto (fun z:Point=>Λ z.1) (channel R c lo) atTop:=
    (Literal.lambda_leads R.family hG).comp (taking R c lo)
  have vanish:Tendsto (fun z:Point=>exp (-(Λ z.1))) (channel R c lo) (𝓝 0):=
    tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp Λlim)
  have entries (a b:I):Tendsto (fun z=>F z a b) (channel R c lo) (𝓝 (R₀ a b)):=by
    apply Metric.tendsto_nhds.mpr
    intro ε he
    filter_upwards [points a b,vanish.eventually_lt_const he] with z hz hw
    exact (show dist (F z a b) (R₀ a b)≤_ by simpa only [dist_eq_norm] using hz).trans_lt hw
  have gathered:Tendsto F (channel R c lo) (𝓝 R₀):=
    tendsto_pi_nhds.mpr fun a=>tendsto_pi_nhds.mpr fun b=>entries a b
  have hd:R₀.det≠0:=((Matrix.isUnit_iff_isUnit_det _).mp nondeg).ne_zero
  have invC:ContinuousAt Inv.inv R₀:=continuousAt_matrix_inv R₀ (by
    rw [Ring.inverse_eq_inv'];exact continuousAt_inv₀ hd)
  have hinv: Tendsto (fun z=>(F z)⁻¹) (channel R c lo) (𝓝 R₀⁻¹):=invC.tendsto.comp gathered
  have live:∀ᶠ z in channel R c lo,IsUnit (F z):=by
    have dets: Tendsto (fun z=>(F z).det) _ (𝓝 R₀.det):=continuous_id.matrix_det.continuousAt.tendsto.comp gathered
    filter_upwards [dets.eventually_ne hd] with z hz
    exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hz)
  let bound:=fun (p:I×I)=>‖R₀⁻¹ p.1 p.2‖+1
  have paid (p:I×I):∀ᶠ z in channel R c lo,‖(F z)⁻¹ p.1 p.2‖≤bound p:=by
    have atp:=tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hinv p.1) p.2
    exact (atp.norm.eventually_lt_const (by dsimp [bound];linarith)).mono (fun _ h=>h.le)
  refine ⟨∑p:I×I,bound p,Finset.sum_nonneg fun p _ => by dsimp [bound];positivity,?_⟩
  filter_upwards [live,(Filter.eventually_all).mpr paid] with z hz hB
  dsimp only
  rw [slice]
  refine ⟨hz,fun a b=>(hB (a,b)).trans (Finset.single_le_sum (f:=bound) (fun i _=>by dsimp [bound];positivity) (Finset.mem_univ (a,b)))⟩

end YM.Integration.WilsonPhysicalExteriorRichFarFrame
end
