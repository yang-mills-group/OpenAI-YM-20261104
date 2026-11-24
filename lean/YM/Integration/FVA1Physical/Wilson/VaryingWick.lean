import YM.Integration.FVA1Physical.Wilson.VaryingExponent
import YM.Integration.FVA1Physical.Wilson.VaryingExpansion
import YM.Integration.FVA1Physical.Wilson.MovingTicket

/-! Integrating the full retuned microscopic Taylor bill against the
inherited Gaussian is precisely the independent Wilson step. The density
and every insertion use the same chart, Gaussian and power-series clock. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function PowerSeries MeasureTheory Lattice RG YM.Wilson Tree Precision RGComparison.Core16 RGComparison.Core16.Descent
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested PertExtension.Series.Radial
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots FormalOPE.RG10.MultiGauge FormalOPE.RG10.MarkovChain.Warp
open FormalOPE.RG10.MultiGauge.Stack FormalOPE.RG10.MultiGauge.Splice FVA2 FVA2.CityHistory FVA2.RayScatter
open GaussianScore
open scoped Classical Topology ContDiff
variable {G : Gauge} {n c : Side} (d : Descent n c) (Z : ChartRatio G) (hZ : LocalRatio Z)
    (t : d.Tags) (h : d.Room G) (u : Pins G c)
    (z : ℕ → ℝ → ℝ) (w : ℕ → PowerSeries ℝ) (hot : ∀ i ≤ d.depth, ContDiffAt ℝ ω (z i) 0)
    (head : ∀ i ≤ d.depth, z i 0 = 1) (hw : ∀ i ≤ d.depth, Aspiration (z i) (term (w i)))
    (heads : Legacy.SoundZ w) (W : SpaceF G d → ℝ) (hW : ContDiffAt ℝ ω W 0)
set_option quotPrecheck false
local notation "J" => jacobian Z (U:=d.Links) ∘ Legacy.framesF d G
local notation "b" => (Fintype.card d.Tags : ℝ)⁻¹
local notation "m₀" => b*overhead Z d.Links
local notation "φ" => clockPhase d t u z
local notation "K" => clockAmplitude d Z W ∘ FVA2.RayScatter.recover u
local notation "I₀" => roll m₀ * (supplyZ d Z t w * rise W)

include hZ hW in
private theorem clock_amp_ledger :
    rise (clockAmplitude d Z W) = roll m₀ * (Legacy.birth Z d * rise W) := by
  have hj : ContDiffAt ℝ ω J 0 := Fork.Hhold Z hZ
  have jac : roll (overhead Z d.Links) * Legacy.birth Z d = rise J := by
    unfold Legacy.birth tissue
    rw [map_mul,boost_c,FormalOPE.RG10.MarkovChain.Vault.climbing _ ((Chart.Ratio.jacobian_smooth hZ).of_le le_top),
      ← mul_assoc]
    unfold Stack.roll
    rw [← map_mul,← map_mul,show jacobian Z (0:Coordinates G d) = overhead Z d.Links from rfl,
      mul_inv_cancel₀ (Stack.official hZ).ne',map_one,map_one,one_mul]
  have f : clockAmplitude d Z W = b • (J * W) := funext (fun x => by
    change jacobian Z x.1 * b * W x = b*(jacobian Z x.1 * W x)
    ring)
  rw [f,ExactTower.rise_natural (f:=J*W) b ((hj.mul hW).of_le le_top),rise_mul (f:=J) (g:=W) (hj.of_le le_top) (hW.of_le le_top),
    ← jac,show roll (E:=SpaceF G d) m₀ = roll b * roll (overhead Z d.Links) from by simp [roll,map_mul]]
  ring

include hot hw heads h hW hZ in
private theorem varied_integrand (i : ℕ) (x : Coordinates G d) :
    integrandSeries φ K i (1,x) = (coeff i I₀).val (x,u) := by
  have hg : ContDiffAt ℝ ω (clockAmplitude d Z W) 0 := clockAmplitude_hot d hZ hW
  have tilt : read (1,x) (rise K) = read (x,u) (rise (clockAmplitude d Z W)) := by
    apply PowerSeries.ext
    intro j
    rw [read_rise,read_rise,GermLaplace.jet_pull (FVA2.RayScatter.recover u) _ (hg.of_le le_top),recovery]
  have full : read (1,x) (rise K) * read (1,x) (exponential (advancing φ)) = read (x,u) I₀ := by
    rw [tilt,varied_interaction d t u (room_ok d h) z w hot hw heads x,clock_amp_ledger d Z hZ W hW,
      Legacy.money Z hZ (room_ok d h)]
    simp only [map_mul]
    ring
  rw [← reading_term,←full,coeff_mul]
  unfold integrandSeries Zone.mul
  apply Finset.sum_congr rfl
  intro j _
  rw [read_rise,business]

include hot head hw heads h hW hZ in
theorem varied_ticket :
    mk (varyingCoefficient d Z z t u W) = C (rayFactor d Z t u h) *
      read u (μLedger d Z t h w * premiere d Z t h w (rise W)) := by
  let Q := jointV (G:=G) d t
  let γ := gives d t h
  let μ := city G d
  let κ := γ.inner
  let ξ := Q.skew γ u
  let s := Real.exp (-1-(Q.reduced γ).flourish u/2)
  let P := basePower Q γ u μ 1
  have core (x : Coordinates G d) : kernel φ (1,x+ξ) = s * κ.kern x := by
    have U := square.size_inner Q γ u x
    rw [Quadratic.centering] at U
    have jq := progress d t (G:=G) (x+ξ,u)
    change Q.flourish (x+ξ,u)/2 = jet (consume d t 1) 2 (x+ξ,u) at jq
    unfold kernel
    rw [clockPhase_hessian d t u (room_ok d h) z hot head,rayPhase,
      cost_law 1 (thermal d t (room_ok d h) 1),if_pos rfl]
    unfold s κ Law.kern
    rw [← Real.exp_add]
    congr 1
    linarith
  have toll : mk (varyingCoefficient d Z z t u W) = C P * read u (Q.uptake μ γ I₀) := by
    apply PowerSeries.ext
    intro i
    rw [coeff_mk,varyingCoefficient,Therm.stamp_moment,coeff_C_mul,reading_term]
    unfold Quadratic.uptake throughPrice
    simp only [AddMonoidHom.coe_mk,ZeroHom.coe_mk,coeff_mk,LinearMap.toAddMonoidHom_coe]
    rw [Quadratic.integrateP_display]
    change _ = P * κ.average μ (fun x => (coeff i I₀).val (x+ξ,u))
    simp_rw [normTerm,varied_integrand d Z hZ t h u z w hot hw heads W hW]
    let r := coeff i I₀
    change (∫ x, r.val (x,u)*kernel φ (1,x) ∂μ) = _
    rw [← integral_add_right_eq_self (f:=fun x : Coordinates G d => r.val (x,u) * kernel φ (1,x)) (g:=ξ)]
    have hx := (ExactTower.venture κ μ).ne'
    unfold Law.average
    simp_rw [core,mul_left_comm (r.val _),integral_const_mul,Pi.mul_apply]
    change _ = (s*ExactTower.capital κ μ) * ((∫ x,r.val (x+ξ,u)*κ.kern x ∂μ)/(ExactTower.capital κ μ))
    field_simp
  rw [toll,Fork.roll_μ,share_part d t w h (rise W) Z hZ,map_mul,rollThrough,rayFactor]
  simp only [map_mul,mul_assoc]
  rfl

end YM.Integration.FVA1Physical.Wilson
