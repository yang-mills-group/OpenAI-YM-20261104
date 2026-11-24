import YM.LocalLTE.Pool.Pass
import YM.LocalLTE.Pool.Glow
/-! # Boundary surface payments on same theory. Extra regular stencil tags; hail projection and rotate. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonStartup.Frost
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset
open AnalyticBridge VerifiedReset Collection Price
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf Urns
open LocalLTE.FrameBox LocalLTE.FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable (G : Gauge) {n : Side} {j:ℕ} {C V: ℝ}
attribute [local instance] Gauge.frobInner
open Start Animals
open Padded Ovens Pipes
variable {x t :ℝ} (M:ℕ) {κ k:ℝ} (p: BudgetPoint)(c:Clip)
open Topology Timing 
open Real (log exp)
open Payments RG.Shoot
variable (A:Stage) (η:ℝ) (L:Side)
-- issue uniform before Calendars. requisite p direct.YEP.
section cutoff
variable (a: Levels G)(m:ℕ)
local notation "P₀"=> a.params m
local notation "Q"=> (a.budget m)
local notation "ζ"=> a.clock.hatBeta m
local notation "σ"=> log (a.clock.hatBeta m)
local notation "λM"=> Timing.M σ
local notation "n'"=> quota σ
structure Cup (κ:ℝ) : Prop where
    must : Start.Allows a m
    time : 1 ≤ ζ
    size : 4 ≤ (Q).B
    e : η > 0
    hank: kettleP (Q) M η ≤1
    income :2*ζ* Start.item G Q ≤ η * ζ^chip 0
    frost (j:ℕ):j ≤ M→2*ζ*(turnFee Q* (betaF G ζ L)^(Urns.dust j-1))≤η*ζ^chip (j+1)
    bills (j:ℕ):j≤ M →∀ (n:Side) (_ :20<n.val)(o:PlaqAxes), (Q).supBounds (0:Site n) (neighbors 4 (0:Site n)) (residual G (0,o)-glaze G o κ j) ((betaF G ζ L)^(Urns.dust j-1))
    loan : Start.Loan Q (ζ/2) λM λM n'
    rates : Payments.Rates (Q).B (a.clock.forcedAllowance m) (exp (-λM)*(exp n'-1)) (Frost.soft (Q) η ζ) λM
lemma rentC (h:Reliable G κ k) (hp:η>0) (hr: kettleP (Time.probe A) M η ≤ 1):∀ᶠ x:ℝ in atTop,∀ (a: Levels G)(m:ℕ), a.params m=A→a.clock.hatBeta m=x → A.clip.direct ≤1 → Cup G M η L a m κ:=by
    by_cases h': A.clip.direct≤ 1; swap; · exact Eventually.of_forall fun x _ _ _ _ he=> False.elim (h' he)
    let u:=range (M+1); filter_upwards [Timing.enough G A h',eventually_ge_atTop (1:ℝ),Real.tendsto_log_atTop.eventually (Timing.nballs.eventually_ge_atTop 4), YM.Work.E07.temp_coarse_le G L, Frost.pay_ink G A η L hp, (eventually_all_finset u).mpr (fun j _=>pay_shelf G A η L j hp), Real.tendsto_log_atTop.eventually (Frost.rates A η hp.le),(eventually_all_finset u).mpr (fun j _ => Frost.can G L κ h A j)] with x hA ht hv hG hf he hB hX a m ha hx hd
    have hq:=hA a m ha hx; let s:= log x; let p:=a.budget m
    have h₁:p.order=A.order:=congr_arg Stage.order ha; have h₂:p.power=A.power:=congr_arg Stage.power ha; have h₃:p.supportExponent=A.supportExponent:=congr_arg Stage.supportExponent ha; have hk:p.B= Timing.balls (log x):=congr_arg Timing.balls (congr_arg log hx)
    have hz:0<x:=zero_lt_one.trans_le ht; have hb:(Real.sqrt x)⁻¹ = exp (-(log x / 2)) := by rw [Real.exp_neg,Real.sqrt_eq_rpow,Real.rpow_def_of_pos hz]; congr 2; ring
    have ht':p.threshold=Pressure.temp x:=by rw [←hx]; rfl
    have hτ:p.threshold=Timing.temp (log x):=by rw [ht',Pressure.temp,hb,Timing.temp,Real.exp_add]
    have hu : a.clock.forcedAllowance m = Timing.normK (log x) := by
       unfold Calendar.forcedAllowance Calendar.monitor Timing.normK; rw [hx,← Real.exp_mul]; congr 3; ring
    constructor
    · exact hq
    · rw [hx]; exact ht
    · change 4 ≤ p.B; rw [hk]; exact hv
    · exact hp
    · rw [sameCost (A:=A) _ η p h₃|>.1]; exact hr
    · rw [hx]; exact hf _ h₁ h₂ ht' (ht'.symm ▸ hG)
    · intro j hj; rw [hx]; exact he j (mem_range.mpr (by omega)) _ h₁ h₂
    · intro j hj n ht; rw [hx]; exact hX j (mem_range.mpr (by omega)) p h₁ h₂ ht' (ht'.symm ▸ hG) n ht
    · rw [hx]; have hv' := (hB p hτ hk h₃).1; rw [Real.exp_log hz] at hv'; exact hv'
    · rw [hu,hx]; have ht:=(hB p hτ hk h₃).2; rw [Real.exp_log hz] at ht; exact ht
-- at_calendar genesis
lemma cashC : ∃ η:ℝ,0<η∧ Frost.kettleP (Time.probe A) M η ≤1:=by
    let C:= Frost.kettleP (Time.probe A) M 1; have he :0 < C:=by unfold C kettleP kiosk; positivity
    refine ⟨C⁻¹,inv_pos.mpr he,Eq.le (by rw [← mul_inv_cancel₀ he.ne']; unfold kettleP C; unfold kettleP; ring)⟩ -- edit scope
end cutoff
-- Surface
end YM.WilsonStartup.Frost
