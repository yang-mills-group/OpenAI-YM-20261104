import YM.Integration.FVA1Physical.Marked.LampFootprint
import YM.Integration.FVA1Physical.Round2.MeasuredFieldFee

/-! A finite census of freshly inserted canonical fields pays a single
coarse support ball irrespective of torus size. Only the actual stage
profile, finite placement radius, and the number of lamps enter the fare. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Finset Lattice RG YM.Wilson Precision Source Labels Extra.Histories
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat Next.Foundations Push.Uniform Push.Local
open Push.AbsoluteSums Further.LogJets LocalLTE Animals
open Integration.FVA1Physical.Marked RGComparison.Core16.Spool
open scoped Classical BigOperators
variable {G:Gauge} {I:Type} [Fintype I] {d:ℕ}

def lampFare (H:Stage) (m radius:ℕ) : ℝ :=
  (((m+1:ℕ):ℝ)*(1+(radius:ℝ))^H.power)^H.order*H.columns^m

theorem lamp_tariff_bound (H:Stage) (B:BudgetPoint) (a:I → CoverLabel G d)
    (power:B.power=H.power) (order:B.order=H.order) (radius:ℕ) :
    localFieldTariff B a H.columns radius ≤ lampFare H (Fintype.card I) radius := by
  have cols:0 ≤ H.columns:=zero_le_one.trans H.columns_ge
  have bank : (∏ j,H.columns*B.threshold^(((frames G).level (a j).1.val).grades (a j).2).2) ≤ 
      ∏ _j:I,H.columns := by
    apply prod_le_prod
    · intro _ _;exact mul_nonneg cols (pow_nonneg B.threshold_pos.le _)
    intro j _
    exact mul_le_of_le_one_right cols (pow_le_one₀ B.threshold_pos.le B.threshold_le)
  simp only [prod_const,card_univ] at bank
  unfold localFieldTariff lampFare
  rw [power,order]
  exact mul_le_mul_of_nonneg_left bank (by positivity)

theorem single_ball_fare {n:Side} (H:Stage) (B:BudgetPoint) (a:I → CoverLabel G d)
    (power:B.power=H.power) (order:B.order=H.order) (exponent:B.supportExponent=H.supportExponent)
    (radius:ℕ) (v:I → Site n) (placed:∀ j,separation (v j) 0 ≤ radius) (fit:radius+Vault.terr G d ≤ B.B)
    (part:Bool) {w:ℝ} (hw:0 < w) (permit:hitWidth B*Real.sqrt w ≤ 1) :
    birthCost B (lampSupport a v) w (localFieldTariff B a H.columns radius+
      ‖(look part (tally (freshLamps a) v 1):ℂ)‖) (2*stencilBound (freshLamps a)) ≤ 
      Real.exp (H.supportExponent+2)*(lampFare H (Fintype.card I) radius+3*stencilBound (freshLamps a)) := by
  have fee:=lamp_tariff_bound H B a power order radius
  have amp:‖(look part (tally (freshLamps a) v 1):ℂ)‖ ≤ stencilBound (freshLamps a):=by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using stencil_bounded (freshLamps a) v part 1
  have b0:0 ≤ localFieldTariff B a H.columns radius:=by
    have cols:=H.columns_ge
    have t:=B.threshold_pos
    unfold localFieldTariff
    positivity
  have pay:=birth_one_ball B (lampSupport a v) hw permit (lamp_one_ball a v radius B.B placed fit)
    (add_nonneg b0 (norm_nonneg (look part (tally (freshLamps a) v 1):ℂ))) (mul_nonneg zero_le_two (stencilBound_pos (freshLamps a)).le)
  rw [exponent] at pay
  exact pay.trans (mul_le_mul_of_nonneg_left (by linarith only [fee,amp]) (Real.exp_pos _).le)

end YM.Integration.FVA1Physical.Round2.Curvature
