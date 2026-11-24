import YM.RG01Estimate.InteriorAdmission
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Token.Purple
/-!
# Costs of cutting an arbitrary dominated numerator on the short torus.

Evaluation proved BEFORE differentiating domains. Instead of a boundary term calculation
we use a neighborhood Estimate (seams for the vacuum directly, relative to authentic
K-density for general weights) and differentiate only the flat-coordinate interior model
and the genuine S.push (on all fields) via smooth norms. Then interpolate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Courtyard
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented PhysicalNext.Repeat
open PhysicalNext.Repeat.Lapis PhysicalNext.Repeat.Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums PhysicalNext.Repeat.Fare Sienna Conditioning
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f L : Side} {S : StepData c f} (F : Forest S.ratio) (T : Tube G S) (O : ChartRatio G)
    (k : S.Choices) (ρ : Bid.Dir G c→AxisChart G F) (B : BudgetPoint) (β D : ℝ) {p a s u v ε K₀ cQ α: ℝ} {j n : ℕ}
local notation "X" => Positions (Uniform.Primary c G)
local notation "K" => Precision.Key F G
local notation "Y" => Poll.Body K
local notation "M" => Lapis.gram F T.up T.high ρ k
local notation "A" => Lapis.table F k T.up T.high
local notation "μ" => Poll.sweep (M 0)⁻¹
local notation "H₀" => mist F O T.up
local notation "G₀" => Lapis.orbit F ρ
local notation "V" => (fun x : X=> represent (tint G _ x))
local notation "d" => gStep β
local notation "P'" => price F T O k ρ β
local notation "R₀" => Pane.virgin T B β

section quotes
variable {P : Teller G} (Zh : Intake P T s (Pane.virgin T B β))
    {x : Positions (Uniform.Primary c G)} (hx : Interior F T O k ρ B β D x u p ε j)
lemma price_pos (h : LocalRatio O) (hp : 0<β) : 0 < P' x := mul_pos (sun F O β hp h) (Real.exp_pos _)
include hx
lemma base_pricing (he : ratify A H₀ G₀ M D (d,x) ≤ K₀) :
      den S β (Pane.virgin T B β).eval x ≤ price F T O k ρ β x * (K₀ + ε):= by
  have hp' := mul_le_mul_of_nonneg_left he (price_pos F T O k ρ β (x:=x) hx.opens hx.room.1).le
  rw [mul_add]; have hk:=hx.unmarked.2; change den S β (Pane.virgin T B β).eval x-_ ≤ _ at hk; linarith only [hp',hk]
-- cost for derivative of inverse. Requires valuation-relative price positivity.
lemma inverse_cost (hp : Brush n K₀ 1 Real.exp 0) (hl : n≤ j) : Brush n
      (clump n (Token.oat n p β+ Token.oat n p β) K₀*(P' x)⁻¹) 1 (fun y=> (P' y)⁻¹) x := by
   have he:= Token.octane F T O ρ β k hl hx.center hx.calcJ hx.room.1
   let f y:= coverLog F T O k ρ β y - coverLog F T O k ρ β x
   have hx' := composite he (show Brush n K₀ 1 Real.exp (f x) from by simpa [f] using hp)
   have hz := price_pos F T O k ρ β (x:=x) hx.opens hx.room.1
   have h:=hx'.smul (P' x)⁻¹; rw [Real.norm_of_nonneg (inv_pos.mpr hz).le,mul_comm] at h
   apply h.shimmy; filter_upwards with y
   change (P' y)⁻¹=(P' x)⁻¹* Real.exp (f y); unfold price f; rw [Real.exp_sub]; simp only [Real.exp_neg, _root_.mul_inv_rev,inv_inv]; field_simp

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
def invoice (U : Config G f → E) (x : X) := (P' x)⁻¹ • roll S β U x
local notation "N" => invoice F T O k ρ β
local notation "W" => ratify A H₀ G₀ M

variable {g : Config G f→ E} (hm : StronglyMeasurable g) (hv : ∀ x, ‖g x‖≤a* (Pane.virgin T B β).eval x)
    (ha : 0 ≤ a)
    {Z t K' : ℝ}
local notation "R'" => Token.prime G S.kernel n Z K₀ β t
include hm hv ha Zh
lemma gross (he : W D (d,x) ≤ K') (hp : Brush n K₀ 1 Real.exp 0)
    (hY : PaintSupply G n Z) (hr : (Fintype.card (Bond c):ℝ)≤ t) (hk : 0 ≤ R') (hl : n≤j) :
     Brush n (clump n (Token.oat n p β+ Token.oat n p β) K₀ * (R' * (a*(K'+ε)))*3^n) 1
        (N g) x := by
   have hX:= hx.center.trans_le hx.calcJ.small
   have h1:= inverse_cost F T O k ρ B β D hx hp hl
   have he' := base_pricing F T O k ρ B β D hx he
   have h2:= (Conditioning.marked S β hY hr hp x hx.rays ((R₀).envelope Zh.cap|>.integrable _) hk hm hv hX).climb (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he' ha) hk) le_rfl
   have hT:= ((h1.twins h2 (ContinuousLinearMap.lsmul ℝ ℝ)).climb (mul_le_of_le_one_left
        (mul_nonneg h1.nonneg h2.nonneg) (ContinuousLinearMap.opNorm_lsmul_le ..)) le_rfl).trim
   apply hT.climb _ le_rfl
   apply le_of_eq
   field_simp [show price F T O k ρ β x≠0 from (price_pos F T O k ρ β hx.opens hx.room.1).ne']; ring -- costs

lemma reduced_pricing (h : GaugeInvariant g) (H : Y → E) (hr : ∀ z:Y, ‖z‖≤D → g (field F ρ β x z) = (R₀).eval (field F ρ β x z) • H z) (hI : Integrable (restricted F T O k ρ D H (d,x)) μ) :
    ‖N g x-∫ i,restricted F T O k ρ D H (d,x) i ∂μ‖ ≤ a*ε := by
   let s:= P' x; let z:= ∫ i,restricted F T O k ρ D H (d,x) i ∂μ; have hP:=prices F T O k ρ B β D Zh hx H hm hI h hv hr ha
   have hS : 0 < s:= price_pos F T O k ρ β hx.opens hx.room.1
   change ‖s⁻¹ • S.push β g (V x)-z‖≤_
   rw [show s⁻¹ • S.push β g (V x)-z=s⁻¹ •(S.push β g (V x)-s •z) by rw [smul_sub,smul_smul, inv_mul_cancel₀ hS.ne',one_smul],norm_smul, Real.norm_of_nonneg (inv_pos.mpr hS).le]
   apply (inv_mul_le_iff₀ hS).2; exact hP.trans_eq (mul_left_comm ..)
end quotes
end YM.RG01Estimate.Courtyard
