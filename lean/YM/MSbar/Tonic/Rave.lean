import YM.MSbar.Tonic.Bond
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Tonic
open Function Filter Whisk Lis Measuring Cacao Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Exterior Wilson Wave
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{c f:Side}{S:StepData c f}
local notation "J"=> Positions (Primary c G)
local notation "X"=> Primary c G
local notation "Q"=> Config G f
variable (β t:ℝ)(U:Config G f)(M:Config G c)(v:S.Choices)
local notation "B₀"=> tribe S β t U v
local notation "Φ"=> wing S U v
variable (x:Positions (Primary c G))(L:List (Primary c G))(i j:Primary c G)(e:Bond c)
variable (hc:S.patch.Branches S.kernel G)
local notation "H"=>prior G f
include hc
variable (R: Rep G f)(τ A B C D:ℝ)(hR:R.Lawful τ A B C D)
-- density old milk U-term derivative `S likelihood`.
local notation "W"=> fun x:J=> postcard G c t x
local notation "i!"=>R.eval
local notation "q!"=> lid S β t G R v
include hR
-- sum-axis all t.R scaled numerator pieces. Need integral l rule
open Bulk
local notation "V"=>railV S β t R
noncomputable def PPress (S:StepData c f)(β t:ℝ) (R:Rep G f)(x:Positions (Primary c G)) := ∫ U:Config G f, railV S β t R U x ∂prior G f
local notation "ζ"=> PPress S β t R
lemma erection (k:List J): roc ζ k x = ∫ U,roc (V U) k x ∂H :=by
    induction k generalizing x with |nil=>rfl|cons a l ih=>rw [roc, show roc ζ l= _ from funext ih]; exact entry β t x hc R τ A B C D hR l|>.2 _
lemma curvet (n:ℕ): ContDiff ℝ n ζ:=by
    have he(n:ℕ)(k:List J) : ContDiff ℝ n (roc ζ k):=by
       induction n generalizing k with
       | zero=> rw [Nat.cast_zero]; apply contDiff_zero.mpr; have hs:=funext fun x=> erection β t x hc R τ A B C D hR k; rw [hs]; refine Differentiable.continuous (𝕜:=ℝ) fun x=> entry β t x hc R τ A B C D hR k|>.1.differentiableAt
       | succ n ih=> rw [Nat.cast_succ]; refine contDiff_succ_iff_fderiv_apply.mpr ⟨?_,by simp,fun x=> ih (x::k)⟩; rw [show roc _ _= _ from funext fun x=> erection β t x hc R τ A B C D hR k]; exact fun x=>entry β t x hc R τ A B C D hR k|>.1.differentiableAt
    exact he n []
variable (hβ:β=R.beta)(hs:∀ U, 0 < R.eval U)
include hs
noncomputable def rave (S: StepData c f)(β t:ℝ)(R: Rep G f)(L:List (Primary c G))(x:Positions (Primary c G))(U:Config G f) := buoy (railV S β t R U) x L / railV S β t R U x
lemma wealth (U:Config G f)(x:J) : 0 < V U x:=by rw [blend β t hc R τ A B C D hR]; exact mul_pos (nut_pos ..) (mul_pos (Progress.DirectedRecipe.density_strict S β hc ..) (hs ..))
lemma prec : PPress S β t R x= nut S β G * S.push β R.eval (W x):=by unfold PPress StepData.push; simp_rw [blend β t hc R τ A B C D hR, integral_const_mul, smul_eq_mul]
lemma base : 0 < ζ x:=by rw [prec β t x hc R τ A B C D hR hs]; exact mul_pos (nut_pos ..) (Progress.DirectedRecipe.push_strict S β hc hs ((R.envelope hR).integrable _) _)
local notation "Z!"=> rave S β t R L x
lemma rents_r (U:Config G f) : rave S β t R L x U*railV S β t R U x=∑ i:S.Choices, lid S β t G R i U x *strap S β t i x L U :=by
    unfold rave; rw [div_mul_cancel₀ _ (wealth β t hc R τ A B C D hR hs U x|>.ne')]; unfold buoy; rw [cruise β t hc R τ A B C D hR]; refine Finset.sum_congr rfl fun i _=>?_ ; unfold lid strap; have hz:0< crew S β t U i x:=Real.exp_pos _;field_simp;rfl
lemma stipend : Measurable (rave S β t R L x):=by
     unfold rave; apply Measurable.div; exact (bond β t hc R τ A B C D hR _ _ (isCompact_closedBall x (1:ℝ))).1 x; exact (bond β t hc R τ A B C D hR [] _ (isCompact_closedBall x (1:ℝ))).1 x
lemma lust {p:ℕ}{K:ℝ}(h:PriceR G p K)(hp : |t| ≤ 1)(hl:L.length≤p)(hv:shade G*|t| *‖x‖≤1)(U:Config G f) : |rave S β t R L x U| ≤ sizeP L.length (glow S.kernel p β K G):=by
    have hK:= wealth β t hc R τ A B C D hR hs U x; let q:=Z!; apply le_of_mul_le_mul_right _ hK; rw [← abs_of_pos hK] -- bad rewrites both?
    rw [← abs_mul,rents_r β t x L hc R τ A B C D hR hs,abs_of_pos hK]; unfold railV; rw [Finset.mul_sum]; refine (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun i _=>?_); have hx: 0 ≤ lid S β t G R i U x:= mul_nonneg (mul_nonneg (S.likelihood_pos ..) (hs _|>.le)) (Real.exp_pos _|>.le); rw [abs_mul, abs_of_nonneg hx]; exact (mul_le_mul_of_nonneg_left (price_u β t U i x L h hp hl hv) hx).trans_eq (mul_comm ..)
include hβ
lemma spec_r : expect S R (W x) (rave S β t R L x) = buoy (PPress S β t R) x L/PPress S β t R x :=by
    have he(U:Q): buoy (V U) x L=railV S β t R U x*Z! U:=by unfold rave; rw [mul_comm,div_mul_cancel₀ _ (wealth β t hc R τ A B C D hR hs U x|>.ne')]
    unfold Bulk.expect; rw [show buoy _ _ _= _ from erection β t x hc R τ A B C D hR (L.map Uniform.bolt)]; let z:=nut S β G
    have hp: (∫ U,roc (V U) (L.map Uniform.bolt) x ∂H) = z*S.push R.beta ((Z!)* R.eval) (W x):=by unfold StepData.push; rw [← integral_const_mul]; apply integral_congr_ae; filter_upwards with i; change buoy (V i) x L = z*_ ; rw [he, blend β t hc R τ A B C D hR]; rw [←hβ]; change (nut S β G * _)* _= z*(S.density β _ _ * (Z! i*R.eval i)); unfold z; ring -- parameters
    rw [hp,prec β t x hc R τ A B C D hR hs, ← hβ]; unfold z; rw [mul_div_mul_left _ _ (nut_pos ..|>.ne')]
end YM.MSbar.Tonic
