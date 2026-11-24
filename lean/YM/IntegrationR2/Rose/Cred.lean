import YM.IntegrationR2.Rose.Dry
import YM.IntegrationR2.Purchase
/-! Single AFTER L payout. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonStartup.Rose
open Function Filter RG Wilson Lattice Design Work Ac Padded Start
open scoped ContDiff Topology Matrix.Norms.Frobenius Classical
open Ovens Ovens.Pipes Quad.Rose Progress.DirectedRecipe Rack
open YM.FullVolume.Urns PhysicalNext.Repeat Set
variable {G : Gauge}{n:Side}{b:BudgetPoint}{θ:ℕ}{v w β a ε:ℝ}{c:Clip}{W:PathData G}
open Timing
open Real (exp log)
-- δtop . leakage small relative allowance when grade≥5. K even allowance priced. Need explicitly purchase for all widths w, for choices before perturbative orders.
def tip (j:ℕ):ℝ:= (8:ℝ)⁻¹*(1+(j:ℝ))⁻¹
def amt (x:ℝ)(θ:ℕ)(μ:ℝ):ℝ:= x^(1-(θ:ℝ)/2+μ)
abbrev χ (x:ℝ) (j θ:ℕ):= amt x θ (tip j)
def υ (x:ℝ)(j:ℕ):ℝ:= (x^(j+1))⁻¹*normK (log x)
lemma available (j:ℕ): 0<tip j∧tip j ≤ 1/8:=by
    unfold tip; constructor; · positivity
    have h: (1+(j:ℝ))⁻¹ ≤ 1:=inv_le_one_of_one_le₀ (le_add_of_nonneg_right (Nat.cast_nonneg _)); norm_num at *; linarith
lemma feather {x y:ℝ} {j k :ℕ} (h:x≥1) (hp: j≤ k): amt x k y ≤ amt x j y:= by unfold amt; apply Real.rpow_le_rpow_of_exponent_le h; gcongr
lemma fit0 (η:ℝ) (hp:0<η) (M : Berry G θ) (A:Stage) : ∀ᶠ s:ℝ in atTop,∀ b: BudgetPoint, b.order=A.order → b.power=A.power → b.supportExponent=A.supportExponent → b.threshold=Timing.temp s →
    b.threshold ≤ threshold M b.order b.power ∧ ledger M b (2* exp s) ≤ amt (exp s) θ η:=by
    let C := (Fintype.card Signed:ℝ)*Fintype.card PlaqAxes*(exp (A.supportExponent*5^4)*(2*Rose.price M A.order A.power))
    have hC : 0<C:= by unfold C; have := (Rose.constants M A.order A.power).1; positivity
    let a := (θ:ℝ)
    have hz : 0 < a+1:= by unfold a; positivity
    filter_upwards [Timing.small (ε:=η/(a+1)) (by positivity), Timing.shrinking.eventually (ge_mem_nhds (constants M A.order A.power).2.1),eventually_ge_atTop (log C * (a+1)/η)] with s h hs hh b hk hP ha ht
    have hhX: ledger M b (2*exp s)= exp (log C+s+(θ:ℝ)*(-(s/2)+(log s)^2)):=by
       simp only [ledger,item,overhead,ha,hk,hP,ht,temp]
       rw [Real.exp_add (log C+s),Real.exp_add (log C),Real.exp_log hC, Real.exp_nat_mul]; unfold C; ring
    refine ⟨by rw [ht,hk,hP]; exact hs,?_⟩; rw [hhX,amt,←Real.exp_mul,Real.exp_le_exp]; have h':=mul_le_mul_of_nonneg_left h (show 0≤(θ:ℝ) from Nat.cast_nonneg _)
    let y:= Real.log C; have hy: y≤ s*η/(a+1):= (le_div_iff₀ hz).mpr ((div_le_iff₀ hp).mp hh); unfold y a at *
    calc _ ≤ s*η/((θ:ℝ)+1)+s+(θ:ℝ)*(-(s/2)+η/((θ:ℝ)+1)*s) := by linarith only [hy,h']
         _ = _ := by field_simp; ring
lemma fit_margin (j:ℕ):∀ᶠ x in atTop, χ x j 5≤ normE (log x)/16 ∧ υ x j≤ normK (log x)/8:=by
    have he: ∀ᶠ s:ℝ in atTop, s*((1-(5:ℝ)/2)+tip j)≤ -(11/10)*s-log 16:= by
         filter_upwards [eventually_ge_atTop (log 16*16), eventually_ge_atTop (0:ℝ)] with s hs hv; nlinarith [available j|>.2]
    filter_upwards [Real.tendsto_log_atTop.eventually he,eventually_ge_atTop (8:ℝ)] with x hx hv; have h:0<x:= by linarith
    refine ⟨by unfold χ amt normE; rw [Real.rpow_def_of_pos h,-- rep
      ← Real.exp_log (show (16:ℝ)>0 from (by norm_num)),← Real.exp_sub,Real.exp_le_exp]; norm_num; linarith,?_⟩
    unfold υ; rw [mul_comm, div_eq_mul_inv]; apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _); apply inv_anti₀ (by norm_num) _; exact hv.trans (le_self_pow₀ (by linarith) (by omega))
lemma fit_force (A: Stage)(j:ℕ):∀ᶠ s in atTop,∀ b:BudgetPoint,b.threshold= Timing.temp s → b.B=Timing.balls s → b.supportExponent=A.supportExponent →
    ∃ σ κ γ, Start.Loan b (exp s/2) σ κ γ ∧ Bid.quote κ (exp γ-1) ≤ υ (exp s) j:=by
    filter_upwards [Timing.loan A.supportExponent,Real.tendsto_log_atTop.eventually_ge_atTop 3, Timing.hard_growth 2,eventually_ge_atTop ((j:ℝ)+4),eventually_ge_atTop (1:ℝ)] with s he hh hs hx hy b ha hb hc
    obtain ⟨he,-⟩:= he b ha hb hc
    refine ⟨_,_,_,he,?_⟩; rw [υ,normK,Real.log_exp, ← Real.exp_nat_mul,← Real.exp_neg]; unfold Bid.quote
    apply (le_trans (b:=exp (-Timing.M s)*exp 1) (mul_le_mul_of_nonneg_left ((sub_le_self _ (by positivity)).trans (Real.exp_monotone (Tent.pill he))) (Real.exp_nonneg _))) _; rw [← Real.exp_add, ← Real.exp_add,Real.exp_le_exp]
    have ht : 2 ≤ exp (4/5*(log s)^2):=(show 2 ≤ 4/5*(log s)^2+1 from (by nlinarith)).trans (Real.add_one_le_exp _)
    have hp : 2*exp ((log s)^2/5)≤ Timing.M s:= (mul_le_mul_of_nonneg_right ht (Real.exp_nonneg _)).trans (show exp _*exp _ ≤ _ from (by unfold Timing.M; rw [← Real.exp_add, show ((4/5:ℝ)*_+_)= (log s)^2 from (by ring)]))
    push_cast; nlinarith
section season
variable (A: Levels G) (N:ℕ)
local notation "x"=> A.clock.hatBeta N
local notation "t"=> A.clock.J N
local notation "p"=> A.budget N
local notation "E"=> A.clock.allowance N
local notation "K"=> A.clock.forcedAllowance N
structure Income (A: Levels G)(N j:ℕ) :Prop where
    care (k:ℕ) : k ≤ j→ ∀ M : Berry G ((4+k)+1), M=jetTail G (4+k) ∨ M=jetRow G (4+k)→ (A.budget N).threshold ≤ threshold M (A.budget N).order (A.budget N).power ∧ ledger M (A.budget N) (2*A.clock.hatBeta N) ≤ χ (A.clock.hatBeta N) j ((4+k)+1)
    shelter: χ (A.clock.hatBeta N) j 5 ≤ A.clock.allowance N /16
    expects: ∃ σ κ γ,Start.Loan (A.budget N) (A.clock.hatBeta N/2) σ κ γ ∧ Bid.quote κ (exp γ-1) ≤ υ (A.clock.hatBeta N) j
    margin : υ (A.clock.hatBeta N) j ≤ A.clock.forcedAllowance N /8
def Standing (A:Levels G):Prop:= ∀ N, Income A N (A.clock.J N)
lemma holds (B:Stage)(j:ℕ): ∀ᶠ y in atTop,∀ (A:Levels G)(N:ℕ), A.params N=B → A.clock.hatBeta N=y → Income A N j :=by
    have h₀(k: Fin (j+1)):= ((fit0 (tip j) (available j).1 (jetTail G (4+k.val)) B).and (fit0 (tip j) (available j).1 (jetRow G (4+k.val)) B)); filter_upwards [Real.tendsto_log_atTop.eventually (eventually_all.mpr h₀), Real.tendsto_log_atTop.eventually (fit_force B j),fit_margin j,eventually_gt_atTop (1:ℝ)] with y h h₁ h₂ h₃ A' N' he hY
    let b:= A'.budget N'
    have hy:0<y:= by linarith
    have hb : b.B=balls (log y) := congr_arg balls (congr_arg log hY)
    have hp : (Real.sqrt y)⁻¹ = exp (-(log y / 2)) := by
        rw [Real.exp_neg,Real.sqrt_eq_rpow,Real.rpow_def_of_pos hy]; congr 2; ring
    have ht : b.threshold = temp (log y) := by
        change (Real.sqrt (A'.clock.hatBeta N'))⁻¹ * exp _ = _
        unfold temp; rw [hY,hp,Real.exp_add]
    have hf : A'.clock.allowance N' = normE (log y) := by
       unfold Calendar.allowance Calendar.hatCoupling normE; rw [hY,hp,← Real.exp_mul]; congr 1; ring
    have hw : A'.clock.forcedAllowance N' = normK (log y) := by
       unfold Calendar.forcedAllowance Calendar.monitor normK; rw [hY,← Real.exp_mul]; congr 3; ring
    have hk : b.order=B.order := congr_arg Stage.order he
    have hP : b.power=B.power := congr_arg Stage.power he; have hE : b.supportExponent=B.supportExponent := congr_arg Stage.supportExponent he
    refine ⟨?_,by rw [hY,hf]; exact h₂.1,?_, by rw [hY,hw]; exact h₂.2⟩
    · rintro k hv M (rfl|rfl) <;> let i:Fin (j+1):= ⟨k,by omega⟩
      · have hx:= (h i).1 b hk hP hE ht; rw [Real.exp_log hy] at hx; rw [hY]; exact hx
      have hx:= (h i).2 b hk hP hE ht; rw [Real.exp_log hy] at hx; rw [hY]; exact hx
    obtain ⟨σ,κ,γ,h₁,hh⟩:= h₁ b ht hb hE; rw [Real.exp_log hy] at h₁ hh; rw [hY]; exact ⟨σ,κ,γ,h₁,hh⟩
open Push PriceCompiler RG.Supply Legato
lemma earned : DelayCharged (Standing (G:=G)):= by
    intro S R Y U; obtain ⟨y,ht,hx,H⟩:= collect_upper U.betaEntry _ fun j=> holds (G:=G) (S.profile j) j
    refine ⟨{U with betaEntry:=y}, ⟨hx,le_rfl,le_rfl,le_rfl⟩,fun W h _ D K' hp N' => H (K'.clock.J N') (K'.clock.hatBeta N') ((h.beta _).trans ?_) _ _ (params_eq hp _) rfl⟩
    cases N' with
    | zero=> rw [hp.firstZero,← hp.firstOne]; exact hp.pays _
    | succ N'=> exact (hp.pays N').trans ((le_add_of_nonneg_right (Work.E04.shift_nonneg G _)).trans_eq (PriceCompiler.beta_eq hp N').symm)
-- fee relationship physical coupling
lemma bounds (H : Standing A)(l:ℕ)(hl:l≤ A.clock.J N) (β: RG.Shoot.band A N)(M: Berry G (4+l+1))(he:M=jetTail G (4+l)∨M=jetRow G (4+l))(n:Side)(ha:(A.params N).clip.direct≤1):
    (payload M n (A.params N).clip β).EBound (A.budget N) (χ (A.clock.hatBeta N) (A.clock.J N) (4+l+1)) := by
    let h:= (H N).care l hl _ he
    refine ink M h.1 ha ?_ h.2; obtain ⟨ht,hp⟩:=β.property; rw [Real.norm_of_nonneg (((div_pos (by linarith [A.fits.delayed N]) zero_lt_two).le.trans ht):0≤β.val)]; exact hp
end season
end YM.WilsonStartup.Rose
