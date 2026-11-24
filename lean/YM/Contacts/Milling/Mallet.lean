import YM.Contacts.Milling.Roller
import YM.Next.STATIONARY.Infrastructure.Jets
import YM.PertExtension.Aspiration
namespace YM.Contacts.Milling
open Function Set Filter Metric MeasureTheory Asymptotics
open Finset PertExtension.Series PertExtension.GaussianScore Pulse Pulse.Form MvPolynomial Radial YM.Stationary
open scoped Topology BigOperators ContDiff Classical
noncomputable section
variable {V E : Type}[NormedAddCommGroup V][NormedSpace ℝ V][FiniteDimensional ℝ V][NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] {m n:ℕ}
section mortar
variable {f g:E→ℝ} (h:AnalyticAt ℝ f 0)
include h
lemma jet_bridge : Rays n f ↔∀ v:E,∀ k<n, jet f k v=0:= by
  let h0:= h.contDiffAt (n:=ω); rw [rays_jet h]; constructor
  · intro p x k hk; rw [jet,p k hk]; simp
  intro p k hk; apply Tensor.ext_diag _ _ h0.iteratedFDeriv_comp_perm (fun _ _=> rfl) (funext (fun x=>?_)); exact (mul_eq_zero.mp (p x k hk)).resolve_left (inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero _))
lemma jet_prefix : f =O[𝓝 0] (fun x=> ‖x‖^n) ↔ Rays n f:= by
  constructor
  · intro hf v; apply ((hf.comp_tendsto (along v)).trans (isBigO_of_le' (c:=‖v‖^n) _ ?_)); intro x; simp only [comp_apply,norm_smul,norm_pow]; rw [Real.norm_of_nonneg (by positivity),mul_pow,mul_comm]
  intro hf; obtain ⟨P,hP⟩:=h; have hh x k (hk:k<n) : Tensor.diagonal (P k) x=0:= (rays_one hP n x).1 (hf x) k hk
  have ht x : P.partialSum n x=0 := sum_eq_zero (fun i hi=> hh x i (mem_range.mp hi)); simpa only [zero_add, ht,sub_zero] using hP.isBigO_sub_partialSum_pow n
lemma serif (r: E→ℝ) (hr:AnalyticAt ℝ r 0) (n:ℕ)(x:E): jet (f+r) n x=jet f n x+jet r n x := by simp only [jet,iteratedFDeriv_add_apply h.contDiffAt hr.contDiffAt,ContinuousMultilinearMap.add_apply,mul_add]
lemma leaf (i:ℕ)(x:E): Tested.Bill (i+1) (fun t:ℝ=>f (t• x)-Zone.eval (jet f) i t x):= by
  obtain ⟨δ,C,hδ,hC,H⟩:= deposition f i h.contDiffAt
  refine ⟨C* ‖x‖^(i+1),by positivity,?_⟩; filter_upwards [Tested.eventually_pos, Tested.eventually_top (show 0<δ/(‖x‖+1) by positivity)] with t ht he; exact H _ _ ht (by nlinarith [(lt_div_iff₀ (by positivity:0< ‖x‖+1)).1 he])
lemma marker {x:E} (i:ℕ)(hF : Tested.Bill i (fun t:ℝ=>f (t•x))): ∀ k < i, jet f k x=0:=by
  induction i with
  | zero=> simp
  | succ k ih=>
    have hc := ih (Tested.bill_ge hF (Nat.le_succ _)); intro j hj; rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hj) with h|h
    -- hc shadow
    · subst j; obtain ⟨δ,c,hb⟩ : Tested.Bill (k+1) (fun t:ℝ=> Zone.eval (jet f) k t x):= by
         obtain ⟨C,hC,H⟩ := Tested.bill_add hF (Tested.bill_neg (leaf (by assumption) k x)); refine ⟨C,hC,H.mono fun i hi=>?_⟩; simpa [sub_eq_add_neg] using hi
      have he (t:ℝ): Zone.eval (jet f) k t x=t^k*jet f k x:= by rw [Zone.eval,sum_range_succ,Finset.sum_eq_zero,zero_add]; rfl; intro i hi; rw [hc i (mem_range.mp hi)]; simp
      by_contra H
      let ε:= ‖jet f k x‖; have hε: 0<ε:=norm_pos_iff.mpr H; obtain ⟨y,hy,hg,hf⟩:= (hb.and (Tested.eventually_pos.and (Tested.eventually_top (show 0<ε/(δ+1) by positivity)))).exists
      dsimp only at hy; rw [he,norm_mul, Real.norm_of_nonneg (pow_nonneg hg.le k),pow_succ] at hy; have hr := (lt_div_iff₀ (by positivity : 0<δ+1)).1 hf; change y*(δ+1)<‖jet f k x‖ at hr; nlinarith only [hy,mul_lt_mul_of_pos_left hr (pow_pos hg k),mul_pos (pow_pos hg k) hg] -- multiply
    exact hc _ h
lemma merkin (hF: Rays n f) (u:V→ E) (hu:AnalyticAt ℝ u 0)(hq:u 0=0): Rays n (f ∘ u):= by
  have hv : AnalyticAt ℝ f (u 0):=by rw [hq]; exact h
  apply (jet_prefix (hv.comp hu)).1; have he:= hu.continuousAt.tendsto; rw [hq] at he; apply ((jet_prefix h).2 hF|>.comp_tendsto he).trans; have hO:= hu.differentiableAt.isBigO_sub; simp only [hq,sub_zero] at hO; exact (hO.norm_norm).pow _
omit h in
lemma jet_serif {r:Fin m→ E→ℝ} (x:E)(hi:∀ i,AnalyticAt ℝ (r i) 0)(n:ℕ): jet (∑ i,r i) n x = ∑ i,jet (r i) n x:= by unfold jet; rw [iteratedFDeriv_sum_apply ?_,ContinuousMultilinearMap.sum_apply,mul_sum]; exact fun i _=> (hi i).contDiffAt
lemma radiant (n:ℕ)(j:ℕ) (hF:∀ x t,f (t• x)=(t:ℝ)^n*f x)(x:E) : jet f j x=if j=n then f x else 0 := by
  rw [homogeneous_derivative f x j h.contDiffAt,funext (hF x)]; rw [show (fun t:ℝ=>t^n*f x)=(fun t:ℝ=>t^n • f x) from rfl, iteratedDeriv_smul_const (f:=fun t:ℝ=>t^n) ?_, iteratedDeriv_fun_pow_zero]; split <;> simp_all [smul_eq_mul]; all_goals first | field_simp | fun_prop
end mortar
end
end YM.Contacts.Milling
noncomputable section
namespace YM.Contacts.Milling
open Function Set Filter Metric MeasureTheory Asymptotics
open Finset PertExtension.Series PertExtension.GaussianScore Pulse Pulse.Form MvPolynomial Radial YM.Stationary
open scoped Topology BigOperators ContDiff Classical
variable {V E : Type}[NormedAddCommGroup V][NormedSpace ℝ V][FiniteDimensional ℝ V][NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]{n m:ℕ}
variable {f g:E→ℝ}{x:E}
-- Exponent difference to pin same definition even under non-invariant coordinates and with lifted ζ powers.
def sample (f:E→ℝ)(x:E)(t:ℝ):= f (t•x)/t^2
lemma rays_cast (h:AnalyticAt ℝ f 0)(hp:Radial.Stationary f) : Rays 2 f:= (jet_bridge h).2 (fun x i hi=> by interval_cases i; simp [hp.base0]; apply hp.base1)
lemma limited (h:Rays 2 f)(x:E) : ∃ D>0, ∀ᶠ t in 𝓝[>] (0:ℝ), ‖sample f x t‖ ≤ D:= by
  obtain ⟨c,hc,H⟩:= (h x).exists_pos
  refine ⟨c,hc,?_⟩; filter_upwards [ H.bound.filter_mono (nhdsGT_le_nhdsNE 0),Tested.eventually_pos] with t hi ht; unfold sample; rw [norm_div, div_le_iff₀]; exact hi; exact norm_pos_iff.mpr (pow_ne_zero _ ht.ne')
lemma sample_cost (hF:Rays 2 f)(hG:Rays 2 g)(x:E)(n:ℕ)(h: Tested.Bill (n+1) (fun t=>Real.exp (-sample f x t)-Real.exp (-sample g x t))): Tested.Bill (n+3) (fun t=>(f-g) (t•x)):= by
  obtain ⟨k,hk,H⟩:=h; obtain ⟨d,hd,hA⟩:=limited hF x; obtain ⟨c,hc,hB⟩:=limited hG x
  let V:=Real.exp (d+c); have hv : 0<V:= Real.exp_pos _
  refine ⟨V*k,by positivity,?_⟩; filter_upwards [H,hA,hB,Tested.eventually_pos] with t h hx hy ht; set F:=-sample f x t; set G:=-sample g x t
  have he (A B:ℝ)(ha:‖A‖ ≤ d+c) (hb:‖B‖≤ d+c)(hp:A≤B) : B - A ≤ V*(Real.exp B-Real.exp A):= by
    have hu : V⁻¹ ≤ Real.exp A:= by unfold V; rw [← Real.exp_neg]; apply Real.exp_monotone; linarith only [neg_le_abs (a:=A), show |A|≤ d+c from ha]
    have hP:= Real.add_one_le_exp (B-A); rw [Real.exp_sub] at hP; have hl := (le_div_iff₀ (Real.exp_pos A)).mp hP; suffices ht:(B-A)*V⁻¹ ≤ Real.exp B - Real.exp A from by rw [mul_comm V]; exact (le_div_iff₀ (inv_pos.mpr hv)).mpr ht |>.trans_eq (by simp)
    exact (mul_le_mul_of_nonneg_left hu (by linarith : 0 ≤ B-A)).trans (by linarith)
  have hx :‖F‖≤d+c:= by unfold F; rw [norm_neg]; linarith
  have hy :‖G‖≤d+c:= by unfold G; rw [norm_neg]; linarith
  have hh: ‖F-G‖ ≤ V * (k*t^(n+1)):= by
    have hZ: |Real.exp F-Real.exp G|≤ k*t^(n+1):= h
    rcases le_total G F with h|h
    · rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr h)]; exact (he _ _ hy hx h).trans (mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hZ) hv.le)
    rw [norm_sub_rev, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr h)]; rw [abs_sub_comm] at hZ; exact (he _ _ hx hy h).trans (mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hZ) hv.le)
  have hy : ‖(f-g) (t • x)‖=‖F-G‖*t^2:= by
    rw [←Real.norm_of_nonneg (pow_nonneg ht.le 2),← norm_mul,show (F-G)*_ = -((f-g) (t•x)) from ?_, norm_neg]
    unfold F G sample; simp only [Pi.sub_apply]; field_simp; ring
  rw [hy]; exact (mul_le_mul_of_nonneg_right hh (sq_nonneg _)).trans_eq (by simp only [pow_succ]; ring)
lemma nightwalk (hF:AnalyticAt ℝ f 0) (hG : AnalyticAt ℝ g 0) (h: Rays n (f-g)) (k:ℕ)(hk:k<n)(x:E) : jet f k x= jet g k x:= by
    have he := (jet_bridge (hF.sub hG)).1 h x k hk; unfold jet at he ⊢; rw [iteratedFDeriv_sub_apply hF.contDiffAt hG.contDiffAt, _root_.sub_apply, mul_sub] at he; exact sub_eq_zero.mp he
lemma benchPitch {f:ℝ×V→ℝ}(h:AnalyticAt ℝ f 0)(H:∀ x:V,∀ k < n,jet f k (1,x)=0): Rays n f:= by
  refine (jet_bridge h).2 ?_; rintro ⟨x,y⟩ i hi; let P (x:ℝ):= jet f i (x,y); have hp : Continuous P := by letI:= borel (ℝ×V); exact (Smooth.continuousJet ..).comp (continuous_id.prodMk continuous_const)
  change P x=0; have ht (x:ℝ)(hx:x≠0): P x=0:= by
    unfold P; rw [show (x,y)=x• ((1:ℝ), x⁻¹ • y) from by ext1 <;> simp [hx, smul_smul], jet_smul,H _ _ hi,mul_zero]; -- ext?
  by_cases he:x=0; subst x; exact tendsto_nhds_unique_of_eventuallyEq (hp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) tendsto_const_nhds (Tested.eventually_pos.mono fun x hx=> ht x hx.ne'); exact ht x he
end YM.Contacts.Milling
