import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Inc
/-!
# Shares for Taylor in an actual short action

Interpolate the **exponent**, not the Mayer function `exp y - 1`. The LHS
of a Taylor comparison will retain the complete interacting theory. At one
step keep the cutoffs, conditional reference, and the input parameters fixed,
and expand (in depth of action perturbation) on each nonexceptional log
leaf. This includes arbitrary positive powers of even a single remaining
head. Here prepare the real-variable multiplier used to perform this expansion
with the project's angular budget. Not Taylor in the coarse coupling/reset and
not an identification of the terms with the independently prescribed PT system.

Formula below uses a C∞ bump *outside* the domain used in the expansion. This
way the Taylor coefficients have support-preserving global extensions when
read on a head. We'll verify (on the physical admissible domain used below)
that these extensions really give the exponent powers, not clipped values. In
the sum 0..M with one error slot at M+1 there is no replacement of any step
by a cutoff approximation without keeping its remainder.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsLocal.ExpShares
open Filter Function Finset Set NormedSpace
open scoped Topology BigOperators Classical ContDiff
-- No Mathlib.exp ambiguity

private def rawLogRatio := dslope (fun s => Real.log (1+s)) (0:ℝ)
private def guard : ContDiffBump (0:ℝ) := ⟨2/3,3/4,by norm_num,by norm_num⟩
def logRatio (x:ℝ) := guard x * rawLogRatio x

private lemma raw_analytic {x:ℝ} (hx : -1 < x) : AnalyticAt ℝ rawLogRatio x := by
  let f y:=Real.log (1+y)
  have hf : AnalyticAt ℝ f x := (analyticAt_const.add analyticAt_id).log (by linarith : 0<1+x)
  by_cases h : x=0
  · subst x; obtain ⟨p,hp⟩:=hf; exact ⟨p.fslope,hp.has_fpower_series_dslope_fslope⟩
  have he : AnalyticAt ℝ (fun y:ℝ=>(y-0)⁻¹*(f y-f 0)) x := ((analyticAt_id.sub analyticAt_const).inv (by simpa using h)).mul (hf.sub analyticAt_const)
  exact he.congr (dslope_eventuallyEq_slope_of_ne f h).symm

lemma logRatio_contDiff (j:ℕ) : ContDiff ℝ (↑j) logRatio := by
  apply contDiff_iff_contDiffAt.mpr
  intro x; by_cases h : -1 < x
  · exact guard.contDiffAt.mul (raw_analytic h).contDiffAt
  have h₁ : x∉ tsupport guard := by
    rw [guard.tsupport_eq, Metric.mem_closedBall]; change ¬ dist x 0 ≤ (3/4:ℝ)
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonpos (by linarith)]; linarith
  refine (contDiffAt_const (c:= (0:ℝ))).congr_of_eventuallyEq ?_
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp h₁] with y hy
  rw [logRatio,hy]; simp


lemma logRatio_open {x:ℝ}(hx : |x| ≤ 2/3) : x * logRatio x=Real.log (1+x) := by
  unfold logRatio
  rw [guard.one_of_mem_closedBall (Metric.mem_closedBall.mpr (by rwa [dist_zero_right])), one_mul]
  simpa [rawLogRatio] using (sub_smul_dslope (fun s=> Real.log (1+s)) 0 x)

def keep : ℕ → ℝ→ℝ
  | 0, _ => 0
  | n+1, x=> x^n*logRatio x^(n+1)/(n+1).factorial

def spill (M:ℕ) (x:ℝ) := 1-∑ n∈range (M+1), keep n x

def share (M n:ℕ) (x:ℝ) := if n=M+1 then spill M x else keep n x

lemma open_keep {s y:ℝ} (he:s=Real.exp y-1)(hs:|s|≤2/3)(n:ℕ) :
    s*keep (n+1) s=y^(n+1)/(n+1).factorial := by
  have h : s* logRatio s=y:= by rw [logRatio_open hs,he,add_sub_cancel,Real.log_exp]
  unfold keep; nth_rw 1 [← h]; ring

lemma share_contDiff (j M n:ℕ) : ContDiff ℝ (↑j) (share M n) := by
  have h (n:ℕ) : ContDiff ℝ (↑j) (keep n) := by
    cases n
    · exact contDiff_const
    exact ((contDiff_id.pow _).mul ((logRatio_contDiff j).pow _)).div_const _
  unfold share; split
  · exact contDiff_const.sub (ContDiff.sum (fun i (_:i∈Finset.range (M+1))=> h i))
  exact h n

lemma shares_literal (M:ℕ)(x:ℝ) : ∑ n:Fin (M+2), share M n x =1 := by
  rw [Fin.sum_univ_castSucc]
  have h (n:Fin (M+1)): share M n.castSucc.val x=keep n.val x:=if_neg (Nat.ne_of_lt n.isLt)
  simp_rw [h]; rw [Fin.val_last,share,if_pos rfl]
  rw [spill, Fin.sum_univ_eq_sum_range (fun n=>keep n x)]; ring

-- An honest high-order error slot (no loss per derivative). Get the
-- factor from the analytic exponential series by divided slopes.
private def scaledTail (M:ℕ) := (swap dslope 0)^[M] Real.exp
private lemma scaled_succ (M:ℕ) : scaledTail (M+1)=dslope (scaledTail M) 0 :=
  Function.iterate_succ_apply' ..
private theorem scaled_zeroSeries (M:ℕ) : HasFPowerSeriesAt (scaledTail M) (FormalMultilinearSeries.fslope^[M] (expSeries ℝ ℝ)) 0 := by
  unfold scaledTail; rw [Real.exp_eq_exp_ℝ]
  exact (NormedSpace.hasFPowerSeriesAt_exp_zero_of_radius_pos (NormedSpace.expSeries_radius_pos ℝ ℝ)).has_fpower_series_iterate_dslope_fslope M
private lemma scaled_value_zero (M:ℕ) : scaledTail M 0=(M.factorial:ℝ)⁻¹ := by
  have h:= (scaled_zeroSeries M).coeff_zero 1
  rw [← h, ← FormalMultilinearSeries.coeff, FormalMultilinearSeries.coeff_iterate_fslope,zero_add]
  change (expSeries ℝ ℝ M fun _=>1) = _
  rw [expSeries_apply_eq]; simp
private lemma scaled_analytic (M:ℕ)(x:ℝ) : AnalyticAt ℝ (scaledTail M) x := by
  by_cases h:x=0
  · subst x; exact ⟨_, scaled_zeroSeries _⟩
  induction M with
  | zero => exact analyticAt_rexp
  | succ n ih =>
    let g:=scaledTail n
    have he : AnalyticAt ℝ (fun y:ℝ=>(y-0)⁻¹*(g y-g 0)) x := ((analyticAt_id.sub analyticAt_const).inv (by simpa using h)).mul (ih.sub analyticAt_const)
    rw [scaled_succ]
    exact he.congr (dslope_eventuallyEq_slope_of_ne g h).symm

def spillFactor (M:ℕ)(x:ℝ) := logRatio x^(M+1) * scaledTail (M+1) (x*logRatio x)

lemma spill_open (M:ℕ) {x:ℝ} (hx:|x|<2/3) : spill M x=x^M*spillFactor M x := by
  suffices he : ∀ (x:ℝ), |x|<2/3→ x≠0→ spill M x=x^M*spillFactor M x by
    by_cases h:x=0
    · subst x
      have hi : ContinuousAt (spill M) 0:= by
        have hv:share M (M+1)=spill M := funext fun x=> if_pos rfl
        rw [← hv]; exact (share_contDiff 0 ..).continuous.continuousAt
      have hj : ContinuousAt (fun x=> x^M*spillFactor M x) 0 := by
        refine (continuousAt_id.pow _).mul (((logRatio_contDiff 0).continuous.continuousAt.pow _).mul ?_)
        exact (((scaled_analytic _ _).continuousAt).comp (continuousAt_id.mul (logRatio_contDiff 0).continuous.continuousAt))
      apply tendsto_nhds_unique (hi.continuousWithinAt (s:={(0:ℝ)}ᶜ))
      refine (show Tendsto _ (𝓝[≠] (0:ℝ)) (𝓝 _) from hj.continuousWithinAt).congr' ?_
      filter_upwards [self_mem_nhdsWithin,(show ContinuousAt abs (0:ℝ) from continuous_abs.continuousAt).continuousWithinAt.eventually (gt_mem_nhds hx)] with y hy hh using (he y hh hy).symm
    exact he x hx h
  intro a hA ha
  let y:=a*logRatio a; have hY:Real.exp y=1+a:= by unfold y; rw [logRatio_open hA.le]; exact Real.exp_log (by have h:= abs_lt.mp hA; linarith)
  induction M with
  | zero =>
    simp only [spill,spillFactor, keep, sum_range_one, sub_zero,pow_zero,one_mul, zero_add,pow_one]; apply mul_left_cancel₀ ha
    have h:=sub_smul_dslope Real.exp 0 y
    change (y-(0:ℝ))*scaledTail 1 y= _ at h
    rw [Real.exp_zero,hY,sub_zero] at h
    calc
      _= y*scaledTail 1 y := by linarith only [h]
      _ = _ := by unfold y; ring
  | succ n ih =>
    have hp:= sub_smul_dslope (scaledTail (n+1)) 0 y; simp only [← scaled_succ, sub_zero,smul_eq_mul,scaled_value_zero] at hp
    rw [show spill (n+1) a=spill n a-keep (n+1) a by unfold spill; rw [sum_range_succ]; ring, ih]
    dsimp only [keep, spillFactor]; change a^n * (_*scaledTail _ y)-_ = a^(n+1)*(_ * scaledTail _ y)
    rw [show scaledTail (n+1) y=y*scaledTail (n+1+1) y+(↑(n+1).factorial : ℝ)⁻¹ by rw [hp,sub_add_cancel]]
    unfold y; ring

def keepFactor : ℕ→ℝ→ℝ
  | 0, _=>0
  | n+1,x=>logRatio x^(n+1)/(n+1).factorial

def factor (M n:ℕ) := if n=M+1 then spillFactor M else keepFactor n

lemma factor_contDiff (j M n : ℕ) : ContDiff ℝ (↑j) (factor M n) := by
  unfold factor; split
  · apply contDiff_iff_contDiffAt.mpr
    intro x; exact (((logRatio_contDiff j).contDiffAt.pow _).mul (((scaled_analytic _ _).contDiffAt).comp x (contDiffAt_id.mul (logRatio_contDiff j).contDiffAt)))
  cases n
  · exact contDiff_const
  exact ((logRatio_contDiff j).pow _).div_const _

lemma share_open (M n:ℕ) {x:ℝ}(hx:|x|<2/3) : share M n x=x^(n-1)*factor M n x := by
  unfold share factor; split
  next h=> subst n; simpa only [Nat.add_sub_cancel] using spill_open M hx
  next h=>
    cases n
    · simp only [keep, keepFactor,mul_zero]
    unfold keep keepFactor; simp only [Nat.add_sub_cancel,mul_div_assoc]

open ConnectedActivityE6.Blaze

private lemma brush_pow {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f:E→ℝ} {x:E} {w:ℝ} {j:ℕ} (h:Brush j w 1 f x) (n:ℕ) : Brush j (w^n) n (fun i=> f i^n) x := by
  induction n with
  | zero => simpa using! (Brush.certified (k:=j) (x:=x) (le_refl (0:ℝ)) (1:ℝ))
  | succ n ih => simpa only [pow_succ,Nat.cast_succ] using! ih.paints h

/-- No loss per derivative; finite constant common across assignments on a step. -/
lemma prices (j M k:ℕ) : ∃ C:ℝ, 1≤ C ∧ ∀ (ρ : ℝ), 2≤ ρ →
    ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (f:E→ℝ) (x:E),
    Brush j ρ⁻¹ 1 f x → Brush j (C* (ρ⁻¹)^(k-1)) 1 (fun i=>share M k (f i)) x := by
  obtain ⟨v,hv,h⟩:= Brush.compact (k:=j) (f:=factor M k) (s:=Set.Icc (-1:ℝ) 1) isCompact_Icc (fun i _=> (factor_contDiff j M k).contDiffAt)
  let u:ℝ:= j.factorial*v * (1+((k-1:ℕ):ℝ)+2)^j
  have hu : 0<u:= by unfold u; positivity
  refine ⟨1+u,by linarith,fun ρ hρ E _ _ f x he=>?_⟩
  have hp:(ρ⁻¹:ℝ) ≤ 1/2 := by rw [one_div]; exact inv_anti₀ (by norm_num) hρ
  have h₀ : |f x| ≤ 1/2:= he.bound.trans hp
  have h₁ : f x∈ Icc (-1:ℝ) 1:= abs_le.mp (h₀.trans (by norm_num))
  have he' := he.pine (h _ h₁)
  apply Brush.shimmy (f:=fun i=> f i ^ (k-1) * factor M k (f i))
  · apply ((brush_pow he (k-1)).paints (he'.climb le_rfl (show (1+ρ⁻¹)*1≤2 by linarith))).trim.climb _ le_rfl
    let w:=(ρ⁻¹)^(k-1); have hw:0≤w:=by unfold w; positivity
    change (w*_)*_ ≤ _
    rw [show w*(j.factorial*v)*(1+(((k-1:ℕ):ℝ)+2))^j=w*u by unfold u; ring]
    change _ ≤ (1+u)*w
    rw [mul_comm w u]; nlinarith only [hw]
  filter_upwards [(he.smooth.continuousAt.abs).eventually (gt_mem_nhds (h₀.trans_lt (show (1/2:ℝ)<2/3 by norm_num)))] with i hi using share_open M k hi

lemma universal_price_spec (j M:ℕ) : ∃ C:ℝ, 1≤ C ∧ ∀ (k:Fin (M+2)), ∀ (ρ : ℝ), 2≤ ρ →
    ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (f:E→ℝ) (x:E),
    Brush j ρ⁻¹ 1 f x → Brush j (C* (ρ⁻¹)^(k.val-1)) 1 (fun i=>share M k (f i)) x := by
  choose C hC h using fun k:Fin (M+2)=>prices j M k.val
  refine ⟨1+∑ k,C k,le_add_of_nonneg_right (sum_nonneg fun k _=>zero_le_one.trans (hC k)),?_⟩
  intro k ρ hρ E _ _ f x he
  refine (h k ρ hρ E f x he).climb ?_ le_rfl
  exact mul_le_mul_of_nonneg_right ((single_le_sum (fun i _=>zero_le_one.trans (hC i)) (mem_univ k)).trans (le_add_of_nonneg_left zero_le_one)) (by positivity)

/-- Chosen entirely before ratios. -/
def overhead (j M:ℕ) : ℝ := (universal_price_spec j M).choose
lemma overhead_bound (j M:ℕ) : 1≤overhead j M := (universal_price_spec j M).choose_spec.1
lemma brush_share {j M:ℕ} {ρ:ℝ} (hp:2≤ρ) (k:Fin (M+2)) {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f:E→ℝ} {x:E}
    (h : Brush j ρ⁻¹ 1 f x) : Brush j (overhead j M* (ρ⁻¹)^(k.val-1)) 1 (fun i=>share M k (f i)) x :=
  (universal_price_spec j M).choose_spec.2 k ρ hp E f x h
end YM.GapsLocal.ExpShares
