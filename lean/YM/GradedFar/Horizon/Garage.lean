import YM.GradedFar.Horizon.Advance

/-!
# Dyadic steps for uniform *fixed grade* payments vs `log(1/r)`
-/
namespace YM.FVA2.GradedFar.Horizon
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus XSpace.Rose
open O O.Score O.Enh O.Canon Scale Dframe Jury Facets Growth Pose Moving
open MS.Book.Program
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {I : Type} {f : ℝ→ℝ} {C : ℝ}
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
variable (simple : G.Simple)

-- need accept Continuum canon logs (1+log(1/r)) eventual each.
abbrev degrees (r : ℝ) := Real.log r⁻¹
lemma at_log : Tendsto (fun i:ℝ=> exp (-i)) atTop τ := by
  exact tendsto_nhdsWithin_iff.mpr ⟨ tendsto_exp_atBot.comp tendsto_neg_atTop_atBot,Eventually.of_forall fun i=> exp_pos _⟩
lemma departing : Tendsto degrees τ atTop := Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
lemma later (t u : ℝ) : exp (-(u+t))*exp t=exp (-u) := by rw [← exp_add]; ring_nf
@[simp] lemma degrees_exp (u : ℝ) : degrees (exp (-u)) = u:= by rw [degrees,Real.log_inv,log_exp,neg_neg]
lemma expr {r : ℝ} (h : 0 < r) : exp (-(degrees r))=r:= by rw [degrees,Real.log_inv,neg_neg,Real.exp_log h]
include simple
lemma prepaid {t : ℝ} (ht : 0<t) : g (exp (-t))^2=(G.slopeConstant*t)⁻¹ := by
    change (√(G.slopeConstant*degrees _))⁻¹^2=_; rw [degrees_exp,inv_pow,Real.sq_sqrt (mul_nonneg (Gauge.slopeConstant_pos simple).le ht.le)]
private lemma charged (hc : 0<C)
    (hr : ∀ᶠ r in τ, ∀ s∈ Growth.Small, f r ≤ (1+C*g r^2) * f (resize r s)) :
    ∃ (x k : ℝ), 0<x ∧ 0<k ∧ ∀ t≥x, ∀ s∈Growth.Small,
      f (exp (-(t+s))) ≤ (1+k / (t+s))* f (exp (-t)) := by
    obtain ⟨t,h⟩:=eventually_atTop.mp (at_log.eventually hr); let k:= C / G.slopeConstant; have hp:= Gauge.slopeConstant_pos simple
    refine ⟨max t 1,k,lt_max_of_lt_right zero_lt_one,div_pos hc hp,?_⟩
    intro x hx s hs; have hx':= (le_max_right t 1).trans hx; have hs0:= hs.1
    have ho : 0<x+s:=by linarith
    have he:= h (x+s) (show t ≤ x+s from ((le_max_left ..).trans hx).trans (le_add_of_nonneg_right hs0)) s hs
    change _ ≤ (1+ _)*_ at he; rw [resize, later, prepaid simple ho] at he
    convert he using 1; unfold k; rw [mul_inv_rev]; ring -- inv product ring

-- prove numeric recurrence via invariant n=number full doubling, exponent K integer picks Bernoulli slope bigger than k. pays no exponential radius risk!
set_option linter.unusedSectionVars false in
private lemma step_exp (t k : ℝ) (ht : 0<t) (hk : 0 < k) (n : ℕ) (hn : k ≤ doubling * n) :
    (1+k/(t+doubling))*t^n ≤ (t+doubling)^n := by
  have hd:=doubling_pos
  have he : 1+k/(t+doubling) ≤ (1+doubling/t)^n := by
    calc
      _ ≤ 1 + n*(doubling/t) := add_le_add_right (le_trans
        (div_le_div_of_nonneg_left hk.le ht (le_add_of_nonneg_right hd.le))
        ((div_le_div_of_nonneg_right hn ht.le).trans_eq (by ring))) _ -- addition
      _ ≤ _ := one_add_mul_le_pow (show -2≤doubling/t from (by linarith [div_pos hd ht])) n
  calc
    _ ≤ (1+doubling/t)^n*t^n := mul_le_mul_of_nonneg_right he (by positivity)
    _ = _ := by rw [← mul_pow, show (1+doubling/t)*t=t+doubling from (by field_simp)]

/-- This recurrence lets polynomial relative expenses be paid *without continuity*
on the family of frames. In terms of Warm measure clocks. For all further radii.
-/
theorem advances (h : ∀ r:ℝ,0≤ f r) (hc : 0<C)
    (hv : ∀ᶠ r in τ, ∀ s∈ Growth.Small, f r ≤ (1+C*g r^2)*f (resize r s)) :
    ∃ k:ℕ,∃ d:ℝ,0<d ∧ ∀ᶠ r in τ,f r ≤ d*(1+degrees r)^k := by
  obtain ⟨x,c,hx,hc',ht⟩:= charged simple hc hv
  let q i:= f (exp (-i))
  let t (n:ℕ):= x+n*doubling
  have hd:=doubling_pos
  obtain ⟨k,hk⟩:= exists_nat_ge (c/doubling)
  have hk':= (div_le_iff₀ hd).1 hk
  rw [mul_comm] at hk'
  have tt (n : ℕ): x≤t n:= by unfold t; exact le_add_of_nonneg_right (by positivity)
  have t0 n:=hx.trans_le (tt n)
  let A:=1+q x/x^k; have hp : 0<A:= by apply add_pos_of_pos_of_nonneg zero_lt_one; exact div_nonneg (h _) (by positivity)
  have he (n : ℕ): q (t n) ≤ A*(t n)^k := by
      induction n with
      | zero=> simp only [t,Nat.cast_zero,zero_mul,add_zero]; unfold A; rw [add_mul,one_mul,div_mul_cancel₀ _ (by positivity)]; linarith [pow_pos hx k]
      | succ n ih=>
        have he:t (n+1)=t n+doubling := by unfold t; push_cast; ring
        rw [he]; calc
          _ ≤ _ := ht (t n) (tt n) doubling ⟨hd.le,le_rfl⟩
          _ ≤ (1+c/(t n+doubling))*(A*(t n)^k) := mul_le_mul_of_nonneg_left ih (by have hh:= t0 n; positivity)
          _ ≤ _ := by rw [mul_left_comm]; apply mul_le_mul_of_nonneg_left _ hp.le; exact step_exp simple _ _ (t0 n) hc' k hk'
  refine ⟨k,(1+c/x)*A,by positivity,?_⟩; filter_upwards [departing.eventually_ge_atTop x,self_mem_nhdsWithin] with r hr (hr':r∈Ioi 0)
  let s:= degrees r; let n : ℕ:= ⌊(s-x)/doubling⌋₊
  have h0 : 0 ≤ s-x := sub_nonneg.mpr hr
  have lo:t n≤ s:= by unfold t; have := (le_div_iff₀ hd).1 (Nat.floor_le (a:=(s-x)/doubling) (by positivity)); change _ ≤ _; linarith
  have up:s≤ t n+doubling:= by
    have h : (s-x)/doubling<n+1:=Nat.lt_floor_add_one _; unfold t; linarith [(div_lt_iff₀ hd).1 h]
  let a:=s-t n; have hv : t n+a=s:= by unfold a; ring
  have ht' := ht (t n) (tt n) a (show a∈Growth.Small from ⟨sub_nonneg.mpr lo,by unfold a; linarith only [up]⟩); rw [hv,expr hr'] at ht'; apply ht'.trans
  refine le_trans (mul_le_mul (show 1+c/s ≤ 1+c/x from (by gcongr)) (he n) (h _) (by positivity)) ?_
  rw [mul_assoc]; gcongr
  exact lo.trans (le_add_of_nonneg_left zero_le_one)
end
end YM.FVA2.GradedFar.Horizon
