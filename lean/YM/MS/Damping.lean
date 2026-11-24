import YM.MS.Rapid
import YM.MS.SymbolParts
import YM.MS.LogTime

/-!
# Norm with rapid allowance factored exponentially (in the first zone)
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS
open Set Function Real Filter
open scoped Topology ContDiff
variable {ι E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {T : Cost ι E} {S : Scale ι} {D : ι→Set E}
section
variable {f f' g : Kern ι E ℝ}
private lemma exp_dist' {x y : ℝ} (h : y ≤ x) : ‖exp x-exp y‖ ≤ ‖x-y‖*exp x := by
   rw [Real.norm_of_nonneg (sub_nonneg.mpr (exp_monotone h)), Real.norm_of_nonneg (sub_nonneg.mpr h)]
   have H:= mul_le_mul_of_nonneg_left (Real.add_one_le_exp (y-x)) (exp_pos x).le; rw [← exp_add,add_sub_cancel] at H
   linarith
private lemma exp_dist (x y : ℝ) : ‖exp x-exp y‖ ≤ ‖x-y‖*exp (max x y) := by
   cases le_total x y with
   | inl h => rw [max_eq_right h, norm_sub_rev (exp _), norm_sub_rev x]; exact exp_dist' h
   | inr h => rw [max_eq_left h]; exact exp_dist' h

lemma Costs.exp_delta (h : Costs T S f fun _ _=>1) (h' : Costs T S f' fun _ _=>1) (hh : Costs T S (fun i p=> f i p-f' i p) g) :
    Costs T S (fun i p => exp (f i p)-exp (f' i p)) (fun i p=>g i p * exp (max (f i p) (f' i p))) := by
  let F i p := exp (f i p); let F' i p := exp (f' i p)
  let Y i p := _root_.fderiv ℝ (f i) p; let Z i := _root_.fderiv ℝ fun p=> f i p-f' i p
  let U i p := exp (max (f i p) (f' i p)); let W i p := g i p * U i p
  have hU i p : 0 < U i p:= exp_pos _
  have he := h.exp_full; have he' := h'.exp_full
  have hs i : ContDiff ℝ ∞ fun p=> F i p-F' i p := (he.smooth i).sub (he'.smooth i)
  have hY : Costs T S Y (fun i _=>S.length i):= by simpa [Y] using h.fderiv
  have hZ : Costs T S Z (fun i p=> g i p*S.length i) := hh.fderiv
  have hw : Costs T S F' U:= he'.raise (Cost.of_le (fun i p _=> exp_monotone (le_max_right ..)))
  refine ⟨hs,?_⟩; intro j; induction j using Nat.strong_induction_on with
  | _ j IH=>
    cases j with
    | zero=> exact Cost.Part.start.mpr ((hh.norm_cost.cancel (fun i p _=>(hU i p).le)).left (fun i p _=> exp_dist _ _))
    | succ j =>
      have ha i : _root_.fderiv ℝ (fun p=> F i p-F' i p)= fun p=> (F i p-F' i p) • Y i p + F' i p • Z i p := by
         funext p; have hp := (h.smooth i).differentiable (by simp) p; have hp' := (h'.smooth i).differentiable (by simp) p
         simp only [Y,Z,F,F', fderiv_fun_sub hp hp', fderiv_fun_sub hp.exp hp'.exp,fderiv_exp hp,fderiv_exp hp']; module
      apply Cost.Part.next.2
      change T.Part S (fun i=> _root_.fderiv ℝ (fun p=> F i p-F' i p)) _ j; simp_rw [ha]
      have hq : T.Part S (fun i p=> (F i p-F' i p) • Y i p) (fun i p=> W i p*S.length i) j:= Cost.Part.bilinear (A:=ContinuousLinearMap.lsmul ℝ ℝ) hs hY.smooth (fun k hk=> IH k (by omega)) fun k _=> hY.quoted k
      refine hq.add (fun i=> (hs i).smul (hY.smooth i)) ?_ (fun i=> (hw.smooth i).smul (hZ.smooth i))
      refine Cost.Part.adjust ((hw.smul hZ).quoted j) (Cost.of_le fun i p _=>?_); unfold W; apply le_of_eq; ring
end
section
variable {a : ι→ℝ} {c : ℝ}
def Scale.region (S : Scale ι) (D : ι → Set E) : Cost ι E := ⟨D,S.full.cheap, fun i p _=> S.full.one_le i p trivial⟩
lemma Costs.localize {f : Kern ι E F} {g : Kern ι E ℝ} (h : Costs S.full S f g) : Costs (S.region D) S f g := by
  refine ⟨h.smooth, fun j=>?_⟩; obtain ⟨C,hC,b,h⟩:= h.quoted j
  exact ⟨C,hC,b, fun i p _=>h i p (mem_univ _)⟩

/-- Use exponential in norm (not square), its constant offset in later conversions is harmless. -/
def Scale.damp (S : Scale ι) (c : ℝ) (i:ι) (p : E) := exp (-c * (S.length i*‖p‖))

private lemma damp_cost (hb:0<c) (b:ℕ) : ∃ C : ℝ, 0<C ∧ ∀ x : ℝ, 0≤x → LogTime.polyExp c b x ≤ C := by
    have h : ∀ᶠ x in atTop, LogTime.polyExp c b x ≤ 1:= (LogTime.vanishes hb _).eventually (ge_mem_nhds zero_lt_one)
    obtain ⟨x,h⟩ := eventually_atTop.mp h
    refine ⟨(1+max x 0)^b, by positivity, fun a ha=>?_⟩
    rcases le_total x a with H|H
    · exact (h a H).trans (one_le_pow₀ (by simp))
    have hi : exp (-c*a) ≤ 1 := exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) ha)
    unfold LogTime.polyExp; apply (mul_le_of_le_one_right (by positivity) hi).trans
    gcongr; exact le_max_of_le_left H
lemma Costs.damped {f : Kern ι E F} (h : Costs (S.region D) S f (fun i p=> a i * S.damp c i p)) (hp : ∀ i, 0 ≤ a i) (hc : 0<c) :
    Line S D f a := by
  intro b; refine ⟨h.smooth, fun j=>?_⟩
  obtain ⟨C,hC,d,H⟩ := h.quoted j
  obtain ⟨A,hA,hq⟩:=damp_cost hc (b+d)
  refine ⟨C*A,by positivity,d,fun i p hx=> (H i p hx).trans ?_⟩
  specialize hp i
  let R:= S.weight i p; have hz:R>0:=S.weight_pos i p
  have hL:= S.pos i; have hB:= S.basic_pos i
  have hw : R^(b+d)*S.damp c i p≤ A:= hq _ (mul_nonneg hL.le (norm_nonneg _))
  change C*(S.basic i * R)^d*(a i*S.damp c i p*S.length i^j) ≤ C*A*(S.basic i)^d*(a i / R^b*S.length i^j)
  rw [mul_pow]
  calc
    _ = C*((S.basic i)^d*(a i/R^b*S.length i^j))*(R^(b+d)*S.damp c i p) := by rw [pow_add]; field_simp
    _ ≤ C*((S.basic i)^d*(a i/R^b*S.length i^j))*A := mul_le_mul_of_nonneg_left hw (by positivity)
    _ = _ := by ring
end
end YM.MS
