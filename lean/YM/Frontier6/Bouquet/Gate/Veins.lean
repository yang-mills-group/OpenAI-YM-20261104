import YM.Frontier6.Bouquet.Gate.Grab

/-! Cut disjoint regions exactly in the finite-λ test representations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Submodule Normal Analysis Anise Metric
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff
open scoped YM.Frontier6.Bouquet
variable {P Q R:Ensemble}
-- cutoff radius (can be specified for all finite needs; proofs invariance via limit)
structure Veins where
   range : Pod→ℝ
   pos :∀ u,0 < range u
namespace Veins
variable (C:Veins)
abbrev blend (p:Pod)(x:Room):= 1-Normal.shrink (normal p) (C.range p) (ontoSpace (normal p) x)
def cutter (s:Finset Pod)(x:Room):ℂ:= ∏ p∈s,C.blend p x
def susp (P Q: Ensemble):= cutter C (scars P Q)
lemma blend_smooth (p:Pod) : Smooth (C.blend p):= contDiff_const.sub ((Normal.shrink (normal p) (C.range p)).contDiff.comp (ontoSpace (normal p)).contDiff)
lemma cutter_smooth (s:Finset Pod) : Smooth (C.cutter s):= contDiff_prod (t:=s) (fun p _=> C.blend_smooth p)
lemma cutter_safe {s:Finset Pod}{p:Pod}(hh:p∈s):Function.support (C.cutter s)⊆ {x| C.range p ≤ ‖ontoSpace (normal p) x‖}:=by
    intro x hx; change C.range p ≤ ‖ontoSpace (normal p) x‖; apply le_of_not_gt; intro h; exact hx (Finset.prod_eq_zero hh (sub_eq_zero.mpr (shrink_home (C.pos _) _ h.le).symm))
lemma cutter_tale {s:Finset Pod}{p:Pod}(hh:p∈s):tsupport (C.cutter s)⊆ {x| C.range p ≤ ‖ontoSpace (normal p) x‖}:=
   closure_minimal (C.cutter_safe hh) (isClosed_le continuous_const (ontoSpace (normal p)).continuous.norm)
lemma cutter_fixed (s:Finset Pod){x:Room}(he:∀ p∈s, 2*C.range p < ‖ontoSpace (normal p) x‖): C.cutter s x=1:=by
   apply Finset.prod_eq_one; intro p hp; unfold blend; rw [(shrink_fits (X:=normal p) (C.pos p)).out _ (he p hp), sub_zero]

lemma susp_both (h:P ≤ Q)(he:Q ≤ R): C.susp R P=C.susp Q P*C.susp R Q:=by ext1 x; unfold susp cutter; rw [←scars_zip h he, Finset.prod_union (scars_apart P Q R)]; exact mul_comm ..
lemma susp_products {A B:Ensemble}(hv:Free P Q)(he:Free A B)(hp:A≤P)(hq:B≤Q): C.susp (merge hv) (merge he)= C.susp P A*C.susp Q B:=by
    unfold susp cutter; ext1 x; rw [scars_sum hv he hp hq, Finset.prod_union (hv.enclosed.mono (show scars P A ⊆ P.enclosed from Finset.sdiff_subset) (show scars Q B ⊆ Q.enclosed from Finset.sdiff_subset))]; rfl -- spacing

def film (P Q: Ensemble): Full (fiber P) →ₗ[ℂ] Full (fiber P) := screen (C.susp P Q ∘ (fiber P).subtypeL) ((C.cutter_smooth _).comp (fiber P).subtypeL.contDiff)
lemma filmed (f:Full (fiber P))(y:fiber P) : C.film P Q f y=C.susp P Q y.val * f y:= rfl
lemma film_here (f:Full (fiber P)) : film C P P f=f:=by ext1 x; rw [filmed]; simp [susp,scars,cutter]
lemma film_support (P Q: Ensemble) (f: Full (fiber P)): tsupport (C.film P Q f) ⊆ tsupport f:= screen_subset ..
lemma film_support' (Q:Ensemble)(f:Full (fiber P)): tsupport (C.film P Q f) ⊆ {x:fiber P|x.val∈ tsupport (C.cutter (scars P Q))}:=
    let F:= C.susp P Q; subset_trans (tsupport_mul_subset_left (f:=F ∘ (fiber P).subtypeL) (g:=f)) (tsupport_comp_subset_preimage F continuous_subtype_val) -- names
section
variable (h:P ≤ Q) (he:Q ≤ R)(z:Margin R Q)(x:fiber Q)(p:Pod)(hp:p∈ Q.enclosed)
include he hp in
lemma projected_scar : ontoSpace (normal p) (forward (plan_sub he) (insideCL loft_le z) x).val= ontoSpace (normal p) x.val:=by
    rw [forward_cast,map_add]; have hx:(insideCL (show Margin R Q≤ fiber R from loft_le) z).val=z.val:=rfl; rw [hx]; obtain ⟨u,hu,hy⟩:= encloses.mp hp; rw [on_blank (orthogonal_le ((normal_sub hy).trans (home_sub hu)) (loft_orth z.property)), zero_add] -- syntactic Cast
lemma susp_scar : C.susp Q P (forward (plan_sub he) (insideCL loft_le z) x).val=C.susp Q P x.val:=by unfold susp cutter; exact prod_congr rfl (fun p hp=>by unfold blend; rw [projected_scar he z x p (Finset.mem_sdiff.mp hp).1]) -- include h? hidden
include h
lemma rectified (f:Full (fiber R)) : restrictS (plan_sub he) (insideCL loft_le z) (C.film R P f)= C.film Q P (restrictS (plan_sub he) (insideCL loft_le z) (C.film R Q f)):=by
    ext1 x; let y:=forward (plan_sub he) (insideCL loft_le z) x; have ht:C.susp R P y.val=C.susp Q P x.val*C.susp R Q y.val:= (congr_fun (C.susp_both h he) y.val).trans (show _ from congr_arg (· * C.susp R Q y.val) (C.susp_scar (P:=P) he z x)); change C.susp R P y.val*f y=C.susp Q P x.val*(C.susp R Q y.val*f y); rw [ht,mul_assoc]
end
end Veins
end YM.Frontier6.Bouquet
