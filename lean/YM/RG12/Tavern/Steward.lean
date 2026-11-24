import YM.RG12.Tavern.Wheel
/-! # Change back to the physical Club pencils from any weather-certified frame

Consecutive normalized prices can be in ANY graded basis W and independent of the official
k-calibrated pencil! As long as W is filtration-compatible and both W and Y have uniform norms
at the common seam (supplied ever in Club, or lift from zeroth-order quantitative pricing).
Thus e.g. don't require proving literal A expansion of the small-field-derived threshold
pencil with no unplanned monitor contamination. Use an alternative position measuring basis
with high-precision pair expansions and first-order scale-law/ties, and change AFTER ratio-consumer
with just a POLYNOMIAL price to its shear. At no stage transporting remainders to IR.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Tavern
open Frames Alidade Function Filter Set Real Finset
open scoped Topology BigOperators Classical
variable {d:ℕ}{V:Grade d→Type}[∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℂ (V i)]
  [FiniteDimensional ℂ (Col V)]{F:Type}[AddCommGroup F][Module ℂ F]
variable (P Y X:Col V≃ₗ[ℂ] F)(t:ℝ)(ht:0<t)
local notation "A!"=>Col V
 -- Cannot rely on `private expand` definition name in Teams, build new inverse.
def lensing (u:ℝ)(hu:0 < u):MC V := LinearEquiv.ofLinear (dilate u) (dilate u⁻¹) (LinearMap.ext fun x=> scale_cancel' hu.ne' x) (LinearMap.ext fun x=> scale_cancel hu.ne' x)
variable {t}
-- P uses generic slot? portal from X→Y. send Y basis coordinates to X. conjugator.
def castL := Y.trans X.symm
def tideMap : MC V:= let S:=castL Y X
                      let A:=lensing t ht
                      S.trans (A.trans (S.symm.trans A.symm))
local notation "S!"=>castL Y X
local notation "K!"=>tideMap Y X ht
omit [FiniteDimensional ℂ (Col V)] in
lemma tide_cast (a:A!): K! a = dilate t⁻¹ ((S!).symm (dilate t (S! a))) := rfl
omit [FiniteDimensional ℂ (Col V)] in
lemma returning (a:A!): (K!).symm a=(S!).symm (dilate t⁻¹ (S! (dilate t a))):=rfl
omit [FiniteDimensional ℂ (Col V)] in
lemma hooking (a:A!): Y (dilate t (K! a))= X (dilate t (S! a)):=by rw [tide_cast,scale_cancel' ht.ne']; change Y (Y.symm (X _)) = _; rw [Y.apply_symm_apply]
omit [FiniteDimensional ℂ (Col V)] in
lemma tripwire (a:A!):X (S! a)=Y a:=X.apply_symm_apply _
variable {P} (h:formative Y P)(hc:formative X P)
include h hc
lemma film : triangular V (S!).toLinearMap:=by
   let A:=Y.trans P.symm; let B:=X.trans P.symm
   have hx : triangular V (B.symm.trans (LinearEquiv.refl ℂ _)).toLinearMap:=hc.inv -- rfl?
   have he: S! = A.trans B.symm:=by ext1 v; change X.symm _= X.symm (P (P.symm (Y v))); rw [P.apply_symm_apply];rfl
   rw [he]; exact hx.comp h
lemma tidal : triangular V (K!).toLinearMap:= ((tri_dilate (V:=V) t⁻¹).comp ((film Y X h hc).inv.comp ((tri_dilate (V:=V) t).comp (film Y X h hc)))) -- comp nesting? actual trans
lemma tide_block (i:Grade d)(v:V i):block V (K!).toLinearMap i i v=v:=by
   let S:= castL Y X; let p:= put V i v
   change K! p i =v; rw [tide_cast,dilation]
   have hT:= film Y X h hc; have hU:= hT.inv
   have hf:=put_flag i i v le_rfl
   rw [show (S!).symm (dilate t (S! p)) i = block V S.symm.toLinearMap i i (dilate t (S! p) i) from same_diag hU ((triangular_iff_stays V _).mp ((tri_dilate (V:=V) t).comp hT) i _ hf)]
   let z:=block V S.toLinearMap i i v
   have hz:block V S.symm.toLinearMap i i z=v:= inv_diag (A:=S.symm) hU i v
   have he(c:ℂ) : block V S.symm.toLinearMap i i (c • z)=c • block V S.symm.toLinearMap i i z:=by
      unfold block put
      rw [show Pi.single i (c • z)=c • Pi.single i z from ?_,map_smul]; rfl
      ext1 j; cases eq_or_ne i j with
      | inl h=> subst h; simp only [Pi.smul_apply, Pi.single_eq_same]
      | inr h=> simp only [Pi.smul_apply,Pi.single_eq_of_ne h.symm, smul_zero]
   rw [dilation,show S! p i=z from rfl,he,hz,smul_smul,← Complex.ofReal_mul,inv_pow,inv_mul_cancel₀ (pow_ne_zero _ ht.ne'),Complex.ofReal_one,one_smul]
omit h hc
variable {r s:ℝ}(R:F→ℝ)(hx:Tests (R∘X) s)(hy:Tests (R∘Y) r)
include hx hy
omit [FiniteDimensional ℂ (Col V)] in
lemma deck (a:A!):
  ‖S! a‖ ≤ s*r*‖a‖ ∧ ‖(S!).symm a‖ ≤ s * r *‖a‖:=by
    have he :0≤r:=zero_le_one.trans hy.legal; have he' :0≤ s:=zero_le_one.trans hx.legal
    have h(x:Col V):Y ((S!).symm x)=X x:=Y.apply_symm_apply _
    constructor
    · apply (hx.lower _).trans
      rw [Function.comp_apply,tripwire]
      exact (mul_le_mul_of_nonneg_left (hy.upper _) he').trans_eq (mul_assoc ..).symm
    apply (hy.lower _).trans
    rw [Function.comp_apply,h]
    exact (mul_le_mul_of_nonneg_left (hx.upper _) he).trans_eq (by ring)
omit [FiniteDimensional ℂ (Col V)] in
lemma floods (a:A!)(hv:1 ≤ t): ‖K! a‖ ≤ (s*r)^2*t^d*‖a‖ ∧ ‖(K!).symm a‖ ≤ (s*r)^2*t^d*‖a‖:=by
   have h₁:0 ≤ s*r:=mul_nonneg (zero_le_one.trans hx.legal) (zero_le_one.trans hy.legal)
   have h₂(a:A!):‖Frames.dilate t a‖ ≤ t^d*‖a‖:=by
      rw [pi_norm_le_iff_of_nonneg (by positivity)]; intro j
      rw [dilation,norm_smul,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul (pow_le_pow_right₀ hv j.is_le) (norm_le_pi_norm a j) (norm_nonneg _) (pow_nonneg ht.le _)
   have h₃(a:A!): ‖Frames.dilate t⁻¹ a‖ ≤ ‖a‖:=by
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg a)).mpr (fun j=>?_)
      rw [dilation,norm_smul,Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      exact (mul_le_mul (pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hv)) (norm_le_pi_norm a j) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
   have hf:= deck Y X R hx hy
   constructor
   · rw [tide_cast]; apply (h₃ _).trans ((hf _).2.trans _)
     grw [h₂ _,(hf _).1]; apply le_of_eq; ring
   rw [returning]; apply (hf _).2.trans _
   grw [h₃ _,(hf _).1,h₂ _];apply le_of_eq; ring
end YM.RG12.Tavern
