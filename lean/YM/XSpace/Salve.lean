import YM.XSpace.Carnation
/-!
# Reparametrize along the announced coupling

Use `Use` eventually on regulators. Junk branch = identity outside that filter. Uniform odd & real transform. No claim that g_top ≈ X exactly at finite gauges; only coeff1 tends to one. No control beyond finite-cutout invertibility given here for higher orders.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Rose
open Function Set Filter MeasureTheory Trace Graph3 Photo Cirrus Normalize AxesTangent PowerSeries ComplexConjugate Retirement Lattice
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}(W:Initialize G) {V:Store G}(Y:Rose.Pick V)(g:G.Simple)(l:Mesh)
local notation "y" => chosen W Y l
abbrev Use := coeff 1 y ≠0
def χ : PS:= if h : Use W Y l then (y).substInvOfIsUnit (isUnit_iff_ne_zero.mpr h) else X
lemma χzero : constantCoeff (χ W Y l)=0:=by unfold χ; split_ifs <;> simp
lemma χday : HasSubst (χ W Y l):= HasSubst.of_constantCoeff_zero' (χzero ..)
local notation "z" => χ W Y l
lemma invertsX (h: Use W Y l): (y).subst z=X:=by rw [χ,dif_pos h]; exact subst_substInvOfIsUnit_right y (zero_choice ..) _
lemma χverts (h: Use W Y l): (z).subst y=X:=by rw [χ,dif_pos h]; exact subst_substInvOfIsUnit_left y (zero_choice ..) _
lemma χinject (h: Use W Y l){f k:PS}(hp:constantCoeff f=0)(hk: constantCoeff k=0)(H:(y).subst f=(y).subst k): f=k:=by
  have he (p:PS)(he:constantCoeff p=0): (z).subst ((y).subst p)=p:=by rw [← subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' (zero_choice W Y l)) (HasSubst.of_constantCoeff_zero' he),χverts W Y l h, subst_X (HasSubst.of_constantCoeff_zero' he)] -- assoc? rw
  exact (he f hp).symm.trans ((congr_arg (fun x:PS=>(z).subst x) H).trans (he k hk))
abbrev ℛ:= starRingEnd ℂ
lemma realχ : PowerSeries.map ℛ z=z:=by
  by_cases h:Use W Y l; swap; · unfold χ; rw [dif_neg h,map_X]
  refine χinject W Y l h (FPS.mapped_zero _ (χzero ..)) (χzero ..) ?_; have he:PowerSeries.map ℛ y=y:= PowerSeries.ext fun i=> Eq.trans (coeff_map ..) (real_c ..); rw [← congr_arg (fun p:PS=>p.subst _) he, ← FPS.substitute_ringHom ℛ _ (χzero W Y l), invertsX W Y l h,map_X] -- syntax
lemma χstar (n:ℕ):star (coeff n z)=coeff n z:=by rw [← starRingEnd_apply, ← coeff_map, realχ]
private lemma basement {f:PS}(h:constantCoeff f=0): constantCoeff (inversion f)=0:=by rw [← coeff_zero_eq_constantCoeff_apply,inversion, coeff_rescale,coeff_zero_eq_constantCoeff_apply,h,mul_zero]
private lemma subneg (f:PS)(x:PS)(h:HasSubst (S:=ℂ) x): (-f).subst x = -f.subst x:= by rw [← coe_substAlgHom h]; rw [map_neg]
lemma rescale_flip (f k:PS)(h:constantCoeff k=0): f.subst (-k)=(inversion f).subst k:=by
  have H:= HasSubst.of_constantCoeff_zero' h; rw [inversion,rescale_eq_subst,neg_one_smul, subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' (a:= - (X:PS)) (by simp)) H, subneg _ k H, subst_X H] -- invalid
lemma χodd (H: V.Meets W l 6): inversion z= -z:=by
  by_cases h:Use W Y l; swap; · unfold χ; rw [dif_neg h]; exact rescale_neg_one_X
  apply χinject W Y l h (basement (χzero ..)) (by rw [map_neg,χzero,neg_zero]); rw [inversion,← FPS.rescale_substitute y z (χzero W Y l),rescale_flip y _ (χzero W Y l),odd_c W Y l H,subneg y z (χday W Y l),invertsX W Y l h,rescale_neg_one_X]
lemma firstχ (h:Use W Y l): coeff 1 z=(coeff 1 y)⁻¹:=by
  have hh:= congr_arg (coeff 1) (invertsX W Y l h); rw [coeff_one_X,FPS.coeff_substituted _ (χzero W Y l)] at hh; simp [Finset.sum_range_succ] at hh; exact mul_left_cancel₀ h (hh.trans (mul_inv_cancel₀ h).symm)
include g in
lemma χlimit : Tendsto (fun l=> coeff 1 (χ W Y l)) Front (𝓝 (1:ℂ)) := by have ht:= (xc W Y g).inv₀ one_ne_zero; rw [inv_one] at ht; exact ht.congr' ((usable W Y g).mono fun i hi=>(firstχ W Y i hi).symm)
end YM.XSpace.Rose
