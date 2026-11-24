import YM.RG05Readout.Velvet.Tide
import YM.RG05Readout.Pulse.Chills
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Velvet
open Function MeasureTheory Set Filter Topology Pulse Native Address Many Lattice Wilson Extraction WithLp
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
set_option quotPrecheck false
variable {m n:ℕ}
-- volumes use no normalization change align ℓ². For reflected applications
-- use Table.Pair.pairIso; this adapter is for positions unreflected.
def tie (m n:ℕ): WithLp 2 (Points m×Points n) ≃ₗᵢ[ℝ] Points (m+n) where
   toFun p:= points (Fin.append p.fst.ofLp p.snd.ofLp)
   invFun p:= toLp 2 (points (fun i=>p (Fin.castAdd n i)),points fun i=>p (Fin.natAdd m i)) -- fix
   left_inv p:=by
      apply WithLp.ofLp_injective 2; refine Prod.ext (PiLp.ext (fun i=>?_)) (PiLp.ext (fun i=>?_)); exact Fin.append_left ..; exact Fin.append_right ..
   right_inv p:=by
      apply PiLp.ext; intro i; refine Fin.addCases ?_ ?_ i<;> intro i; exact Fin.append_left ..; exact Fin.append_right ..
   map_add' p q:=by
      apply PiLp.ext; intro i; refine Fin.addCases (fun i=>?_) (fun i=>?_) i<;> simp
   map_smul' a b:=by
      apply PiLp.ext; intro i; refine Fin.addCases (fun i=>?_) (fun i=>?_) i<;> simp
   norm_map' p:=by
       rw [←sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),PiLp.norm_sq_eq_of_L2,WithLp.prod_norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2 _ p.fst,PiLp.norm_sq_eq_of_L2 _ p.snd,Fin.sum_univ_add]; simp
noncomputable def stripe (m n:ℕ) : Points (m+n) ≃L[ℝ] Points m × Points n := ((tie m n).symm).toContinuousLinearEquiv.trans (WithLp.prodContinuousLinearEquiv 2 ℝ (Points m) (Points n))
lemma stitches : MeasurePreserving (stripe m n):=(WithLp.volume_preserving_ofLp _ _).comp ((tie m n).symm.measurePreserving)
def ribbon (x:Points m)(y:Points n): Points (m+n):=(stripe m n).symm (x,y)
lemma ribbon_cons (x:Points m)(y:Points n): ribbon x y=points (Fin.append x.ofLp y.ofLp):=rfl
noncomputable def unbutton (n:ℕ): Points (n+1)≃L[ℝ] E4 × Points n:= (Points.peel).toContinuousLinearEquiv.trans (WithLp.prodContinuousLinearEquiv 2 ℝ _ _)
lemma buttons (n): MeasurePreserving (unbutton n):=(WithLp.volume_preserving_ofLp _ _).comp ((Points.peel (n:=n)).measurePreserving)
lemma zipper (x:E4) (y:Points n) : (unbutton n).symm (x,y)=Points.cons x y:=rfl
section
open Finset
end
section
variable {Ψ:Wave (Fin m)}{g:Body}(hG:IsCompact (tsupport g.val))(hF:IsCompact (tsupport Ψ.val)){q:ℝ}(h:0<q)
local notation "L"=> (tsupport g.val)
noncomputable def beginAt (q:ℝ)(z:E4)(x:Points m): Points m:= points (fun _=> z)+ q • x
@[simp]
lemma short (q:ℝ)(z:E4)(x:Points m)(i): beginAt q z x i=z+q • (x i):=rfl
abbrev bag (m:ℕ): Points m ≃L[ℝ] Cloud (Fin m):= PiLp.continuousLinearEquiv 2 ℝ _
def pattern (Ψ:Wave (Fin m)):Points m→ℂ:= fun x=> Ψ.val x.ofLp
def overturn (q:ℝ)(z:E4)(x:Points m) :Points m:= q⁻¹ • (x-points fun _=> z)
lemma shaped (z:E4) (x:Points m): (rel q Ψ z).val x.ofLp=pattern Ψ (overturn q z x):=by apply congr_arg Ψ.val; ext1 i; change q⁻¹ • _ + q⁻¹ • _= q⁻¹ • (x i-z);rw [sub_eq_add_neg,smul_add,add_comm] -- defeq
include h
lemma unturned (x:Points m)(z:E4): beginAt q z (overturn q z x)=x:=by unfold beginAt overturn; rw [smul_inv_smul₀ h.ne',add_sub_cancel ..] -- check
lemma turned (x:Points m)(z:E4): overturn q z (beginAt q z x)=x:=by unfold beginAt overturn;rw [add_sub_cancel_left,inv_smul_smul₀ h.ne']
omit h
abbrev scoreHull (Ψ:Wave (Fin m)) :Set (Points m):= (bag m)⁻¹' tsupport Ψ.val
lemma patterned_sub : tsupport (pattern Ψ) ⊆ scoreHull Ψ := closure_minimal (fun _ hx=> subset_closure hx) ((isClosed_tsupport _).preimage (bag m).continuous)
include hF
lemma scoreSmall : IsCompact (scoreHull Ψ) := (bag m).toHomeomorph.isCompact_preimage.mpr hF
lemma pattern_support : IsCompact (tsupport (pattern Ψ)) := (scoreSmall hF).of_isClosed_subset isClosed_closure patterned_sub
abbrev pad (Ψ: Wave (Fin m)) (g:Body) (q:ℝ): Set (Points m):= (fun z:E4×Points m=> beginAt q z.1 z.2) '' (tsupport g.val ×ˢ scoreHull Ψ)
local notation "P"=> pad Ψ g q
include hG
lemma padSmall : IsCompact P := (hG.prod (scoreSmall hF)).image (f:=fun z:E4 × Points m=> _) (by unfold beginAt; apply Continuous.add _ (continuous_snd.const_smul q); exact (bag m).symm.continuous.comp (continuous_pi fun _=> continuous_fst))
include h
lemma outline : tsupport (pattern (molten Ψ q hG))⊆ P:=by
   apply closure_minimal _ (padSmall hG hF).isClosed; intro x hx; unfold pattern at hx; by_contra he
   apply hx; dsimp only; rw [glow_point]
   have hv(z:E4): g.val z*(rel q Ψ z).val x.ofLp=0:=by
      by_contra hζ; exact he ⟨(z,overturn q z x),⟨subset_closure (left_ne_zero_of_mul hζ),patterned_sub (subset_closure (show pattern Ψ (overturn q z x)≠0 from by rw [← shaped]; exact right_ne_zero_of_mul hζ))⟩, unturned h x z⟩
   simp_rw [hv,integral_zero]
end
end YM.RG05Readout.Velvet
