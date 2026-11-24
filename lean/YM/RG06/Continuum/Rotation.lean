import YM.RG06.Continuum.RadialQuot
import YM.Extra.FREE_DETECTOR_ALGEBRA.Covariance
/-!
# Index conventions & geometric soldering
All directions incl antisymmetric & unsymmetrized curvature slots transform, with NO
orientation sign on each field other than the pullback of its indices; pseudo behavior (if
required) only by contracted label choice. Taylor integrates A as a covector without
coupling or reflection twist. Conjugation when reflecting for OS is a separate operation.
This file pins O4 with its inverse in exactly the same slots as `Taylor.turn`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.Continuum
open Analysis Tensor Maxwell Extra.FD Pert.Bare Pert.Align Labels
open scoped Topology ContDiff Matrix.Norms.Frobenius ComplexConjugate BigOperators Classical
namespace Form
variable {G : Gauge} {j k : ℕ}

def spread : Response G j→ₗ[ℝ] TwoJet G.Color j where
  toFun v i b:=∑ w, spaceMon w (v i b w)
  map_add' v u:=by funext i b; ext1 z; simp [sum_apply,mon_eq,smul_add, Finset.sum_add_distrib]
  map_smul' c v:=by funext i b; ext1 z; simp [sum_apply,mon_eq,smul_comm c,Finset.smul_sum]
lemma spread_at (v:Response G j)(i b:Axis)(z):spread v i b z=∑ w, (∏ a, z a (w a)) • (v i b w):=by
  change (∑ w, spaceMon w (v i b w)) z=_;rw [sum_apply]; rfl

def tally : TwoJet G.Color j→ₗ[ℝ] Response G j where
  toFun v i b w:=v i b fun a=>basis (w a)
  map_add' _ _:=rfl
  map_smul' _ _:=rfl
lemma tally_spread (v:Response G j):tally (spread v)=v:=by
  funext i b w; change spread v i b (fun a=>basis (w a))=v i b w
  rw [spread_at,Finset.sum_eq_single w]
  · simp [basis_eq]
  · intro a _ ha; obtain ⟨k,h⟩:= Function.ne_iff.mp ha
    have he:k∈(Finset.univ:Finset (Fin j)):=by simp
    rw [Finset.prod_eq_zero he (show (basis (w k)) (a k)=0 from by simp [basis_eq,h])]; simp
  simp
lemma spread_tally (v:TwoJet G.Color j):spread (tally v)=v:=by
  funext i b; ext1 z; rw [spread_at]
  change _ = (v i b).toMultilinearMap _
  conv_rhs=> arg 2; rw [← show (fun k=> ∑ a:Axis,z k a • basis a)= z from funext (fun k=> by ext t; simp [WithLp.ofLp_sum,Finset.sum_apply,basis,Pi.single_apply,mul_ite])]
  rw [MultilinearMap.map_sum_finset];simp_rw [(v i b).toMultilinearMap.map_smul_univ,Fintype.piFinset_univ];rfl

def bouquet : Response G j≃ₗ[ℝ] TwoJet G.Color j:=
  {spread with invFun:=tally, left_inv:=tally_spread, right_inv:=spread_tally}

def impulseO (u:Ortho):Response G j→ₗ[ℝ] Response G j:=tally ∘ₗ carry u ∘ₗ spread
lemma turned_basis (u:Ortho)(p:Response G j)(i b:Axis)(w:Fin j→Axis) : impulseO u p i b w=
    bi u.val (fun a k=>spread p a k (fun l=> mov u⁻¹ (basis (w l)))) i b:=carry_eval u _ _ _ _
lemma spread_turned (u:Ortho)(v:Response G j):spread (impulseO u v)=carry u (spread v):=by rw [impulseO,LinearMap.comp_apply,LinearMap.comp_apply,spread_tally]

/-- O4 action on independent extrapolated covariant slots (not projected yet). -/
def turning (u:Ortho)(v:Tower G):Tower G:=fun j=> impulseO u (v j)
lemma turning_id (v:Tower G):turning 1 v=v:=by
  funext j; change tally (carry 1 (spread (v j)))=v j; rw [carry_id,tally_spread]
lemma turning_composes (u r:Ortho)(v:Tower G):turning u (turning r v)=turning (u*r) v:=by
  funext j; change tally (carry u (spread (impulseO r (v j)))) = tally (carry (u*r) (spread (v j)))
  rw [spread_turned,carry_mul]
lemma colored_orbits (u:Ortho)(s:G.El)(v:Tower G):spin s (turning u v)=turning u (spin s v):=by
  funext j i b w; change G.adjoint s (impulseO u _ i b w)=impulseO u _ i b w
  simp_rw [turned_basis,bi_eval,spread_at,spin,map_sum,map_smul];simp

-- radial_value rewritten as contraction of genuine multilinear extension
lemma radial_eq_box (v:Response G j)(i:Axis)(x:E4): (radialize v).value i x=
    ((↑(j+2:ℕ)):ℝ)⁻¹ • (1/2:ℝ) •
    ∑ k:Axis,x k • (diagonal (spread v k i) x - diagonal (spread v i k) x):=by
  rw [Pert.Bare.radial_value]; simp_rw [diagonal,spread_at,← Finset.sum_sub_distrib, ← smul_sub,Finset.smul_sum,smul_smul]
  -- assoc under sums
  refine Finset.sum_congr rfl fun k _=>?_ ; refine Finset.sum_congr rfl fun a _=>?_ ; congr 2; ring

lemma transfer_contract (u:Ortho)(v:TwoJet G.Color j)(i:Axis)(x:E4)(z):
    ∑ k:Axis,x k • (bi u.val (fun a b=> v a b z) k i - bi u.val (fun a b=>v a b z) i k) =
    ∑ b:Axis,u.val i b • ∑ a:Axis,mov u⁻¹ x a • (v a b z-v b a z):=by
  have he(k b:Axis):bi u.val (fun a c=>v a c z) k b-bi u.val (fun a c=>v a c z) b k=
    bi u.val (fun a c=>v a c z-v c a z) k b:=by
    simp_rw [bi_eval]; nth_rw 2 [Finset.sum_comm]
    simp_rw [← Finset.sum_sub_distrib, smul_sub]
    refine Finset.sum_congr rfl fun a _=> Finset.sum_congr rfl fun c _=>?_ ; rw [smul_comm (u.val b c)]
  have hsum(k:Axis):bi u.val (fun a c=>v a c z-v c a z) k i=∑ c,∑ a:Axis,u.val k a • u.val i c • (v a c z-v c a z):= by rw [bi_eval,Finset.sum_comm]
  simp_rw [he,hsum,Finset.smul_sum, mov_apply, Ortho.move,M4.at_coord, Extra.FD.inv_at]
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun b _=>?_ ; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun a _=>?_ ; rw [Finset.sum_smul,Finset.smul_sum];refine Finset.sum_congr rfl fun k _=>?_ ; simp only [smul_smul];congr 1; ring

lemma radial_turning (u:Ortho)(v:Response G j): radialize (impulseO u v)=Taylor.turn u (radialize v):=by
  apply Taylor.value_ext; funext i x
  simp_rw [Taylor.turn_value,radial_eq_box, spread_turned, diagonal,carry_eval]
  rw [transfer_contract]; simp only [Finset.smul_sum,smul_smul,mov_apply]; refine Finset.sum_congr rfl fun b _=> Finset.sum_congr rfl fun a _=>?_ ;congr 1;ring

lemma rec_ortho (u:Ortho)(v:Tower G):recover (turning u v)=Labels.changedJet (fun _=>Taylor.turn u) (recover v):=funext fun _=>radial_turning u _

lemma redundant_ext (p q : Pol G) (h:∀ v:Tower G,applyTo v p=applyTo v q): p=q:=by
  apply MvPolynomial.funext_set (fun _=>Set.range ((↑): ℝ→ℂ)) (fun _=>Set.infinite_range_of_injective Complex.ofReal_injective)
  intro x hx
  choose y hy using fun k=> show ∃ t:ℝ,(t:ℂ)=x k from hx k (Set.mem_univ k)
  let v:Tower G:=fun j i b w=> WithLp.toLp 2 (fun c:G.ColorIndex=> y ⟨j,w,i,b,c⟩)
  rw [show x=coords v from funext (fun k=> (hy k).symm)];exact h v

open MvPolynomial
-- Contravariant on operators, but left action by inverting the motion
private def motionX (s:Ortho)(k:Glyph G):Pol G:=
  ∑ a:Spot G k.order, MvPolynomial.X (vertex a) * MvPolynomial.C (↑(impulseO s⁻¹ a.impulse k.faceL k.faceR k.chain k.color):ℂ)
lemma dual_motion (s:Ortho)(q:Tower G)(k:Glyph G):applyTo q (motionX s k)= coords (turning s⁻¹ q) k:=by
  let c(a:Spot G k.order):ℂ:= (↑(impulseO s⁻¹ a.impulse k.faceL k.faceR k.chain k.color):ℂ)
  have he:motionX s k=∑ a:Spot G k.order,X (vertex a)*C (c a):= by unfold motionX; rfl
  rw [he,map_sum]
  conv_rhs=> unfold coords turning
  conv_rhs=> rw [meter_full (q k.order),map_sum]
  simp only [Finset.sum_apply,WithLp.ofLp_sum,applyTo,map_mul,map_smul,Pi.smul_apply,PiLp.smul_apply,
    smul_eq_mul,aeval_X,aeval_C,Algebra.algebraMap_self,RingHom.id_apply, ← spot_meter,
    Complex.ofReal_sum,Complex.ofReal_mul]
  rfl

def depart (s:Ortho): Pol G→ₐ[ℂ] Pol G:= aeval (motionX s)

lemma turned_labels (s:Ortho)(p:Pol G)(v:Tower G):applyTo v (depart s p)=applyTo (turning s⁻¹ v) p:=by
  induction p using MvPolynomial.induction_on with
  | C c=>simp [depart,applyTo]
  | add p q hp hq=> simp only [_root_.map_add,hp,hq]
  | mul_X p i hp=> rw [_root_.map_mul,_root_.map_mul,_root_.map_mul,hp,depart,aeval_X,dual_motion,applyTo,aeval_X]

lemma departure_id (p:Pol G):depart 1 p=p:=redundant_ext _ _ fun _=>by rw [turned_labels,inv_one,turning_id]
lemma departure_composes (u s:Ortho)(p:Pol G):depart u (depart s p)=depart (u*s) p:=redundant_ext _ _ fun _=>by simp only [turned_labels,turning_composes,mul_inv_rev]

lemma motion_degree {M:Type*}[AddCommMonoid M](f:ℕ→M)(s:Ortho)(a: Glyph G):Tier (fun k:Glyph G=>f k.order) (f a.order) (motionX s a):=by
   unfold motionX; apply IsWeightedHomogeneous.sum; intro i _; rw [mul_comm]; exact (isWeightedHomogeneous_X ..).C_mul ..
lemma degree_turned {p:Pol G}(s:Ortho){M:Type*}[AddCommMonoid M](f:ℕ→M){m:M}(h:Tier (fun k:Glyph G=>f k.order) m p): Tier (fun k:Glyph G=>f k.order) m (depart s p):= by
   change Tier _ _ (eval₂Hom MvPolynomial.C (motionX s) _); exact Tier.bind _ _ (motion_degree f s) h

lemma finite_turned {p:Pol G}{d:ℕ}(s:Ortho)(h:p∈limited G d): depart s p∈limited G d:=by
   rw [p.as_sum,map_sum] -- conv_lhs through mem?
   apply Submodule.sum_mem; intro i hi; apply (MvPolynomial.mem_restrictSupport_iff ℂ).mpr; intro b hb
   have he:=degree_turned s (·+2) (MvPolynomial.isWeightedHomogeneous_monomial weight i (coeff i p) rfl (m:=Finsupp.weight _ i)) (MvPolynomial.mem_support_iff.mp hb)
   change Finsupp.weight weight b ≤ d; change Finsupp.weight weight b = _ at he; rw [he]; exact (MvPolynomial.mem_restrictSupport_iff ℂ).mp h hi

lemma invariant_turned {p:Pol G}(s:Ortho)(h:p∈invariant G): depart s p∈invariant G:=by
   intro q u; rw [turned_labels,turned_labels,← colored_orbits]; exact h _ _

def turnField (s:Ortho){d:ℕ}:Field G d →ₗ[ℂ] Field G d:=
   ((depart s).toLinearMap.comp (localSpace G d).subtype).codRestrict _
    fun p=>⟨finite_turned s p.property.1,invariant_turned s p.property.2⟩

lemma turn_lift {d:ℕ}(v: Labels.Label G d)(s:Ortho):turnField s (asGlyph v)=asGlyph (Labels.tensor s v):= by
   apply Subtype.ext; apply redundant_ext; intro q
   change applyTo q (depart s (sectionPol v.val))=applyTo q (sectionPol (Labels.rotated s v.val))
   rw [turned_labels,section_reads,section_reads,Labels.rotated,Labels.eval_changed,rec_ortho]

-- star on Euclidean operators before renormalization. No contact orientation or BV star inferred for
-- MSbar enlarged ring.
def conjScript (G:Gauge): Pol G→+* Pol G:= MvPolynomial.map (starRingEnd ℂ)
lemma real_script (q:Tower G)(p:Pol G):applyTo q (conjScript G p)=star (applyTo q p):=by
  induction p using MvPolynomial.induction_on with
  | C c=>simp [applyTo,conjScript]
  | add p u hp hv=>rw [_root_.map_add,_root_.map_add,_root_.map_add,hp,hv,star_add]
  | mul_X p i hp=>rw [_root_.map_mul,_root_.map_mul,_root_.map_mul,hp,star_mul];simp [applyTo,conjScript,coords,mul_comm]
lemma degree_real (p:Pol G)(b): coeff b (conjScript G p) = star (coeff b p):= by rw [conjScript,MvPolynomial.coeff_map];rfl
lemma finite_real {p:Pol G}{d:ℕ}(h:p∈limited G d): conjScript G p∈limited G d :=by
  apply (MvPolynomial.mem_restrictSupport_iff ℂ).mpr; intro b hb; apply (MvPolynomial.mem_restrictSupport_iff ℂ).mp h
  change b ∈ (conjScript G p).support at hb
  change b ∈ p.support; simpa only [MvPolynomial.mem_support_iff,degree_real, ne_eq,star_eq_zero] using hb
lemma invariant_real {p:Pol G}(h:p∈invariant G): conjScript G p ∈invariant G:= by
   intro q u;rw [real_script,real_script,h q u]
def realField {d:ℕ}(p:Field G d) : Field G d:= ⟨conjScript G p.val,finite_real p.property.1,invariant_real p.property.2⟩
lemma real_turn {d:ℕ}(p:Field G d)(s:Ortho): realField (turnField s p)=turnField s (realField p):= by
   refine Subtype.ext (redundant_ext _ _ (fun q=>?_)); change applyTo q (conjScript _ (depart s p.val)) = applyTo _ (depart _ (conjScript _ _)); rw [real_script,turned_labels,turned_labels,real_script]
lemma real_lift {d:ℕ}(p:Labels.Label G d): realField (asGlyph p)=asGlyph (Labels.realBar p) := by
   refine Subtype.ext (redundant_ext _ _ (fun q=>?_)); change applyTo q (conjScript _ (sectionPol p.val)) = applyTo _ (sectionPol (Labels.conjPol p.val)); rw [real_script,section_reads,section_reads,Labels.conj_value]
lemma bridge_real (g:ℝ){d:ℕ}(p:Field G d): bridge g (realField p) = Labels.realBar (bridge g p):=by
   apply Subtype.ext; apply Labels.eval_ext; intro v;
   change Labels.read _ (toCommon _ (realField p).val) = Labels.read _ (Labels.conjPol (toCommon _ p.val)); rw [radial_checks,Labels.conj_value,radial_checks]; exact real_script _ _
end Form
end YM.RG06.Continuum
