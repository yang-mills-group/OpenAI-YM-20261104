import YM.XSpace.CoverProjector
import YM.FiniteVolumeClosure.A0bOriginals.Bare
/-! # Image covariance, including self contractions

Both the orbit projection and normalization of Hessian matter!
`image_rule` charges exactly one image per line in addition to the
ordinary cover line with the correct sign. Tree gauge covariance in
potential variables alone does *not* have this property.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace
open Function Set Filter Lattice Wilson MeasureTheory Matrix
open scoped Topology Matrix.Norms.Frobenius InnerProductSpace BigOperators Matrix ContDiff

namespace Regulator
variable (R : Regulator) (G : Gauge)

def flipA (A : Pot G R.side) (e : R.LEdge) := -A (R.antipode e)

def halfTurn (p : FKey G R.side) : FKey G R.side := ((-(p.1.1+step p.1.2.val.1+step p.1.2.val.2),p.1.2),p.2)

@[simp] lemma turn_half (p : FKey G R.side) : R.halfTurn G (R.halfTurn G p)=p := by
  unfold halfTurn
  rw [show -(-(p.1.1 + step p.1.2.val.1 + step p.1.2.val.2) + step p.1.2.val.1 + step p.1.2.val.2) = p.1.1 by simp; abel]

def mirror := Matrix.of fun i j:FKey G R.side=>if j=R.halfTurn G i then (1:ℝ) else 0

lemma mirror_apply (x : FKey G R.side→ℝ) : R.mirror G *ᵥ x = x ∘ R.halfTurn G := by
  ext i; simp [mirror,mulVec,dotProduct]
lemma mirror_symm : (R.mirror G).IsSymm := by
  ext i j
  by_cases h : i=R.halfTurn G j
  · simp [mirror,h]
  have he : j ≠ R.halfTurn G i := fun t=> h (by rw [t,R.turn_half]); simp [mirror,h,he]

lemma flip_field (A : Pot G R.side) : R.mirror G *ᵥ fields G R.side A = fields G R.side (R.flipA G A) := by
  rw [mirror_apply]; funext p
  let x:=p.1.1; let a:=p.1.2.val.1; let b:=p.1.2.val.2
  change curl A (-(x+step a+step b)) a b p.2= curl (R.flipA G A) x a b p.2; apply congr_arg (fun v : G.Color => v p.2)
  simp only [curl,flipA,antipode]
  rw [show (-(x+step a+step b))+step a= -(x+step b) by abel,
    show (-(x+step a+step b))+step b= -(x+step a) by abel,add_right_comm x (step b)]; abel

lemma mirror_comm : kernel G R.side * R.mirror G=R.mirror G * kernel G R.side := by
  let K := kernel G R.side; let M:= R.mirror G
  have he : K * (M*K)=M*K := by
    apply Matrix.ext_iff_mulVec.mpr; intro x; rw [← Matrix.mulVec_mulVec]; rw [← Matrix.mulVec_mulVec]
    obtain ⟨b,h⟩:=project_into G R.side x; change K *ᵥ x = _ at h; unfold M; rw [h, flip_field]; exact project_fixes ..
  have hh:= congr_arg Matrix.transpose he; rw [Matrix.transpose_mul,Matrix.transpose_mul,show Kᵀ=K from kernel_symm ..,show Mᵀ=M from mirror_symm .., Matrix.mul_assoc,he] at hh; exact hh.symm

namespace Tree
variable {R} (T : R.Tree) {G}

def treePotential (A : R.Potential G) (v : R.Vertex) : G.Color :=
  if h : v = R.root then 0 else
    let a : R.Nonroot:=⟨v,h⟩; let p:=T.parent a; let l:=T.edge a
    treePotential A p + (if R.src l=p then A l else -A l)
termination_by T.depth v
decreasing_by exact T.lower _

lemma treePotential_tie (A : R.Potential G) (v : R.Nonroot) :
    T.treePotential A (R.dst (T.edge v))-T.treePotential A (R.src (T.edge v))=A (T.edge v) := by
  have hp : T.treePotential A v.val = T.treePotential A (T.parent v)+(if R.src (T.edge v)=T.parent v then A (T.edge v) else -A (T.edge v)) := by rw [treePotential,dif_neg v.property]
  rcases T.joins v with ⟨h,j⟩|⟨h,j⟩
  · rw [h] at hp; rw [h,j,hp]; simp
  rw [j,h,hp]; simp [h,(T.parent_ne v).symm]

lemma tree_replace (A : R.Potential G) : ∃ B : T.Array G,
    fields G R.side (T.periodic G B)=fields G R.side (R.liftA G A) := by
  let w:= T.treePotential A
  let C (l : R.Link) := A l - (w (R.dst l)-w (R.src l))
  let B (l : T.Mobile) := C l.val
  let u:= w ∘ R.vertex
  have he (e : R.LEdge) : R.liftA G (T.injection G B) e = R.liftA G A e - grad u e := by
    have hx (v : R.Link) : R.liftA G (T.injection G B) v.val= R.liftA G A v.val - grad u v.val := by
      rw [R.liftA_link,R.liftA_link]; change T.injection G B v=C v
      by_cases h : v∈T.ties
      · obtain ⟨p,-,rfl⟩:=Finset.mem_image.mp h; rw [injection_tie]; unfold C w; rw [treePotential_tie]; simp
      exact T.injection_mobile B ⟨v,h⟩
    have h := hx (R.link e)
    change R.liftA G (T.injection G B) (R.edgeRep e)= _ at h
    change _ = R.liftA G A (R.edgeRep e)-grad u (R.edgeRep e) at h
    rcases R.edgeRep_cases e with hh|hh
    · rwa [hh] at h
    rw [hh,R.liftA_anti, R.liftA_anti] at h
    have hz : grad u (R.antipode e)= - grad u e := by
      simp only [grad, u, antipode, R.vertex_neg,Function.comp_apply]; rw [show -(e.1+step e.2)+step e.2 = -e.1 by abel,R.vertex_neg, neg_sub]
    rw [hz,neg_sub_neg] at h; rw [neg_eq_iff_eq_neg] at h; rw [h,neg_sub]
  have hv : T.periodic G B = R.liftA G A-grad u := funext he
  refine ⟨B,?_⟩; rw [hv]; funext p
  simp [fields,field,curl_sub,curl_grad]

variable (G)
local notation "n" => R.side

def rows : Matrix (FKey G n) (T.Idx G) ℝ := Matrix.of fun i j=> fields G n (T.periodic G (T.basisT G j)) i

lemma rows_read (v : T.Idx G → ℝ) : T.rows G *ᵥ v=fields G n (T.periodic G ((T.basisT G).equivFun.symm v)) := by
  ext i; simp [Module.Basis.equivFun_symm_apply, rows,mulVec,dotProduct,map_sum,map_smul,Finset.sum_apply,mul_comm]

lemma fixes_rows : R.mirror G*T.rows G=T.rows G ∧ kernel G n*T.rows G=T.rows G := by
  constructor <;> apply Matrix.ext_iff_mulVec.mpr <;> intro x <;> rw [← Matrix.mulVec_mulVec,T.rows_read]
  · rw [flip_field]
    congr 1; funext e; rw [flipA]; exact Eq.trans (congr_arg Neg.neg (R.liftA_anti _ _)) (neg_neg _)
  exact project_fixes ..

lemma into_rows (x : FKey G n → ℝ) : ∃ v : T.Idx G → ℝ, ((1 + R.mirror G)*kernel G n)*ᵥ x = T.rows G *ᵥ v := by
  rw [← Matrix.mulVec_mulVec,Matrix.add_mulVec, Matrix.one_mulVec]
  obtain ⟨p,h⟩:= project_into G n x; rw [h,flip_field,← map_add]
  let X := p+R.flipA G p
  let b (l : R.Link):= X l.val
  have he (e) : X (R.antipode e)= -X e := by unfold X flipA; simp
  have hv : R.liftA G b=X := by
    funext e; rcases R.edgeRep_cases e with h|h
    · simp [liftA,h,b,link]
    simp [liftA,h,b,link,R.antipode_free e,he]
  obtain ⟨v,hv'⟩:=T.tree_replace b
  refine ⟨(T.basisT G).equivFun v,?_⟩; rw [rows_read,LinearEquiv.symm_apply_apply, hv',hv]

lemma gram : (T.rows G)ᵀ*T.rows G = (2:ℝ) • T.precision G := by
  ext i j
  let A := T.periodic G (T.basisT G i); let B:= T.periodic G (T.basisT G j)
  let s:=∑ p, inner ℝ (field A p) (field B p)
  have hp : T.precision G i j=s/2 := T.flat_hessian.2.2 _ _
  simp only [Matrix.smul_apply,smul_eq_mul,hp, Matrix.mul_apply]
  rw [show (2:ℝ)*(s/2)=s by ring]; unfold s
  change (∑ x : FKey G n,(field A x.1 x.2)*(field B x.1 x.2))=_
  rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun x _=>?_ ; simp [PiLp.inner_apply]; exact Finset.sum_congr rfl fun j _=> mul_comm .. -- ]

def treeCov := T.rows G * T.covariance G * (T.rows G)ᵀ

theorem image_matrix : T.treeCov G = (1+ R.mirror G) * kernel G n := by
  let L:= T.rows G; let W:=T.covariance G; let P:=kernel G n; let M:=R.mirror G
  let C:=T.treeCov G; let D:=(1+M)*P
  have hu : L*W* T.precision G=L := by rw [Matrix.mul_assoc]; rw [show W*T.precision G=1 from Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (T.precision_pos G).det_pos.ne')]; simp
  have hC : C*L=(2:ℝ) • L := by
    unfold C treeCov
    change L*W*Lᵀ*L=_; rw [Matrix.mul_assoc _ Lᵀ L,T.gram, Matrix.mul_smul,hu]
  have he : C * D = (2:ℝ) • D := by
    apply Matrix.ext_iff_mulVec.mpr; intro x; rw [← Matrix.mulVec_mulVec,Matrix.smul_mulVec]; obtain ⟨v,hv⟩:= T.into_rows G x
    change D *ᵥ x = L *ᵥ v at hv
    rw [hv,Matrix.mulVec_mulVec,hC,Matrix.smul_mulVec]
  have hp : Dᵀ=D := by
    change ((1+M)*P)ᵀ=_; rw [Matrix.transpose_mul,Matrix.transpose_add, Matrix.transpose_one, show Pᵀ=P from kernel_symm .., show Mᵀ=M from R.mirror_symm G]
    unfold D; rw [Matrix.mul_add,Matrix.mul_one,Matrix.add_mul, Matrix.one_mul,R.mirror_comm G]
  have hf : Cᵀ=C := by unfold C treeCov; rw [Matrix.transpose_mul,Matrix.transpose_mul,Matrix.transpose_transpose,show Wᵀ=W from T.covariance_symm G,Matrix.mul_assoc]
  have ht : D*L=(2:ℝ) • L := by unfold D; rw [Matrix.mul_assoc,T.fixes_rows G|>.2,Matrix.add_mul,Matrix.one_mul, T.fixes_rows G|>.1,two_smul]
  have hx := congr_arg Matrix.transpose he
  rw [Matrix.transpose_mul,hp,hf, Matrix.transpose_smul,hp] at hx
  apply smul_right_injective _ (two_ne_zero (α:=ℝ))
  calc (2:ℝ) • T.treeCov G = D*C := by
           unfold C treeCov; change _ = D*(L*W*Lᵀ); rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,ht,Matrix.smul_mul,Matrix.smul_mul]
       _ = _ := hx

theorem image_rule (a b : FKey G n) : T.treeCov G a b=kernel G n a b + kernel G n (R.halfTurn G a) b := by
  rw [image_matrix,Matrix.add_mul,Matrix.one_mul]; simp [Matrix.mul_apply, mirror, ite_mul]
end Tree
end Regulator
end YM.XSpace
