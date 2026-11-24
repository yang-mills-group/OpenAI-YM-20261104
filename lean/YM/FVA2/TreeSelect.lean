import YM.FVA2.TreeRank
import YM.PertExtension.OrbCovariance

/-!
# The inverse Hessian and the choice of tree/Faddeev slices on the quotient
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Inversion
open Finset Matrix Set Function Filter Lattice Wilson MS.Koszul MS.Native
open MS.Cylinder.Taylor PertExtension PertExtension.Orb GaussianScore Series Series.Radial
open Ends ArrayMap
open scoped Topology ContDiff Classical

variable {A : Type} [DecidableEq A] [Fintype A] (J:A→Prop)
variable {G:Gauge}

def extend_zero (G:Gauge) : Ends.Links G {x//J x} →ₗ[ℝ] Ends.Links G A where
  toFun x u := if h:J u then x ⟨u,h⟩ else 0
  map_add' x y := by funext u; by_cases h:J u <;> simp [h]
  map_smul' c x:= by funext u; by_cases h:J u <;> simp [h]

-- Caution: only one DecidablePred choice; use Classical uniformly here and in Orb's tree.
local notation "D" => extend_zero
omit [DecidableEq A] [Fintype A] in
lemma pickedL : pick (G:=G) J ∘ₗ D J G=LinearMap.id := by apply LinearMap.ext; intro f; funext i; change (D _ _ f i.val)=_; unfold extend_zero; simp only [LinearMap.coe_mk,AddHom.coe_mk,dif_pos i.property]; rfl
omit [DecidableEq A] [Fintype A] in
lemma pick_rest : pick (G:=G) J ∘ₗ D (fun i=>¬J i) G=0 := by apply LinearMap.ext; intro f; funext i; change D _ _ f i.val=0; unfold extend_zero; simp only [LinearMap.coe_mk, AddHom.coe_mk,dif_neg (show ¬¬J i.val from (not_not.mpr i.property))]
omit [DecidableEq A] [Fintype A] in
lemma completion (G:Gauge) : (D J G) ∘ₗ pick J + (D (fun i=>¬J i) G) ∘ₗ pick (fun i=>¬J i)=LinearMap.id := by
  apply LinearMap.ext; intro f; funext i; by_cases h:J i <;> simp [extend_zero,pick,h]
lemma pick_matrix [Fintype {x // J x}] (G:Gauge) (i : Ends.Z G {x//J x}) (j : Ends.Z G A) :
    coordinate (pick J : Ends.Links G A →ₗ[ℝ] _) i j= if (i.1.val,i.2)=j then 1 else 0 := by
  rw [coordinate_apply]; simpa [pick, projector_k] using coord_recover (i.1.val,i.2) j
lemma extend_matrix [Fintype {x // J x}] (G:Gauge) : (coordinate (D J G))ᵀ= coordinate (pick J) := by
  ext ⟨⟨i,h⟩,a⟩ ⟨j,b⟩; simp only [transpose_apply,coordinate_apply,projector_k]
  unfold extend_zero; by_cases H:j=i
  · subst j; simp [pick,h,priv,baseC,eq_comm]
  by_cases hu:J j <;> simp [pick,hu,priv,H,Ne.symm H]

variable {n:Side}
abbrev FP (G:Gauge)(J:OEdge n→Prop) :=
  (coordinate (pick J (G:=G)))*gradientGraph (G:=G) (root n)

/-- Tree-slice criterion. An admissible tree must kill all based gradients and
have no redundant fixing. -/
structure Choice (G:Gauge)(n:Side) where
  tree : OEdge n→Prop
  param : Matrix (Z G (Vert n)) (Z G {i//tree i}) ℝ
  left_tree : param * FP G tree = 1
  right_tree : FP G tree * param = 1

def canonical (G:Gauge)(h:Even n.val) : Choice G n := by
  let L:=treeIso G h; have hp : coordinate L.toLinearMap=FP G Branch := by
    rw [show L.toLinearMap= _ from invert_tree G h, coordinate_mul,dGraph]
  refine ⟨Branch,coordinate L.symm.toLinearMap,?_,?_⟩
  · rw [←hp,← coordinate_mul, show (L.symm.toLinearMap ∘ₗ L.toLinearMap)=LinearMap.id from LinearMap.ext (fun x=> L.symm_apply_apply _), coordinate_id]
  rw [← hp,← coordinate_mul,show (L.toLinearMap ∘ₗ L.symm.toLinearMap)=LinearMap.id from LinearMap.ext (fun x=> L.apply_symm_apply _),coordinate_id]

namespace Choice
variable (T:Choice G n)

abbrev Co := {i//¬T.tree i}
abbrev takeTree := coordinate (pick (G:=G) T.tree)
abbrev takeCo := coordinate (pick (G:=G) (fun i=>¬T.tree i))
abbrev fix : Matrix (Z G (Vert n)) (Z G (OEdge n)) ℝ := T.param*T.takeTree
abbrev includeCo := coordinate (D (fun i=>¬T.tree i) G)
abbrev hesT (G:Gauge) (n:Side) := costMatrix (priorRoot G n)
abbrev subH := T.includeCoᵀ * hesT G n * T.includeCo
abbrev gaugeMatrix (G:Gauge) (n:Side):= gradientGraph (G:=G) (root n)
lemma fixes : T.fix * gaugeMatrix G n = 1 := by unfold fix; rw [Matrix.mul_assoc]; exact T.left_tree
lemma direct : T.takeTree*T.includeCo=0 := by rw [takeTree,includeCo,← coordinate_mul,pick_rest, coord_zero]
lemma fixed_tree : T.takeTree*(1-gaugeMatrix G n * T.fix)=0 := by
  unfold fix
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc,show T.takeTree*_ * T.param= (1:Matrix _ _ _) from T.right_tree,Matrix.one_mul,sub_self]
lemma co_T : T.includeCoᵀ=T.takeCo := by exact extend_matrix (fun i=>¬T.tree i) G
lemma co_inv : T.includeCoᵀ*T.includeCo=1 := by rw [co_T,takeCo,includeCo,← coordinate_mul,pickedL,coordinate_id]
lemma finite_split : T.takeTreeᵀ*T.takeTree+T.includeCo*T.includeCoᵀ=1 := by
  rw [co_T, show T.takeTreeᵀ=coordinate (D T.tree G) from by rw [← Matrix.transpose_inj]; simp only [transpose_transpose]; exact (extend_matrix T.tree G).symm]
  change coordinate _ * coordinate (pick T.tree) + coordinate _ * coordinate (pick (fun i=>¬T.tree i))= _
  rw [← coordinate_mul, ← coordinate_mul,←coordinate_add,completion,coordinate_id]


lemma resolver :
    let U:=1-gaugeMatrix G n*T.fix; U=T.includeCo*T.includeCoᵀ * U := by
  intro U
  have he : U=(1:Matrix _ _ ℝ)*U:= (Matrix.one_mul _).symm
  nth_rw 1 [he]; rw [← T.finite_split,add_mul, Matrix.mul_assoc, show T.takeTree*U= _ from T.fixed_tree, Matrix.mul_zero, zero_add]

/-- Bootstrap inverses from one canonical gauge Hessian. -/
lemma makes {Q:Matrix (Z G T.Co) (Z G T.Co) ℝ} (hp:Q*T.subH=1) :
    (T.includeCo*Q*T.includeCoᵀ)*hesT G n = 1-gaugeMatrix G n*T.fix := by
  let U : Matrix (Z G (OEdge n)) (Z G (OEdge n)) ℝ:= 1-gaugeMatrix G n*T.fix
  let K:=gaugeMatrix G n
  have hx:= Ends.cost_kernel _ (prior_root_prop G n)
  have hu : hesT G n*U=hesT G n:= by unfold U; rw [mul_sub, mul_one,← Matrix.mul_assoc]; change _-hesT G n*gaugeMatrix G n*T.fix=_; rw [show hesT G n*K=0 from hx]; simp
  change _=U
  calc
    _ = T.includeCo*(Q*T.subH)*T.includeCoᵀ*U := ?_
    _ = _ := by rw [hp,Matrix.mul_one]; exact T.resolver.symm
  unfold subH
  simp_rw [Matrix.mul_assoc]; rw [← Matrix.mul_assoc T.includeCo T.includeCoᵀ U,← T.resolver,hu]

end Choice
open Choice
lemma canonical_co (G:Gauge)(he:Even n.val) :
    let T:=canonical G he
    T.subH=Orb.coefficientMatrix (baseChart G (Cotree n)) := by
  intro T -- expose binder issues
  let U:=D (fun i:OEdge n=>¬Branch i) G
  let V:=U.toContinuousLinearMap
  let S:=priorRoot G n
  have ht : -fiscal=S ∘ V := by
    funext x
    change -(energy (representative x)/2)=-(energy (liftLinks _)/2)
    congr; change Orb.liftLinks _=_; apply congr_arg liftLinks; funext i; change splitLink _ _ i=G.lieExp (U x i)
    unfold U extend_zero splitLink; by_cases H:Branch i <;> simp [H]
  have hz:=costs_comp V S (prior_root_prop G n).smooth
  change (coordinate U)ᵀ * costMatrix S * coordinate U=_; rw [show (coordinate U)ᵀ * costMatrix S * coordinate U=costMatrix (S ∘ V) from hz.symm,← ht,← neg_one_smul ℝ fiscal,costs_smul _ _ fiscal_smooth.contDiffAt]
  have hs (x : Dir G n): scoreDual x x = (fderiv ℝ (fderiv ℝ fiscal) 0) x x := by
    change score x x=_; rw [second_jet]; unfold jet
    norm_num [Nat.factorial, iteratedFDeriv_succ_apply_right, iteratedFDeriv_one_apply, Fin.init]; ring
  have hi : ContDiffAt ℝ ω (fiscal (G:=G) (n:=n)) 0:= fiscal_smooth.contDiffAt
  have hv (x y:Dir G n): scoreDual x y=(fderiv ℝ (fderiv ℝ fiscal) 0) x y:= by
    have hy : scoreDual x y=scoreDual y x := (saddle he).turns ..
    have HH:=hi.isSymmSndFDerivAt_of_omega x y
    have hh:=hs (x+y); simp only [map_add, LinearMap.add_apply, _root_.add_apply] at hh; rw [hs,hs,← hy,← HH] at hh; linarith
  ext i j
  simp_rw [Matrix.smul_apply, smul_eq_mul,neg_one_mul]
  change -(-fderiv ℝ (fun a=> fderiv ℝ fiscal a (priv i)) 0 (priv j))=scoreDual ((baseChart G (Cotree n)) i) ((baseChart G (Cotree n)) j)
  have hk:= (hi.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)
  rw [neg_neg,← show priv j= (baseChart G (Cotree n)) j from (base_at j).symm,base_at,hv,
    (hk.hasFDerivAt.clm_apply (hasFDerivAt_const (priv i) (0:Dir G n))).fderiv]
  simp; exact hi.isSymmSndFDerivAt_of_omega _ _

lemma inverse_wick (G:Gauge)(h: Even n.val) :
    let B:= baseChart G (Cotree n)
    let T:=canonical G h
    (show Matrix (Z G (Cotree n)) (Z G (Cotree n)) ℝ from T.subH) * Orb.covariance B h=1 := by
  intro b T
  rw [show T.subH= _ from canonical_co G h]
  ext i j
  let x := (saddle h).inverse (b.coord j)
  change (∑ k, score (b i) (b k) * b.coord k x) = _
  calc
    _ = ∑ k, scoreDual (b i) (b.coord k x • b k):= Finset.sum_congr rfl fun k _=> by rw [map_smul];change _=b.coord k x*score (b i) (b k);ring
    _ = scoreDual (b i) (∑ k, b.coord k x • b k) := by rw [map_sum]
    _ = score (b i) x := by rw [show (∑ k, b.coord k x • b k)=x from b.sum_repr x];rfl
    _ = scoreDual x (b i) := (saddle h).turns ..
    _ = b.coord j (b i) := congr_arg (fun l : Orb.Source G n=>l (b i)) (saddle h|>.applies _)
    _ = _ := by simp [Matrix.one_apply, Finsupp.single_apply]
namespace Choice
variable (T : Choice G n) (h:Even n.val)
local notation "δ" => T.fix
local notation "t" => T.takeTree
local notation "v" => T.includeCo
local notation "GA" => gaugeMatrix G n
local notation "M" => hesT G n
local notation "S" => T.subH
abbrev inverseCo : Matrix (Z G T.Co) (Z G T.Co) ℝ:= S⁻¹
abbrev Ctilt : Matrix (Z G (OEdge n)) (Z G (OEdge n)) ℝ:= (T.includeCo*T.inverseCo)*T.includeCoᵀ
lemma h_symm : Sᵀ=S := by unfold subH; rw [transpose_mul, transpose_mul,transpose_transpose, show Mᵀ=M from Ends.cost_symmetric _ (prior_root_prop ..), Matrix.mul_assoc]
lemma inv_symm : T.inverseCoᵀ=T.inverseCo:= by unfold inverseCo; rw [Matrix.transpose_nonsing_inv,h_symm]
lemma c_symm : T.Ctiltᵀ=T.Ctilt:= by unfold Ctilt; rw [Matrix.transpose_mul,Matrix.transpose_mul, inv_symm, Matrix.transpose_transpose,Matrix.mul_assoc]
lemma canonical_inv : (canonical G h).inverseCo= Orb.covariance (baseChart G (Cotree n)) h := by
  let B:=baseChart G (Cotree n)
  have he:=inverse_wick G h
  exact Matrix.inv_eq_right_inv he
lemma canonical_law : (canonical G h).Ctilt * M = 1-GA*(canonical G h).fix := by
  apply (canonical G h).makes
  apply _root_.mul_eq_one_comm.mpr
  change (show Matrix (Z G (Cotree n)) (Z G (Cotree n)) ℝ from (canonical G h).subH)*(show Matrix (Z G (Cotree n)) (Z G (Cotree n)) ℝ from (canonical G h).inverseCo)= _
  rw [canonical_inv]; exact inverse_wick G h
include h
lemma truly_inverse : T.inverseCo*T.subH=1 := by
  let E:=1-GA*T.fix
  let C:=(canonical G h).Ctilt
  have ht : S=T.includeCoᵀ*M*T.includeCo:= rfl
  have he : Eᵀ*M=M := by
    let Ω:=prior_root_prop G n
    unfold E; rw [transpose_sub,transpose_mul,transpose_one]; rw [Matrix.sub_mul,Matrix.one_mul]
    rw [Matrix.mul_assoc, show GAᵀ*M=0 from ?_,Matrix.mul_zero,sub_zero]
    rw [show M=Mᵀ from (Ends.cost_symmetric _ Ω).symm,← transpose_mul,
      show M*GA=0 from Ends.cost_kernel _ Ω, transpose_zero]
  let L: Matrix (Z G T.Co) (Z G T.Co) ℝ:= T.includeCoᵀ * (E*C*Eᵀ) * T.includeCo
  have hu : L*S=1 := by
    have hz : Eᵀ*(T.includeCo*T.includeCoᵀ)=Eᵀ:= by
      obtain hh:= congr_arg Matrix.transpose T.resolver
      rw [transpose_mul,transpose_mul,transpose_transpose] at hh; exact hh.symm
    have hm : δ*v=0:= by unfold fix; rw [Matrix.mul_assoc,T.direct,Matrix.mul_zero]
    have hv : E*v=v:= by unfold E; rw [Matrix.sub_mul, Matrix.one_mul,Matrix.mul_assoc,hm,Matrix.mul_zero,sub_zero]
    have hG : E*GA=0:= by unfold E; rw [Matrix.sub_mul, Matrix.one_mul,Matrix.mul_assoc,T.fixes,Matrix.mul_one,sub_self]
    calc
      _ = vᵀ * E * C * (Eᵀ * (v*vᵀ)) * M * v := by unfold L; rw [ht]; simp_rw [Matrix.mul_assoc]
      _ = vᵀ * (E*(1-GA*(canonical G h).fix)) * v := by
        rw [hz,show 1-GA*_=C*M from (canonical_law (G:=G) h).symm] -- syntax?
        simp_rw [Matrix.mul_assoc]; rw [← Matrix.mul_assoc Eᵀ,he]
      _ = _ := by rw [Matrix.mul_sub, Matrix.mul_one,← Matrix.mul_assoc E,hG,Matrix.zero_mul,
                       sub_zero, Matrix.mul_assoc, hv, T.co_inv]
  rw [show T.inverseCo=L from Matrix.inv_eq_left_inv hu, hu]

lemma actual_covariance : T.Ctilt * hesT G n = 1-gaugeMatrix G n*T.fix :=
   T.makes (T.truly_inverse h)
end Choice
end YM.FVA2.Inversion
