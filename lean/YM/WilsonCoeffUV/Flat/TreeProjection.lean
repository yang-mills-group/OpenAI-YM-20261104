import YM.WilsonCoeffUV.Flat.CompletedJoint
import YM.Push.FREE_RESOLVENT.GaugeProjection
import YM.UVNext.PRICED_KERNELS.Trees
/-!
# Return to the tree slice used by the formal Wick rule
Counting matrices. In particular kernel of the joint projection includes
joint (all-site) gauges. Does NOT put full-site gauge zero in the tree,
which would eliminate modes we must integrate. No a.e. momentum statements.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV
open Function Lattice RG Laurent Exterior Bloch Matrix Precision Stationary Tree
open UVNext.PricedKernels (rootAt hiker)
open scoped Topology BigOperators ComplexConjugate
variable {G:Gauge} {c f L : Side} {S : StepData c f}
open FreeResolvent

lemma to_patron {j k : ℕ} (A : Matrix (Body k f) (Body j L) ℝ) : tensor G A = patron G A := by
  refine testers fun v x=>congr_arg (dotProduct v) (funext ?_)
  intro i; rcases i with ⟨i,t,b⟩
  rw [patron_fee]
  exact congr_fun (component_mul A x b) (i,t)

lemma tensor_mul {r s t : ℕ} (A : Matrix (Body r c) (Body s f) ℝ) (B : Matrix (Body s f) (Body t L) ℝ) :
    tensor G (A*B)=tensor G A*tensor G B := by rw [to_patron,to_patron,to_patron,patron_mul]
lemma tensor_zero {r s : ℕ} : tensor G (0:Matrix (Body r c) (Body s f) ℝ)=0 := by ext i j; simp [tensor]
lemma tensor_add {r s : ℕ} (A B : Matrix (Body r c) (Body s f) ℝ) : tensor G (A+B)=tensor G A+tensor G B := by
  ext i j; unfold tensor; simp; split <;> simp
lemma tensor_scale {r s : ℕ} (A : Matrix (Body r c) (Body s f) ℝ) (k : ℝ) : tensor G (k • A)= k • tensor G A := by
  ext i j; unfold tensor; simp [mul_ite]

lemma parent_apply (S : StepData c f) (u : Vec G c 0) (i : Site f) j :
    (tensor G (rootAt S.ratio) *ᵥ u) (i,Exterior.vac,j) = u (S.ratio.parent i,Exterior.vac,j) := by
  change component (tensor G _ *ᵥ u) j (i,Exterior.vac)= _
  rw [component_mul,rootAt,LinearMap.toMatrix'_mulVec]; rfl
lemma climb (T : Forest S.ratio) (u : Vec G f 1) : tensor G (hiker S T) *ᵥ u=FreeResolvent.potential T u := by
  funext ⟨x,b,i⟩; rw [vac_only b]; unfold FreeResolvent.potential
  change component (tensor G _ *ᵥ u) i (x,Exterior.vac) = _
  rw [component_mul,hiker,LinearMap.toMatrix'_mulVec]; rfl
lemma fix_rt (S : StepData c f) (u : Vec G f 0) (i : Site c) j :
    (tensor G (fixRoot S) *ᵥ gradient u) (i,Exterior.vac,j)= u (S.ratio.embed i,Exterior.vac,j) - (curryG G S *ᵥ u) (i,Exterior.vac,j) := by
  rw [curry_at]
  change component (tensor G _ *ᵥ gradient u) j (i,Exterior.vac) = _
  unfold gradient; rw [component_mul,component_mul]; exact psi_proj S _ _
lemma climb_grad (T : Forest S.ratio) (u : Vec G f 0) (i : Site f) j :
    potential T (gradient u) (i,Exterior.vac,j) = u (S.ratio.embed (S.ratio.parent i),Exterior.vac,j) - u (i,Exterior.vac,j) := by
  unfold FreeResolvent.potential gradient; rw [component_mul,telescopes,T.hike_root]; rfl
lemma gradient_A (v : Vec G f 0) : gradientA G f v=gradient v := by rw [first_uniform,gradient,to_patron,patron_fee]

-- Turn parameters. Use only a copied root parameter and within-block
-- integral. All prices of these maps at a step can be post-L.
def turning (G:Gauge) (T : Forest S.ratio) :=
    tensor G (hiker S T) * butt G c f -
    tensor G (rootAt S.ratio) * (brim G c f + tensor G (fixRoot S) * butt G c f)

def toTree (G:Gauge) (T : Forest S.ratio) :=
    butt G c f + tensor G (d 0 f) * turning G T

def restrictTree (G:Gauge) (T : Forest S.ratio) := FreeResolvent.reduce G S T * toTree G T

lemma upper_apply (G:Gauge) (T : Forest S.ratio) (v : Corn (Bodies G c f)) :
    turning G T *ᵥ v = potential T (butt G c f *ᵥ v) -
    tensor G (rootAt S.ratio) *ᵥ (brim G c f *ᵥ v + tensor G (fixRoot S) *ᵥ (butt G c f *ᵥ v)) := by
  rw [turning,sub_mulVec,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,Matrix.add_mulVec,← Matrix.mulVec_mulVec,climb]

lemma leaf_turn (T : Forest S.ratio) (v : Corn (Bodies G c f)) : Vanishes T (toTree G T *ᵥ v) := by
  let x := butt G c f *ᵥ v
  let u := brim G c f *ᵥ v + tensor G (fixRoot S) *ᵥ x
  rw [toTree, add_mulVec,← Matrix.mulVec_mulVec,upper_apply, Matrix.mulVec_sub]
  rw [add_sub_assoc']
  intro i e h
  rcases e with ⟨a,b⟩
  change component (representative S T x) i (a,coord b) -component (gradient (tensor G (rootAt S.ratio)*ᵥ u)) i (a,coord b)=0
  have he : component (representative S T x) i (a,coord b)=0 := onto_slice T x i (a,b) h
  rw [he,gradient,component_mul,d_sites]
  change 0-(((tensor G (rootAt _) *ᵥ u) (a+step b,Exterior.vac,i) - (tensor G (rootAt _) *ᵥ u) (a,Exterior.vac,i)))=0
  rw [parent_apply,parent_apply,T.trunk_internal h,sub_self,sub_zero]

lemma coordinate_elim (T : Forest S.ratio) : toTree G T=insertion (plant (G:=G) T)*restrictTree G T := by
  refine testers fun u v=> congr_arg (dotProduct u) ?_
  rw [restrictTree,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,projects T _ (leaf_turn T v)]

lemma work_clock (u : Vec G f 0) :
    butt G c f *ᵥ (spreadM S *ᵥ u)= -gradient u ∧ brim G c f *ᵥ (spreadM S *ᵥ u) = -(curryG G S *ᵥ u) := by
  rw [parliament,helmet_ear,gradient_A,helmet_butt,helmet_brim,sliceX,sliceY]
  exact ⟨rfl,rfl⟩

lemma kill_all (T : Forest S.ratio) : toTree G T * spreadM (G:=G) S=0 := by
  refine testers fun i v=>congr_arg (dotProduct i) ?_
  rw [← Matrix.mulVec_mulVec,toTree, Matrix.add_mulVec,← Matrix.mulVec_mulVec, zero_mulVec]
  have hu := work_clock (S:=S) v
  rw [hu.1]
  have hp : turning G T *ᵥ (spreadM S *ᵥ v)=v := by
    rw [upper_apply, ← climb,hu.1,hu.2, Matrix.mulVec_neg,Matrix.mulVec_neg,climb]
    funext ⟨x,b,j⟩; rw [vac_only b]
    change -FreeResolvent.potential T (gradient v) _ - (tensor G (rootAt S.ratio) *ᵥ _) (x,Exterior.vac,j)=_
    rw [climb_grad,parent_apply]; simp only [Pi.add_apply,Pi.neg_apply,fix_rt]; ring
  rw [hp]; exact neg_add_cancel _

lemma fortune_p (T : Forest S.ratio) : tensor G (probe S)*toTree G T = -fortune G S := by
  refine testers fun u v=> congr_arg (dotProduct u) ?_
  let V := butt G c f *ᵥ v
  let B := brim G c f *ᵥ v
  let k := turning G T *ᵥ v
  let C := tensor G (d 0 c)
  have hy i j : k (S.ratio.embed i,Exterior.vac,j)= -(B (i,Exterior.vac,j) + (tensor G (fixRoot S) *ᵥ V) (i,Exterior.vac,j)) := by
    unfold k; rw [upper_apply,Pi.sub_apply,parent_apply]
    have he := roots_pinned T V j
    rw [S.ratio.embed_parent, show FreeResolvent.potential T (butt G c f *ᵥ v) (S.ratio.embed i,Exterior.vac,j)=0 from congr_fun he (i,Exterior.vac),zero_sub]; rfl
  have hx : tensor G (probe S) *ᵥ gradient k= -(C *ᵥ (B+tensor G (fixRoot S) *ᵥ V)) := by
    funext ⟨x,a,j⟩
    change component (G:=G) (tensor G (probe S) *ᵥ gradient k) j (x,a) = - component (G:=G) (C *ᵥ (B+tensor G (fixRoot S) *ᵥ V)) j (x,a)
    rw [gradient,component_mul,component_mul,root_gradient]; unfold C; rw [component_mul]
    have he : centered S (component k j)= -component (B+tensor G (fixRoot S) *ᵥ V) j := by
      funext ⟨x,b⟩; rw [vac_only b]; exact hy x j
    rw [he,Matrix.mulVec_neg]; rfl
  rw [← Matrix.mulVec_mulVec,toTree, Matrix.add_mulVec,← Matrix.mulVec_mulVec, Matrix.mulVec_add, fortune, bondsM]
  rw [show tensor G (probe S) *ᵥ (tensor G (d 0 f) *ᵥ (turning G T *ᵥ v))=_ from hx]
  rw [probe,tensor_add,tensor_mul, Matrix.add_mulVec,← Matrix.mulVec_mulVec,
      ← to_patron,← to_patron, Matrix.neg_mulVec,Matrix.add_mulVec,← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, Matrix.neg_mulVec, Matrix.mulVec_add]
  change tensor G (mean S) *ᵥ V + _ + -(C *ᵥ B + C *ᵥ (tensor G (fixRoot S) *ᵥ V))=-( -(tensor G (mean S) *ᵥ V) + C *ᵥ B)
  unfold C B V; abel

lemma removable (T : Forest S.ratio) (B : Bed) : frontR G S B=(restrictTree G T)ᵀ*treeMatrix G S T B.metric*restrictTree G T := by
  classical
  let H := B.metric
  let P := toTree G T
  let Q := tensor G (Precision.K (H.acts f))
  let D := tensor G (d 0 f)
  let R := tensor G (probe S)
  have he : Q*D=0 := by unfold D Q; rw [← tensor_mul,K_kills,tensor_zero]
  have hf : Dᵀ*Q=0 := by unfold D Q; rw [tensor_transpose,← tensor_mul,K_orthogonal,tensor_zero]
  have hh : Pᵀ*Q*P=posting G S B := by
    unfold P toTree; rw [transpose_add,transpose_mul,Matrix.add_mul];
    change (_+(turning G T)ᵀ*Dᵀ*Q)*(_+D*_) = _
    rw [Matrix.mul_assoc (turning G T)ᵀ,hf,Matrix.mul_zero,add_zero,Matrix.mul_add,← Matrix.mul_assoc _ D, Matrix.mul_assoc _ Q D, he, Matrix.mul_zero, Matrix.zero_mul, add_zero]
    unfold Q; rw [to_patron]; rfl
  have hv : fullMatrix G S H=Q+S.kernel.penalty • (Rᵀ*R) := by
    rw [fullMatrix,baseMatrix,tensor_add,tensor_scale,tensor_mul, ← tensor_transpose]
  have hz : Pᵀ*(Rᵀ*R)*P=(fortune G S)ᵀ*(fortune G S) := by
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.mul_assoc _ R P, show R*P= _ from fortune_p T, transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  rw [show frontR G S B=Pᵀ*fullMatrix G S H*P from ?_]; swap
  · unfold frontR; rw [hv,Matrix.mul_add, Matrix.mul_smul,Matrix.add_mul,Matrix.smul_mul, hz,hh]
  unfold P; rw [coordinate_elim T,transpose_mul, show treeMatrix G S T B.metric= (insertion (plant (G:=G) T))ᵀ* fullMatrix G S H *insertion (plant T) from (insertion.compress (plant T) (fullMatrix G S H)).symm]
  simp only [Matrix.mul_assoc]

lemma onto (T : Forest S.ratio) : ∃ V : Matrix (Bodies G c f) (Active G T) ℝ, restrictTree G T*V=1 := by
  classical
  let I := insertion (plant (G:=G) T)
  let D := tensor G (fixRoot S)
  let Q : Matrix (Bodies G c f) (Active G T) ℝ := fun i j=> Sum.elim (fun x=> I x j) (fun x=>-(D*I) x j) i
  have he : butt G c f * Q = I := by
    rw [helmet_butt]; ext i j; exact congr_fun (sliceX _ _ ℝ (fun i=>Q i j)) i
  have hv : brim G c f * Q = -(D*I) := by
    rw [helmet_brim]; ext i j; exact congr_fun (sliceY _ _ ℝ (fun i=>Q i j)) i
  have hh : tensor G (hiker S T) * I =0 := by
    refine testers fun u v=> congr_arg (dotProduct u) ?_
    rw [Matrix.zero_mulVec,← Matrix.mulVec_mulVec,climb]
    funext ⟨i,b,j⟩
    apply hike_zero; intro z hz
    change (I *ᵥ v) (z.1,coord z.2,j) = 0
    unfold I; refine Finset.sum_eq_zero fun w _=> ?_
    change (if plant T w = (z.1,coord z.2,j) then 1 else 0) * _ = 0
    rw [if_neg ?_,zero_mul]; intro h
    apply w.1.property
    rw [show w.1.val=z from Prod.ext (congr_arg (fun i : Lines G f 1=>i.1) h) ((coord_iff ..).mp (congr_arg (fun i : Lines G f 1=>i.2.1) h))]; exact hz
  have hu : turning G T * Q=0 := by rw [turning,Matrix.sub_mul,Matrix.mul_assoc,he,Matrix.mul_assoc,Matrix.add_mul,Matrix.mul_assoc,he,hv,hh]; unfold D; simp
  refine ⟨Q,?_⟩
  rw [restrictTree,toTree,Matrix.mul_assoc,Matrix.add_mul,he,Matrix.mul_assoc,hu,Matrix.mul_zero,add_zero]
  change Iᵀ*I=1
  ext i j; simp only [Matrix.mul_apply,I,insertion,transpose_apply,Matrix.of_apply,Matrix.one_apply,ite_mul,mul_ite]
  by_cases h : i=j <;> simp [h, (plant_inj T).eq_iff]

-- Abstract projection of an inverse; no spectral or determinant bound after L used in this identity
lemma project_factor {α β γ:Type} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (T : Matrix β β ℝ) (P : Matrix β α ℝ) (U : Matrix α β ℝ) (X : Matrix γ α ℝ) (Y : Matrix α γ ℝ)
    (V : Matrix α α ℝ) (hp : P*U=1) (hx : P*Y=0) (hr : IsUnit (X*Y).det)
    (hv : V*(Pᵀ*T*P+ Xᵀ*X)=1) : P*V*Pᵀ*T=1 := by
  set W := U-Y*((X*Y)⁻¹*(X*U))
  have hh : P*W=1 := by unfold W; rw [Matrix.mul_sub,← Matrix.mul_assoc,hx,hp,Matrix.zero_mul,sub_zero]
  have hg : X*W=0 := by unfold W; rw [Matrix.mul_sub,← Matrix.mul_assoc,← Matrix.mul_assoc,mul_nonsing_inv _ hr, Matrix.one_mul,sub_self]
  calc
    _ = P * V * ((Pᵀ*T*P+ Xᵀ*X)*W) := by rw [Matrix.add_mul, Matrix.mul_assoc _ P, Matrix.mul_assoc Xᵀ,hh,hg,Matrix.mul_zero,add_zero,Matrix.mul_one, Matrix.mul_assoc (P*V)]
    _ = _ := by rw [Matrix.mul_assoc P V,← Matrix.mul_assoc V,hv,Matrix.one_mul,hh]

lemma projecting (T : Forest S.ratio) (t:S.Choices) (B:Bed) (hp : S.patch.Branches S.kernel G)
    (V:Matrix (Bodies G c f) (Bodies G c f) ℝ) (hv : V*(frontR G S B+ (postroom S t (inch S.patch.L))ᵀ*(postroom (G:=G) S t (inch S.patch.L)))=1) :
    restrictTree G T * V * (restrictTree G T)ᵀ * treeMatrix G S T B.metric=1 := by
  classical
  obtain ⟨U,hU⟩ := onto (G:=G) T
  refine project_factor _ _ U (postroom (G:=G) S t (inch S.patch.L)) (spreadM (G:=G) S) V hU ?_ ?_ ?_
  · rw [restrictTree,Matrix.mul_assoc,kill_all,Matrix.mul_zero]
  · rw [fired S t hp]; exact (grenade_safe _ (inch_pos _)).det_pos.ne'.isUnit
  rw [removable T] at hv; exact hv
end YM.WilsonCoeffUV
