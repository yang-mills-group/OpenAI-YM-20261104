import YM.WilsonCoeffUV.Step.NoiseUnit

/-!
# Gluing full coordinates, no independent edge quotient

Common counting covariance identical over all physical logs, Wick on all
bonds with degeneracy, or only active and affine shift; exact unnormalized
quadratic. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV
open Wilson Lattice Laurent Exterior Bloch Matrix Precision Stationary RG Blue
open Next.Free FreeResolvent Tree Filter Metric Function
open PowerSeries
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {c f : Side}
section matrices
variable (G) (S:StepData c f)(F:Forest S.ratio)

abbrev reveal:= insertion (plant F (G:=G))
def camber (M:Matrix (Woods G f) (Woods G c) ℝ) := leftFlag (Woods G f) (Woods G c)+ M* rightFlag (Woods G f) (Woods G c)
-- shift both vars (identity on right)
def groundM (M:Matrix (Woods G f) (Woods G c) ℝ) : Matrix (Joint G f c) (Joint G f c) ℝ:= Matrix.fromBlocks 1 M 0 1

def extractV (Q: Matrix (Body 1 f) (Body 1 c) ℝ) := tensor G (extracted S F Q)

def overM := bridgeM (reveal G S F) (Woods G c)
def camSlice (M:Matrix (Woods G f) (Woods G c) ℝ) := (camber G M)* overM G S F
def panSlice (M:Matrix (Woods G f) (Woods G c) ℝ):= groundM G M * overM G S F

lemma camVec (M:Matrix (Woods G f) (Woods G c) ℝ) (x:Lawn (Joint G f c)): camber G M *ᵥ x=leftArm x+M*ᵥrightArm x := by rw [camber,add_mulVec,← Matrix.mulVec_mulVec,left_hit,right_hit]
lemma camIn (M:Matrix (Woods G f) (Woods G c) ℝ)(u:Lawn (Joint G f c)): leftArm (groundM G M*ᵥ u)= camber G M *ᵥ u ∧ rightArm (groundM G M *ᵥ u)=rightArm u := by
  have hx : u=Sum.elim (leftArm u) (rightArm u):= funext fun i=> by cases i <;> rfl
  rw [camVec]; constructor <;> ext i
  · conv_lhs => rw [hx];
    rw [groundM,Matrix.fromBlocks_mulVec]; simp [leftArm]
  conv_lhs=>rw [hx];
  rw [groundM,Matrix.fromBlocks_mulVec]; simp [rightArm]
lemma arm_ground (M:Matrix (Woods G f) (Woods G c) ℝ): leftFlag _ _ * groundM G M=camber G M ∧ rightFlag _ _ * groundM G M=rightFlag _ _ := by
  classical
  constructor <;> (apply Matrix.toLin'.injective; apply LinearMap.ext; intro u; change _*ᵥ u=_*ᵥ u; rw [← Matrix.mulVec_mulVec]);
  · rw [left_hit]; exact (camIn G M u).1
  rw [right_hit,right_hit]; exact (camIn G M u).2
lemma arm_pan (M: Matrix (Woods G f) (Woods G c) ℝ)(z) : panSlice G S F M *ᵥ z = Sum.elim (camSlice G S F M *ᵥ z) (rightArm z) := by
  unfold camSlice; ext i; cases i with
  | inl i=>
    rw [Sum.elim_inl]
    exact congr_fun (show leftArm (panSlice G S F M *ᵥ z)= _ from by unfold panSlice; rw [← left_hit,Matrix.mulVec_mulVec,←Matrix.mul_assoc, (arm_ground G M).1]) i
  | inr i=>
    rw [Sum.elim_inr];
    exact congr_fun (show rightArm (panSlice G S F M *ᵥ z)= _ from by unfold panSlice; rw [←right_hit,Matrix.mulVec_mulVec,←Matrix.mul_assoc,(arm_ground G M).2,overM,(flag_cast _ _).2,right_hit]) i
lemma camber_tree (M:Matrix (Woods G f) (Woods G c) ℝ): camSlice G S F M= reveal G S F*leftFlag _ _+ M*rightFlag _ _ := by rw [camSlice,camber,Matrix.add_mul, Matrix.mul_assoc,overM] ; rw [(flag_cast _ _).1,(flag_cast _ _).2]
lemma sweeps {A : FreeResolvent.FaceRow}(Q:Matrix (Body 1 f) (Body 1 c) ℝ) (Y:FreeResolvent.FaceRow)
    (hA:IsUnit (treeMatrix G S F A).det)(h:Inputs S Q (A.acts f) (Y.acts c)) :
    extractV G S F Q=reveal G S F * ((reveal G S F).transpose*extractV G S F Q) := by
  rw [extractV,←mean_map G S _ _ _ _ h hA, covariance]
  let I:=reveal G S F; let V:= extractV G S F Q; let P:= treeInverse G S F A
  have he : I.transpose*I=1 := by apply insertion.orthogonal; exact plant_inj F
  simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc (insertion _).transpose,he, Matrix.one_mul]

lemma matrix_form (K:Matrix (Woods G c) (Woods G c) ℝ) (p q:TreeVars G c)(hs:K.transpose=K): dotProduct p (K *ᵥ q)=dotProduct q (K*ᵥp) := link_kinetic K p q hs
-- algebra
lemma full_write {H : FreeResolvent.FaceRow} : fullMatrix G S H= precisionC _ _ H + S.kernel.penalty • ((pressM G S).transpose * pressM G S) := by rw [fullMatrix,baseMatrix,tensor_add,tensor_scale,pressM,tensor_mul, ← tensor_transpose]; rfl
lemma taken (H Y:FreeResolvent.FaceRow)(Q:Matrix (Body 1 f) (Body 1 c) ℝ)
    (h : Inputs S Q (H.acts f) (Y.acts c)) :
    let V:=extractV G S F Q; let R:=1-pressM G S*V
    precisionC G f H * V=S.kernel.penalty • (pressM G S).transpose * R ∧
    V.transpose * precisionC G f H * V+S.kernel.penalty • (R.transpose*R)=precisionC G c Y := by
  intro V R
  have he : R=tensor G (1- probe S* extracted S F Q) := by unfold R pressM V extractV; rw [←tensor_mul];
                                                            ext i j; rcases i,j with ⟨⟨x,a,b⟩,y,c,d⟩; by_cases he:b=d <;> simp [tensor,Matrix.one_apply,he]
  constructor
  · rw [he,pressM,show V=extractV G S F Q from rfl,extractV,precisionC,tensor_transpose,←tensor_scale, ←tensor_mul, ←tensor_mul]; rw [(stationed F Q _ _ h).2,(stationed F Q _ _ h).1, sub_sub_cancel, Matrix.smul_mul,Matrix.mul_smul,smul_smul,mul_inv_cancel₀ S.kernel.penalty_pos.ne',one_smul]
  unfold V extractV at *
  rw [he,precisionC,precisionC,tensor_transpose,←tensor_mul,←tensor_mul, tensor_transpose,← tensor_mul,←tensor_scale,← tensor_add]
  congr 1; exact action F Q (H.acts f) (Y.acts c) h

/-! Fundamental completion calculations on active directions. -/
end matrices
end YM.WilsonCoeffUV
