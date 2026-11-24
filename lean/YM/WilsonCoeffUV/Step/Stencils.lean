import YM.WilsonCoeffUV.Step.Pad
import YM.WilsonCoeffUV.Flat.Width
import YM.Work.F03.Flat
import YM.Branch.Covariant

/-! Torus unmasked flat-germ inputs, real shared predictor, no quotient.
Exactly Wilson and physical counting and Hessians. Off-tree projection comes
only later (construct bulk on the unmarked full logs, gauge period proof).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV
open Wilson Lattice Laurent Exterior Bloch Matrix Precision Stationary RG Blue
open Next.Free FreeResolvent Tree Filter Gauge Metric
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {c f : Side}

abbrev Woods (G:Gauge)(c:Side) := FreeResolvent.Slot G c 1
abbrev TreeVars (G:Gauge)(c:Side) := Lawn (Woods G c)

/-- native real logarithmic directions to links. -/
def cloth (G:Gauge)(n:Side) : fieldDir G n 1 ≃L[ℝ] TreeVars G n:= LinearEquiv.toContinuousLinearEquiv {
  toFun:=flatten
  invFun:= fun p b=> WithLp.toLp 2 (fun i=> p (FreeResolvent.ix b i))
  left_inv:=fun _=> rfl
  right_inv:=fun _=> rfl
  map_add':=fun _ _=>rfl
  map_smul':=fun _ _=>rfl }

def mantle (x:TreeVars G c) := represent ((cloth G c).symm x)
lemma placed (v:fieldDir G c 1) : mantle (flatten v)=represent v:= rfl
lemma mantle_zero : mantle (0: TreeVars G c)=1 := by rw [mantle,map_zero,link_one]
lemma mantle_cont : Continuous (mantle (G:=G) (c:=c)) := by
  apply Continuous.comp (show Continuous represent from ?h) (ContinuousLinearEquiv.continuous (cloth G c).symm)
  case h=> unfold represent increment collect; fun_prop
lemma mantle_green (e : Edge (Site c)) : ContDiff ℝ ω (fun x:TreeVars G c=>G.mat (mantle x e)) := (Work.F03.represent_smooth _).comp (cloth G c).symm.contDiff

def eWilson (v:TreeVars G c) := Wilson.energy (mantle v)
def precisionC (G:Gauge) (c:Side) (H: FreeResolvent.FaceRow) : Matrix (Woods G c) (Woods G c) ℝ := tensor G (Precision.K (H.acts c))
-- raw width-independent top
lemma link_kinetic (K:Matrix (Woods G c) (Woods G c) ℝ) (u v:TreeVars G c) (hh:K.transpose=K) : dotProduct u (K*ᵥ v)=dotProduct v (K*ᵥ u) := by
  conv_lhs => arg 2; rw [← hh];
  rw [dotProduct_transpose_mulVec]
lemma kinetic_sym {H: FreeResolvent.FaceRow} (hh : (H.acts c).transpose=H.acts c) : (precisionC G c H).transpose=precisionC G c H := by rw [precisionC,tensor_transpose]; rw [Precision.K,transpose_mul,transpose_mul, transpose_transpose,hh, Matrix.mul_assoc]
lemma W_green : Green (eWilson (G:=G) (c:=c)) := by
  unfold Green eWilson Wilson.energy; apply ContDiffAt.sum; intro e _; apply Work.F03.price_smooth (A:=fun x=> faceValue (mantle x) e)
  exact (Push.writes _ _).comp (f:=fun x=> (cloth G c).symm x) 0 (cloth G c).symm.contDiff.contDiffAt

-- absolute hessian Wilson rank two via limit on physical directions
lemma density_hill {H: FreeResolvent.FaceRow}(h:H.acts c=1)(u v:TreeVars G c) : dotProduct u (precisionC G c H *ᵥ v)=
    ∑ j:Face (Per c), inner ℝ (Work.F03.faceCurl j ((cloth G c).symm u)) (Work.F03.faceCurl j ((cloth G c).symm v)) := by
  let x:= dColor G c 1 ((cloth G c).symm u); let y:= dColor G c 1 ((cloth G c).symm v)
  have hs : dotProduct u (precisionC G c H *ᵥ v)= dotProduct (flatten x) (flatten y) := by
    rw [component_dot,component_dot]; apply Finset.sum_congr rfl; intro i _; rw [precisionC,component_mul, Precision.K,h,Matrix.mul_one,
        ← Matrix.mulVec_mulVec,dotProduct_transpose_mulVec]; apply dotProduct_comm
  rw [hs,flat_dot]; exact (Equiv.sum_comp (Equiv.prodCongr (Equiv.refl (Site c)) plaqEquiv) (fun i=> inner ℝ (x i) (y i))).symm
lemma w_jets {H: FreeResolvent.FaceRow}(h:H.acts c=1) :
    eWilson (0:TreeVars G c)=0 ∧ fderiv ℝ eWilson (0:TreeVars G c)=0 ∧ ∀ i j:TreeVars G c,
     iteratedFDeriv ℝ 2 eWilson 0 ![i,j]=dotProduct i (precisionC G c H*ᵥ j) := by
  apply Work.F03.hessian_of_limit (W_green.of_le (by simp)) ?l ?a (fun i j=>link_kinetic _ i j (kinetic_sym (by rw [h]; simp)))
  case l=>
    intro x; let v:=(cloth G c).symm x
    rw [density_hill h,Finset.sum_div]; simp_rw [eWilson,Wilson.energy,Finset.sum_div,mantle,map_smul]
    exact tendsto_finsetSum _ fun i _=> by
        rw [real_inner_self_eq_norm_sq]; apply Work.F03.price_limit (V:=fun t:ℝ=>faceValue (represent (t • v)) i) _ (Work.F03.face_deriv i v)
        rw [zero_smul]; exact Push.stroll_zero (G:=G) ..
  case a=> intro x y z; rw [add_dotProduct]

section actual
variable (G) (S:StepData c f)
-- arbitrary tags picked from same law. cost selected at unscaled logs.
def tac : S.Choices := Classical.arbitrary _
abbrev Joint (G:Gauge)(f c:Side) := Woods G f ⊕ Woods G c
def jointPen (x:Lawn (Joint G f c)) := noiseTaylor S (mantle (rightArm x)) (mantle (leftArm x)) (tac S)
def pressM := tensor G (probe S)
def penQuad : Matrix (Joint G f c) (Joint G f c) ℝ :=
    let R:= rightFlag (Woods G f) (Woods G c) - pressM G S * leftFlag _ _
    S.kernel.penalty • (R.transpose*R)
lemma pressAct (x:TreeVars G f): pressM G S *ᵥ x= flatten (Bid.bills S ((cloth G f).symm x)) := by
  funext y; obtain ⟨a,j,b⟩:=y
  exact congr_fun (component_mul _ x b) (a,j)
lemma terrain (x:Lawn (Joint G f c)) :
    rightFlag _ _ *ᵥ x- (pressM G S * leftFlag _ _)*ᵥ x = flatten (Work.F03.residual S ((cloth G c).symm (rightArm x),(cloth G f).symm (leftArm x))) := by rw [right_hit,← Matrix.mulVec_mulVec,left_hit,pressAct]; rfl
lemma penSym : (penQuad G S).transpose=penQuad G S := by unfold penQuad; simp
lemma hessianPen (x:Lawn (Joint G f c)) : dotProduct x (penQuad G S*ᵥ x)= S.kernel.penalty * ∑ i, let v:=Work.F03.residual S ((cloth G c).symm (rightArm x),(cloth G f).symm (leftArm x)); inner ℝ (v i) (v i) := by
  rw [penQuad,Matrix.smul_mulVec,←Matrix.mulVec_mulVec,dotProduct_smul, dotProduct_transpose_mulVec, sub_mulVec, terrain, flat_dot]; rfl
lemma penSmooth (h:S.patch.Branches S.kernel G): Green (jointPen G S) := by
  unfold Green jointPen noiseTaylor
  refine ContDiffAt.mul contDiffAt_const (ContDiffAt.sum (fun i _=>?_));
  have he : Green fun x : Lawn (Joint G f c)=> (cloth G f).symm (leftArm x) := by
    simp_rw [←left_hit]; apply (cloth G f).symm.contDiff.contDiffAt.comp 0 (board _)
  let M (x:Lawn (Joint G f c)):= (cloth G f).symm (leftArm x)
  have hm : M 0=0:= by unfold M; rw [show leftArm (0:Lawn (Joint G f c))=0 from rfl,map_zero]
  have ht : Green (fun x : Lawn (Joint G f c)=> G.mat (S.prediction (mantle (leftArm x)) (tac S) i)) := by
    have hh : ContDiffAt ℝ ω (fun v=> G.mat (S.prediction (represent v) (tac S) i)) (M 0) := by rw [hm]; exact Push.prediction_cont S h i _
    exact hh.comp (f:=M) 0 he
  apply Work.F03.price_smooth (A:=fun x: Lawn (Joint G f c)=> mantle (rightArm x) i* (S.prediction (mantle (leftArm x)) (tac S) i)⁻¹)
  simp only [G.mat_mul,G.mat_inv];
  apply ContDiffAt.mul ?_ ((starL ℝ).contDiff.contDiffAt.comp 0 ht)
  simp_rw [←right_hit]; exact (mantle_green _).contDiffAt.comp 0 (board _)
lemma pen_jets (h:S.patch.Branches S.kernel G) :
    jointPen G S 0=0 ∧ fderiv ℝ (jointPen G S) 0=0 ∧ ∀ i j,
     iteratedFDeriv ℝ 2 (jointPen G S) 0 ![i,j]=dotProduct i (penQuad G S*ᵥ j) := by
  apply Work.F03.hessian_of_limit ((penSmooth G S h).of_le (by simp))
  · intro x; rw [hessianPen]; unfold jointPen mantle; simp_rw [←right_hit,←left_hit,Matrix.mulVec_smul,map_smul]; apply Work.F03.noise_limit h (tac S) ((cloth G c).symm _,(cloth G f).symm _)
  · intros; rw [add_dotProduct]
  intro i j; conv_lhs => arg 2; rw [← penSym G S];
  rw [dotProduct_transpose_mulVec]
end actual

end YM.WilsonCoeffUV
