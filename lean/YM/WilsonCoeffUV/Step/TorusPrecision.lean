import YM.WilsonCoeffUV.Step.Square
/-! Exact closed value as log-coordinate polynomial. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV
open Wilson Lattice Laurent Exterior Bloch Matrix Precision Stationary RG Blue
open Next.Free FreeResolvent Tree Filter Metric Function
open PowerSeries
open scoped Topology ContDiff BigOperators
variable {G:Gauge} {c f : Side} (S:StepData c f)

private lemma q_compare {X Y : Type*} [DecidableEq X][DecidableEq Y][Fintype X][Fintype Y]
    (V:Matrix X Y ℝ)(B: Matrix X X ℝ)(P:Matrix Y X ℝ)(b q k)
    (h:B.transpose=B) (he:B*V = k • P.transpose * (1-P*V)) (u:X→ℝ)(v:Y→ℝ)
    (hQ: q= dotProduct u ((B+k • (P.transpose*P))*ᵥ u)/2 + dotProduct v ((V.transpose*B*V+k • ((1-P*V).transpose*(1-P*V)))*ᵥ v)/2)
    (hh:b=u+V*ᵥv) :
    dotProduct b (B*ᵥ b)/2+k*dotProduct (v-P*ᵥ b) (v-P*ᵥ b)/2=q := by
  subst b q
  let x := V*ᵥ v; let y:=(1 - P*V)*ᵥ v
  have ht: v-P*ᵥ (u+ V*ᵥ v)= y - P *ᵥ u := by unfold y; rw [sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, mulVec_add]; abel
  have hc : dotProduct x (B*ᵥ u)=dotProduct u (B*ᵥ x) := by conv_lhs=> arg 2; rw [←h];
                                                            rw [dotProduct_transpose_mulVec]
  have hx : dotProduct v ((V.transpose*B*V) *ᵥ v)=dotProduct x (B*ᵥ x) := by rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_transpose_mulVec,dotProduct_comm]
  have hy: dotProduct u (B*ᵥ (V*ᵥ v))=k*dotProduct (P*ᵥ u) y:= by rw [Matrix.mulVec_mulVec,he,←Matrix.mulVec_mulVec, Matrix.smul_mulVec, dotProduct_smul, dotProduct_transpose_mulVec,smul_eq_mul, dotProduct_comm]
  rw [ht,add_dotProduct,mulVec_add]
  simp only [add_mulVec, Matrix.smul_mulVec,dotProduct_add,dotProduct_smul,hx,smul_eq_mul]
  change (u ⬝ᵥ _ +u ⬝ᵥ (B*ᵥx) +(x ⬝ᵥ _ + _))/2+_= _
  rw [hc,show u ⬝ᵥ (B*ᵥx)=_ from (show u ⬝ᵥ (B*ᵥ x)=_ from hy),sub_dotProduct,dotProduct_sub,dotProduct_sub,dotProduct_comm y (P*ᵥ u),← Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,dotProduct_transpose_mulVec,dotProduct_transpose_mulVec]; unfold x y; ring

variable (G) (F:Forest S.ratio) (H Y:FreeResolvent.FaceRow) (Q:Matrix (Body 1 f) (Body 1 c) ℝ)

lemma residual_val (x:Lawn (Joint G f c)) :
    dotProduct x (penQuad G S*ᵥ x) = S.kernel.penalty * dotProduct (rightArm x - pressM G S*ᵥ leftArm x) (rightArm x - pressM G S*ᵥ leftArm x) := by
  simp only [penQuad,Matrix.smul_mulVec,←Matrix.mulVec_mulVec,dotProduct_smul,dotProduct_transpose_mulVec,sub_mulVec, left_hit,right_hit,smul_eq_mul]

lemma close_square (h: Inputs S Q (H.acts f) (Y.acts c)) (hy:(H.acts f).transpose= H.acts f) :
    let M:=extractV G S F Q
    loom (camSlice G S F M) (orbC (precisionC G f H)) + loom (panSlice G S F M) (orbC (penQuad G S)) =
      holdUp (Active G F) (orbC (precisionC G c Y))+bodyQ (Woods G c) (treeMatrix G S F H) := by
  intro M; classical
  let E := Active G F; let I:=reveal G S F
  let T := treeMatrix G S F H
  rw [←hold_loom, body_orb_C];
  simp only [loom,orbC, PowerSeries.map_C]; rw [←map_add,←map_add]; congr 1
  apply MvPolynomial.funext; intro w
  simp only [map_add];
  -- realm of scalars
  change MvPolynomial.eval _ (cord _ _) + MvPolynomial.eval _ (cord _ _) = MvPolynomial.eval _ (cord _ _) + MvPolynomial.eval _ (cord _ _)
  rw [cord_apply,cord_apply,cord_apply,cord_apply,orb_eval,orb_eval,orb_eval,orb_eval,left_hit,right_hit, residual_val, arm_pan]
  let x:=leftArm w; let y:=rightArm w; let b:=camSlice G S F M*ᵥ w
  rw [add_comm (dotProduct y _ /2)]
  have hx : b= I*ᵥ x+M*ᵥ y := by unfold b; rw [camber_tree, add_mulVec,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,left_hit,right_hit]
  obtain ⟨hz,hv⟩ := taken G S F H Y Q h
  apply q_compare (extractV G S F Q) (precisionC G f H) (pressM G S) b _ _ (kinetic_sym hy) hz (I*ᵥ x) y _ hx
  congr 1
  · rw [← full_write]
    have hh : dotProduct x (T *ᵥ x) = dotProduct (I*ᵥ x) (fullMatrix G S H *ᵥ (I*ᵥ x)) := (insertion.dot_compress (plant F) _ _ _).symm
    exact congrArg (fun x:ℝ=> x/2) hh
  rw [hv]
end YM.WilsonCoeffUV
