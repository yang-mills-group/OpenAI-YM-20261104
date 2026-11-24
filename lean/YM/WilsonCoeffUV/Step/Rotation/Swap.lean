import YM.Work.F05.Reindex
import YM.WilsonCoeffUV.Step.Ward.Invariance
/-!
# Auxiliary for the forest independence of W: match active counts,
spectator variables unchanged. No change-of-width assertions. Native on
finite tori.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Power.Freedom
open Wilson Lattice Laurent Exterior Bloch Matrix Precision Stationary RG Blue
open Next.Free FreeResolvent Tree Work.F05 Function PowerSeries
open scoped Topology ContDiff BigOperators
variable {c f : Side}{G:Gauge}(S:StepData c f)
section alg
variable {V W X':Type*} [Fintype V] [Fintype W] [Fintype X']
omit [Fintype X'] in
lemma usual_repack [DecidableEq V][DecidableEq W] (K:Matrix W W ℝ)(e:V ≃ W) :
    let P : Matrix W V ℝ := insertion (e:V→ W); let N:=K.submatrix e e
    K⁻¹=P * N⁻¹ * P.transpose := by
  intro P N
  unfold N
  have hp : P*P.transpose=1:= by
    have hx : P=(insertion (e.symm:W→V)).transpose := by
      ext1 i j; obtain ⟨k,rfl⟩ := e.surjective i
      simp [P,insertion,eq_comm]
    rw [hx,transpose_transpose]; exact insertion.orthogonal _ e.symm.injective
  rw [Matrix.inv_submatrix_equiv,← insertion.compress (e:V→W)]
  change _ = P * (Pᵀ * K⁻¹ * P)* Pᵀ
  rw [← Matrix.mul_assoc P,← Matrix.mul_assoc P P.transpose,hp,one_mul, Matrix.mul_assoc,hp,mul_one]
lemma bridgeArms [DecidableEq V][DecidableEq W][DecidableEq X'] (P:Matrix V W ℝ) (x:Lawn (W ⊕ X')) :
    leftArm (bridgeM P X'*ᵥx)=P*ᵥleftArm x ∧ rightArm (bridgeM P X'*ᵥx)=rightArm x := by
  constructor
  · rw [← left_hit, Matrix.mulVec_mulVec,(flag_cast X' P).1,← Matrix.mulVec_mulVec,left_hit]
  rw [← right_hit, Matrix.mulVec_mulVec,(flag_cast X' P).2,right_hit]
lemma across_body [DecidableEq V][DecidableEq W][DecidableEq X'] (K:Matrix W W ℝ)(e:V≃W) :
    loom (bridgeM (insertion (e:V→ W)) X') (bodyQ X' K) = bodyQ X' (K.submatrix e e) := by
  let P: Matrix W V ℝ := insertion (e:V→ W)
  rw [body_orb_C,body_orb_C,loom,map_C]; congr 1
  apply MvPolynomial.funext; intro x
  change MvPolynomial.eval _ (cord (bridgeM P _) _) = _
  simp only [cord_apply,left_hit,orb_eval]
  rw [(bridgeArms P x).1]; congr 1; exact insertion.dot_compress _ _ _ _
lemma across_read [DecidableEq V][DecidableEq W][DecidableEq X'] {K:Matrix W W ℝ}(h:K.transpose=K)(e:V≃W) (P:Ink (W⊕X')) :
    let N:= K.submatrix e e
    Wick X' K⁻¹ P=Wick X' N⁻¹ (loom (bridgeM (insertion (e:V→ W)) X') P) := by
  intro N
  rw [bridge_rail]
  have he: train (path (U:=X')) = RingHom.id (Ink X') := by
    apply serial_ext (by simp) _ (by simp)
    intro p; induction p using MvPolynomial.induction_on with
    | C a=> exact train_real ..
    | add v w a b=> simp_rw [map_add,a,b]
    | mul_X p i H=> simp only [map_mul,H]; congr 1; apply train_path
  have hK: K⁻¹.transpose=K⁻¹ := by rw [transpose_nonsing_inv,h]
  rw [W_linear _ _ hK (show N⁻¹.transpose=N⁻¹ by simp only [transpose_nonsing_inv,N,transpose_submatrix,h]) (usual_repack K e) P,he,RingHom.id_apply]
end alg

section wardrobe
variable {B T : Forest S.ratio}
def stripe (e:B.Free ≃ T.Free) : Matrix (Active G T) (Active G B) ℝ:= insertion (onKey (G:=G) e)
-- Work.F05 and here compare counting, not unequal volume logs.
lemma v_exchange (e:B.Free ≃ T.Free) (w:Lawn (Active G B)) :
    vcloth S T G (stripe S e *ᵥ w)=index e (vcloth S B G w) := by
  funext i; obtain ⟨j,rfl⟩:= e.surjective i
  rw [index_apply]
  ext x
  change (insertion (onKey (G:=G) e)*ᵥ w) (onKey (G:=G) e (j,x)) = _
  simp [mulVec,insertion,dotProduct,eq_comm]
  rfl
lemma primalSweeps (Q : Matrix (Body 1 f) (Body 1 c) ℝ) :
    let M:=extractV G S B Q; let I:=reveal G S B
    M=I*(I.transpose*M) := by
  intro M I
  refine testers fun u v=>congr_arg (dotProduct u) (Eq.symm ?_)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  unfold M extractV; apply projects
  intro i; rw [component_mul]; exact stays B Q _
end wardrobe
end YM.WilsonCoeffUV.Power.Freedom
