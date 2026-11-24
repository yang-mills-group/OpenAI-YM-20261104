import YM.OPE.Compatible.Woods.Rail
/-!
# Mean complete: includes rooting and lift gradient.

`Larger` here used to shorten proof; need physically on all sufficiently large stages. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Woody
open Function Filter Set Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08 Next.Free FreeResolvent
open scoped Topology BigOperators ComplexConjugate
variable {G: Gauge}{ι:Type*}{c f L:Side}{j: ℕ}{P:Patch}{C:KernelChoices}{η A s: ℝ}
lemma stratify {A: Row (TypeFace 2) (TypeFace 2)} {v: ℝ}{S:StepData c f}{W:Matrix (Body 1 f) (Body 1 c) ℝ}{D'}(H:Tree.Forest S.ratio)
    (hb:Inputs S W (A.acts f) D') (hL: Bid.Larger (G:=G) S)(hv:0<v)(hp:Gap (A.acts f) v):
    FreeResolvent.covariance G S H A * tensor G (S.kernel.penalty • (probe S).transpose) = tensor G (extracted S H W):=by
       obtain ⟨hV,hZ⟩:= stationed H W _ _ hb; let P:= (probe S).transpose; let K':= S.kernel.penalty; have hk: K'≠ 0:= S.kernel.penalty_pos.ne'
       have hh: baseMatrix S A *extracted S H W=K' • P :=by unfold baseMatrix; rw [Matrix.add_mul,hZ,Matrix.smul_mul,Matrix.mul_assoc,hV,Matrix.mul_sub,Matrix.mul_one,Matrix.mul_smul,smul_sub,smul_smul,mul_inv_cancel₀ hk,one_smul,add_sub_cancel]
       change _*tensor G (K' • P)= _; rw [← hh, AnalyticBridge.LocalGaussianLaws.Current.tensor_mul]; let T:= tensor G (extracted S H W)
       change _*(fullMatrix _ S A*T)= T; apply Matrix.ext_of_mulVec_single; intro i; rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, block_solve _ _ hL hv hp]; apply fixes; intro j; unfold T; rw [component_mul]; exact Precision.stays _ _ _
namespace Medal
variable (S: StepData c f) (h:Odd S.patch.L.val)(v: Train j)(B:Medal S.patch G S.kernel j)
lemma trueMean {W:Matrix (Body 1 f) (Body 1 c) ℝ}{D'}(hL:Bid.Larger (G:=G) S)(hk:4≤ j)(hp:Inputs S W ((pink S.kernel.penalty v).acts f) D'):
    installed S.ratio (B.highCross v)=tensor G (extracted S (forest S.ratio h) W):=by
       rw [B.rolled h v hk]
       obtain hb:= heart_heats _ S.kernel.penalty_pos hk (fun i:Train j=> i); obtain ⟨a,D,ha,_,hh⟩:=hb.1.funds; exact stratify _ hp hL ha ⟨fun w=> ((obey_band _ (hb.1.stock.whole v) (hh v) f).2 w).1⟩
end Medal
end YM.OPE.Woody
