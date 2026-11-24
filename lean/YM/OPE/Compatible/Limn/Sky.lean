import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Inverse
import YM.OPE.Compatible.Porch.Halt
/-!
# Panel inverse budgets. positive gained from full Schur. arbitrary subsets. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Limn
open Function Filter Set MeasureTheory Lattice Laurent RG Matrix Precision Exterior Tree Push Push.AbsoluteSums
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{X Y:Type}{c f:Side}
open Next.SectorChange Next.SectorChange.Schur
variable {t r R B b ε:ℝ}{m:ℕ}
variable (S:StepData c f)(F: Forest S.ratio)
open Finset LinearMap Gaussian
section
variable {s:X→Site f} [Fintype X][DecidableEq X]{A:Matrix X X ℝ}
omit [DecidableEq X] in
lemma swings {B:Matrix X X ℝ}(h:B.IsSymm)(x y:X→ℝ): x ⬝ᵥ (B*ᵥ y)= y ⬝ᵥ (B*ᵥ x):=by rw [dotProduct_mulVec, dotProduct_comm, ←mulVec_transpose]; rw [show Bᵀ=B from h] -- direction
lemma Gape (h:A.PosDef)(hp:Pours A⁻¹ s s 0 R)(ht:0 < R): Gapped A R⁻¹:=by
      intro x; let t:= R⁻¹; have he':0 ≤ t:= inv_nonneg.mpr ht.le; let y:= A⁻¹*ᵥ x; have he:A*ᵥ y=x:=by rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ ((A.isUnit_iff_isUnit_det).mp h.isUnit),one_mulVec]
      have hh: x ⬝ᵥ y ≤ R*(x ⬝ᵥ x):=by apply le_trans (le_abs_self _) ((estimate hp x x).trans_eq ?_); rw[sumSq_dot];ring
      have hz :0 ≤ (x - t • y) ⬝ᵥ (A *ᵥ (x - t • y)):= star_trivial (x-t • y) ▸ h.posSemidef.dotProduct_mulVec_nonneg (x-t • y)
      rw [mulVec_sub, Matrix.mulVec_smul,he,dotProduct_sub,sub_dotProduct,sub_dotProduct,dotProduct_smul, dotProduct_smul,smul_dotProduct,smul_dotProduct,show y ⬝ᵥ x=x ⬝ᵥ y from dotProduct_comm .., swings (B:=A) (Matrix.isHermitian_iff_isSymm.mp h.isHermitian) y x,he] at hz; simp only [smul_eq_mul] at hz
      rw [sumSq_dot]; apply le_of_sub_nonneg
      have hv: t*R=1:= inv_mul_cancel₀ ht.ne'; change 0 ≤ x ⬝ᵥ (A *ᵥ x)-t * (x ⬝ᵥ x); nlinarith only [hz,hv,mul_le_mul_of_nonneg_left hh (mul_nonneg he' he'),show t*t*(R*(x ⬝ᵥ x))= t*(x ⬝ᵥ x) from (by rw [mul_assoc t,← mul_assoc t R,hv,one_mul])]
section
variable [Fintype Y][DecidableEq Y](z:Y↪ X)
noncomputable def Ext (z:Y↪X)(p:Y→ℝ): X→ℝ:= fun i=>∑ j:Y, (if z j=i then p j else 0)
omit [Fintype X][DecidableEq Y] in
lemma covers (p:Y→ℝ)(i):Ext z p (z i)=p i:=by unfold Ext; rw [Finset.sum_eq_single i]; simp only[if_true]; intro y _ h; rw [if_neg (fun H=>h (z.injective H))]; simp
omit [Fintype X][DecidableEq Y] in
lemma coversOut (p:Y→ℝ)(i:X)(h:¬∃ a,z a=i): Ext z p i=0:= Finset.sum_eq_zero fun j _=> if_neg (fun he=>h ⟨j,he⟩)
omit [DecidableEq Y] in
lemma entr (p:Y→ℝ)(q:X→ℝ): Ext z p ⬝ᵥ q=p ⬝ᵥ (q ∘ z):=by unfold dotProduct Ext; simp_rw[Finset.sum_mul,ite_mul,zero_mul]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_eq_single (z i)]; simp; intro x _ h; rw [if_neg h.symm];simp
omit [DecidableEq Y] in
lemma spired (h:Gapped A ε): Gapped (A.submatrix z z) ε:=by
        intro x; have hk (i): (A.submatrix z z *ᵥ x) i=(A*ᵥ Ext z x) (z i):=by rw [mulVec,mulVec,dotProduct_comm,dotProduct_comm (A (z i)), entr]; rfl
        have h':= h (Ext z x); rw[sumSq_dot,entr, show Ext z x ∘ z=x from funext (fun i=>covers ..), entr,show (A*ᵥExt z x) ∘ z=A.submatrix z z *ᵥ x from (funext fun i=>(hk i).symm)] at h'; rwa [sumSq_dot]
omit [DecidableEq X][DecidableEq Y] in
lemma sculpt (h:Pours A s s ε R) : Pours (A.submatrix z z) (s ∘ z) (s∘ z) ε R:=by
       have hk(p:X→ℝ)(hp:∀ i,0 ≤ p i): ∑ i:Y,p (z i) ≤ ∑ i,p i:= by rw [← Finset.sum_map _ z p];exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=> hp i)
       refine ⟨h.pos,fun i=>?_,fun j=>?_⟩
       · exact le_trans (hk (fun j=>Wisps.rate ε (separation (s (z i)) (s j))*|A (z i) j|) (fun i=>mul_nonneg (Wisps.rate_pos ..).le (abs_nonneg _))) (h.row (z i))
       exact le_trans (hk (fun i=>Wisps.rate ε (separation (s i) (s (z j)))*|A i (z j)|) (fun i=>mul_nonneg (Wisps.rate_pos ..).le (abs_nonneg _))) (h.col (z j))
end
end
end YM.OPE.Limn
