import YM.Integration.WilsonMarkedInheritedGaussianPlacement
import YM.Integration.WilsonMovingRunWickCoordinates

/-! Period-independent mean and covariance entries for the real original
shifted Gaussian, on the independently prescribed forest and every actual tag. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMarkedRelativeGaussianBudget
open Function Matrix Lattice Laurent Wilson Exterior Precision RG Next.Free UVExtension.Free Bloch
open WilsonCoeffUV Stationary Tree Work.F08 FormalBulk08 Flat Reef Jets AllOrder.Ker
open PhysicalNext.Repeat.Legato Comparison.RG02
open scoped Classical Matrix

variable {G:Gauge} {K:KernelChoices} {j t:ℕ}

private theorem booked {c f:Side} (S:StepData c f)(P:Flight j t)(L:Lodge P.patch)
    (h:P.patch.Branches K G)(hp:S.patch=P.patch)(hk:S.kernel=K)
    (row:PoleRows S.patch)(hr:HEq row (P.duo K.penalty).A0)(b σ:ℝ)
    (mean:∀v w,|Reef.pMean G K P c (Reef.floor K P L c) v w|≤b)
    (cov:∀v w,|(Reef.ferry P h L c).saddle.q v w|≤σ):
    ∃F:Forest S.ratio,HEq F (Reef.floor K P L c) ∧
      (∀v w,|Flat.rawMean G S F (Bloch.installed S.ratio row) v w|≤b) ∧
      (∀v w,|(Flat.testPrecision G S F P.wing)⁻¹ v w|≤σ) ∧
      Fintype.card (F.Free × G.ColorIndex)=c.val^4*Fintype.card (Lodge.selected G P.patch L):=by
  rcases S with ⟨p,k,size⟩
  change p=P.patch at hp
  change k=K at hk
  subst p
  subst k
  have f' : f=c*P.patch.L:=Subtype.ext size
  subst f
  obtain rfl:=eq_of_heq hr
  let F:=Reef.floor K P L c
  let T:=Flat.testPrecision G (primary P.patch K c) F P.wing
  have ht:=Reef.honey P h L c
  have inv:T⁻¹=(Reef.ferry P h L c).saddle.q:=
    left_inv_eq_right_inv (Matrix.nonsing_inv_mul T (isUnit_iff_ne_zero.mpr ht.1.det_pos.ne')) ht.2
  refine ⟨F,HEq.rfl,mean,?_,?_⟩
  · intro a d;change |T⁻¹ a d|≤_;rw [inv];exact cov a d
  · exact (Fintype.card_congr (Reef.pines (G:=G) F)).trans
      (WilsonMarkedInheritedGaussianPlacement.size P L G K c)

def mean (R:Run G)(N i per:ℕ)(F:Forest (R.family.path.levels.clock.op i per).ratio):=
  let V:=R.family.path.levels
  let S:=V.clock.op i per
  Flat.rawMean G S F (Bloch.installed S.ratio ((destination V N i).duo V.clock.kernel.penalty).A0)

theorem onRun (R:Run G)(N i:ℕ)(hi:i<N)(L:Lodge (R.family.path.levels.clock.op i 0).patch):
    let V:=R.family.path.levels
    let P:=destination V N i
    ∃b σ:ℝ, 1≤b ∧ 1≤σ ∧ ∀per:ℕ,
    ∃F:Forest (V.clock.op i per).ratio,
      HEq F (Reef.floor V.clock.kernel P L (R.family.side i per)) ∧
      (∀v w,|mean R N i per F v w|≤b) ∧
      (∀tag:(V.clock.op i per).Choices, ∀v w,
        |((RunFormalChain.fromRun R).step N i per hi).covariance F tag v w|≤σ) ∧
      Fintype.card (F.Free × G.ColorIndex)=(R.family.side i per).val^4*Fintype.card (Lodge.selected G P.patch L):=by
  intro V P
  let h:P.patch.Branches V.clock.kernel G:=(V.blocks i 0).branches
  obtain ⟨σ,hσ,price⟩:=WilsonMarkedInheritedGaussianKernel.covariance P L h
  obtain ⟨b,hb,drift⟩:=WilsonMarkedInheritedGaussianKernel.drift P L G V.clock.kernel P.legal (V.clock.adm i)
  refine ⟨b,σ,hb,hσ,fun per=>?_⟩
  let c:=R.family.side i per
  let S:=V.clock.op i per
  obtain ⟨F,orig,received,q,sizes⟩:=booked S P L h rfl rfl (P.duo V.clock.kernel.penalty).A0 HEq.rfl
    b σ (drift c) (price c).2
  refine ⟨F,orig,received,?_,sizes⟩
  intro tag a d
  have eq:=congrFun (congrFun (WilsonMovingRunWickCoordinates.precision R N i per hi F tag) ((Reef.pines F) a)) ((Reef.pines F) d)
  simp only [Matrix.submatrix_apply,Equiv.symm_apply_apply] at eq
  rw [eq]
  exact q _ _

end YM.Integration.WilsonMarkedRelativeGaussianBudget
end
