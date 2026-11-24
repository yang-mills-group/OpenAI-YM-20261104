import YM.Integration.WilsonOriginalProfileStrip
import YM.Integration.WilsonOlderFreshGraphCappedPrice

/-! A booked width for a fixed compound source. All retained degrees share one
payroll. At a date read the original stage order and power from the paid sheet. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonOriginalCompoundStrip
open Function Filter Finset Lattice RG RG.Shoot RG.Supply Wilson Precision Input Org
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato ThroughLaunch Next.Foundations Push.PriceCompiler
open QuadraticLocal QuadraticLocal.Advent
open scoped Classical
variable {G:Gauge}

structure Request (G:Gauge) where
  radius : KernelChoices → ℕ → ℕ → ℝ
  positive : ∀ K j H,0<radius K j H
  multiplier : ℕ → ℝ
  grows : ∀ H,0 < multiplier H
  entrance : KernelChoices → ℕ → Stage → ℕ

def partialWidth (Q:Request G)(K:KernelChoices)(j H:ℕ):ℝ:=Q.radius K j H/(16*Q.multiplier H)
def width (Q:Request G)(K:KernelChoices)(j H:ℕ):ℝ:=min 1 (partialWidth Q K j H)

private theorem width_pos (Q:Request G)(K:KernelChoices)(j H:ℕ):0<width Q K j H:=
  lt_min one_pos (div_pos (Q.positive K j H) (mul_pos (by norm_num) (Q.grows H)))

def programme (Q:Request G):WilsonOriginalProfileStrip.Menu G where
  cap:=partialWidth Q
  positive:=fun K j H=>div_pos (Q.positive K j H) (mul_pos (by norm_num) (Q.grows H))
  threshold:=Q.entrance
  bill:=fun K j A H=>∑ s∈Finset.range (j+2),WilsonOlderFreshGraphCappedPrice.factor
    (WilsonOlderFreshGraphCappedPrice.degree s A.power A.order) (width Q K j H/4)

def Filed (Q:Request G):WilsonLimitConstruction.FundedCompanySelection.Prediction G:=
  @WilsonOriginalProfileStrip.Filed G (programme Q)

theorem original (Q:Request G)(cap U:ℕ→ℕ)(mono:Monotone cap)(simple:G.Simple){ε:ℝ}(pos:0<ε):
    WilsonOriginalCourseSupplement.Award (@Filed G Q)
      (WilsonEmittedPositionSchool.funded.{u} cap U mono simple pos):=
  WilsonOriginalProfileStrip.original (programme Q) cap U mono simple pos

theorem date (Q:Request G)(R:Run G)(paid:Filed Q R.kit)(i H:ℕ)(fit:H≤R.alloy.B.a.clock.J i):
    let j:=R.alloy.B.a.clock.J i
    let K:=R.metals.p.kernel
    let μ:=width Q K j H
    Q.entrance K j (R.metals.p.profile j)≤(R.alloy.B.a.clock.factor j).val ∧
    0<μ ∧ μ≤1 ∧ μ≤Q.radius K j H/(16*Q.multiplier H) ∧
    Real.exp (μ⁻¹^2)≤R.alloy.B.a.clock.hatBeta i ∧
    ∀s:ℕ,s≤j+1→WilsonOlderFreshGraphCappedPrice.factor
      (WilsonOlderFreshGraphCappedPrice.degree s (R.alloy.B.a.budget i).power (R.alloy.B.a.budget i).order)
      (μ/4)≤budgetR R i:=by
  obtain ⟨entry,pos,one,small,beta,cash⟩:=WilsonOriginalProfileStrip.on_run (programme Q) R paid i H fit
  refine ⟨entry,pos,one,small,beta,?_⟩
  intro s hs
  let K:=R.metals.p.kernel
  let j:=R.alloy.B.a.clock.J i
  let A:=R.metals.p.profile j
  let μ:=width Q K j H
  have belongs:s∈Finset.range (j+2):=Finset.mem_range.mpr (by dsimp [j]; omega)
  have term:=Finset.single_le_sum (f:=fun k=>WilsonOlderFreshGraphCappedPrice.factor
      (WilsonOlderFreshGraphCappedPrice.degree k A.power A.order) (μ/4))
    (fun k _=>zero_le_one.trans (WilsonOlderFreshGraphCappedPrice.permanent _ (div_pos (width_pos Q K j H) (by norm_num)))) belongs
  have stage:=params_eq R.alloy.B.valid i
  have order:(R.alloy.B.a.budget i).order=A.order:=congr_arg Stage.order stage
  have power:(R.alloy.B.a.budget i).power=A.power:=congr_arg Stage.power stage
  rw [order,power]
  exact term.trans cash

end YM.Integration.WilsonOriginalCompoundStrip
