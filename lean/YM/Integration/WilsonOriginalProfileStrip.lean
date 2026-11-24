import YM.Integration.WilsonOriginalSmallStrip
import YM.Integration.WilsonOriginalCourseSupplement

/-! The enrolled regular order and power are known on the original payroll
sheet before the length choice. They may enter the added coefficient bill. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonOriginalProfileStrip
open WilsonLimitConstruction.FundedCompanySelection
open Function Filter Finset Lattice RG RG.Shoot RG.Supply Wilson Precision Input Org
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato ThroughLaunch Next.Foundations Push.PriceCompiler
open QuadraticLocal QuadraticLocal.Advent
open scoped Classical
variable {G:Gauge}

structure Menu (G:Gauge) where
  cap : KernelChoices → ℕ → ℕ → ℝ
  positive : ∀ K j H,0<cap K j H
  threshold : KernelChoices → ℕ → Stage → ℕ
  bill : KernelChoices → ℕ → Stage → ℕ → ℝ

def booked (V:Menu G)(A:ℕ→Stage):WilsonOriginalSmallStrip.Menu G:=
  ⟨V.cap,V.positive,fun K j=>V.threshold K j (A j),fun K j h=>V.bill K j (A j) h⟩

def Filed (V:Menu G):Prediction G:=fun {M} {_} {A} _=>
  WilsonOriginalSmallStrip.Enrolled (booked V M.p.profile) M.p.kernel A.B.a

theorem prepaid (V:Menu G)(simple:G.Simple)(s:Sheet G)(M:MapPrices):
    WilsonFundedWindowMenu.Prepared (@Filed G V) s M:=
  WilsonOriginalSmallStrip.prepaid simple (booked V s.profile) s M

theorem on_run (V:Menu G)(R:Run G)(paid:Filed V R.kit)(i H:ℕ)(fit:H≤R.alloy.B.a.clock.J i):
    let j:=R.alloy.B.a.clock.J i
    let K:=R.metals.p.kernel
    let σ:=min 1 (V.cap K j H)
    V.threshold K j (R.metals.p.profile j)≤(R.alloy.B.a.clock.factor j).val ∧
    0<σ ∧ σ≤1 ∧ σ≤V.cap K j H ∧ Real.exp (σ⁻¹^2)≤R.alloy.B.a.clock.hatBeta i ∧
    V.bill K j (R.metals.p.profile j) H≤budgetR R i:=by
  exact ⟨paid.1 _,WilsonOriginalSmallStrip.on_run (booked V R.metals.p.profile) R paid i H fit⟩

theorem original (V:Menu G)(cap U:ℕ→ℕ)(mono:Monotone cap)(simple:G.Simple){ε:ℝ}(pos:0<ε):
    WilsonOriginalCourseSupplement.Award (@Filed G V)
      (WilsonEmittedPositionSchool.funded.{u} cap U mono simple pos):=
  WilsonEmittedPositionSchool.withSupplement.{u} (@Filed G V) (fun s _=>prepaid V simple s _) cap U mono simple pos

end YM.Integration.WilsonOriginalProfileStrip
