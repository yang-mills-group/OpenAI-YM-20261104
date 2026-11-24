import YM.Integration.WilsonGeometricPrimaryReturn
import YM.Integration.WilsonOriginalNullBareClean
import YM.Integration.WilsonCenteredFiledAtoms

/-! Read the physical top field on its own vacuum. The auxiliary cutoff sets only the test step. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullBarePanel
open Function Filter Finset Lattice RG Wilson Source Labels Extra.Histories Push.Local
open Next.Foundations Planned.AtomRegular ProjectorNext.Equivariance Trace.Physical.Germ
open PhysicalNext.Repeat.Legato Pert.Asymptotics Stationary Comparison.RG02
open WilsonCapturedPrimaryPaid WilsonCapturedPrimaryReading WilsonCenteredFiledAtoms
open scoped Topology Classical
variable {G:Gauge} {d:ℕ} (R:Run G) (F:Frame G d) (A:Hol G) (S:SectionData F)
theorem original (simple:G.Simple) (T:ℕ) {n per:ℕ}
    (wrapped:(eventually_atTop.mp (Trace.Physical.GermGraph.cut_flat R.family simple 0)).choose  ≤  n)
    (late:(eventually_atTop.mp (WilsonCapturedPrimaryOnRun.readouts R simple F A S T 0 1 le_rfl)).choose  ≤  n)
    (W:Rep G (R.family.side n per)) (date:W.p=R.family.path.levels.budget n)
    (support:1 ≤ W.p.supportExponent) (rank:d+1 ≤ W.p.order) (o:Site (R.family.side n per)) {μ κ fee mass:ℝ}
    (read:Readable A S W.p (R.family.side n per) μ)
    (U:Config G (R.family.side n per)→ℂ) (bank:Store W S A o κ fee
      (fun V=>(W.eval V:ℂ)*U V)) (pos:0 ≤ mass)
    (hearing:∀ V:Config G (R.family.side n per), flags W.p.threshold V=∅ → ‖U V‖ ≤ mass) :
    let gs:=regulatorRun R.family (n+1) per (n+1)
    let s:=(WilsonCapturedPrimaryDecoder.invoice F A d)*gs^T
    let wrap:=WilsonCapturedPrimaryCoreBill.wrapFee F A
    let gross:=2*s*(mass/gs^(grade T d 1)+μ*(wrap*fee)+fee)
    s*μ ≤ 1/2 →
    ∃ h:Coefficient F (R.family.side n per),h.Format o A W ∧ h.remBound o W κ fee ∧
      (∀ V,h.density o S W V=(W.eval V:ℂ)*U V) ∧
      F.coeffSize (projection F A W.p.threshold o h) ≤ gross ∧ F.coeffSize h.x ≤ gross+wrap*fee :=by
  intro gs s wrap gross small
  obtain ⟨h,form,rough,value⟩:=bank
  have size:0<gs:=inv_pos.mpr (Real.sqrt_pos.mpr
    (Overlay.beta_positive R.makes.wilson (N:=n+1) (m:=n+1) (p:=per) le_rfl))
  have sp:=pow_pos size (grade T d 1)
  have both:=WilsonGeometricPrimaryReturn.original F A S R simple T (N:=n+1) (per:=per)
    (Nat.lt_succ_self n) wrapped late W date support rank o h read form rough (div_nonneg pos sp.le) small
  refine ⟨h,form,rough,value,both ?_⟩
  intro V hv
  rw [reading,value,mul_div_cancel_left₀ _ (noFlagEval hv),div_mul_cancel₀ _ sp.ne']
  exact hearing V hv
end YM.Integration.WilsonOriginalNullBarePanel
