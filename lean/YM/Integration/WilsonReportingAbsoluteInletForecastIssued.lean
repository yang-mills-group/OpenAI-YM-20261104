import YM.Integration.WilsonReportingAbsoluteInletForecastReciprocal

/-! Select one before-period calibration threshold. At each later regulator
the forecast evaluates the same independently filed physical kinetic action
at all dates; no choice of marks or interpolation enters its file. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingAbsoluteInletForecastIssued
open Filter RG Wilson Pert.Asymptotics PhysicalNext.Repeat.Legato
open WilsonReportingAbsoluteInletNativeDates WilsonReportingAbsoluteInletNativeInvoice
open WilsonReportingAbsoluteInletForecastRate WilsonReportingAbsoluteInletForecastReciprocal
open scoped Classical Topology
variable {G:Gauge}
universe u

theorem selected (R:Run G) (simple:G.Simple) (p:ℕ) {Scene:ℕ→ℕ→Type u}
    (law:∀N per,ℕ→Scene N per→Prop) (read:∀N per,Scene N per→ℕ→ℝ)
    (docket:∀ᶠ k:ℕ in atTop,∀N per,k≤N→(∃S:Scene N per,law N per k S) ∧
      ∀S:Scene N per,law N per k S→∀j,k≤j→j<N→
        |regulatorRun R.family N per j/regulatorRun R.family N per (j+1)-read N per S j|≤
          (R.family.path.levels.clock.hatBeta j)^exponent (p+2)):
    ∃ (k₀:ℕ) (a:ℕ→ℕ→ℕ→ℝ),(∀N per,k₀≤N→∃S:Scene N per,law N per k₀ S ∧
      ∀j,a N per j=read N per S j) ∧ InversePrice R p (fun N per j=>(a N per j)⁻¹):=by
  obtain ⟨k₀,buy⟩:=eventually_atTop.mp docket
  have issued:=buy k₀ le_rfl
  let a:=fun N per j=>if h:k₀≤N then read N per (Classical.choose (issued N per h).1) j else 1
  refine ⟨k₀,a,?_,inverse R simple p a ?_⟩
  · intro N per hi
    exact ⟨_,Classical.choose_spec (issued N per hi).1,fun j=>by simp only [a,dif_pos hi]⟩
  · filter_upwards [eventually_ge_atTop k₀] with k past N per j kj jn
    have hi:k₀≤N:=past.trans (kj.trans jn.le)
    have S:=Classical.choose_spec (issued N per hi).1
    simpa only [a,dif_pos hi] using (issued N per hi).2 _ S j (past.trans kj) jn
end YM.Integration.WilsonReportingAbsoluteInletForecastIssued
