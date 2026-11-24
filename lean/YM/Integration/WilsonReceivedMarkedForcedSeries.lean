import YM.Integration.WilsonReceivedMarkedAperture
import YM.Integration.SelectedCofactorJointBudget

/-! The compulsory contribution of the received marked input on its actual
incoming representation. Each nonzero term retains the complete compatible
minor and selects one genuine original compulsory inventory. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReceivedMarkedForcedSeries
open Function Filter Finset MeasureTheory Lattice RG Wilson Precision Marker Multi Exterior Tree
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric PhysicalNext.Repeat.Legato Comparison.RG02 Integral
open Actual Order Push.SectorMeasure Push.AbsoluteSums NativeTasteCoveredCofactor
open SelectedCofactorJointBudget WilsonReceivedMarkedCofactor
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {ι : Type} [DecidableEq ι] [Fintype ι] {Γ : Census ι}
    (R : Run G) {J : Request ι} {A : NumericSchedule R.family J}
    (d : LocalFormal.Datum R.family Γ) {H : AnalyticInput J A d} {η : ℝ}
    (I : FullPreparedInputAt H η) (x : IndependentTests J.tests)
local notation "P" => I.carrier.rep
local notation "X" => testInclusion J.tests x
local notation "D" => I.prepared.remainder.leaf (X)
local notation "w" => fun v => H.inputRadii v/H.kernelCosts v
local notation "p" => A.inputNorm d.level
local notation "pay" => (Fintype.card ι:ℝ)*(forcedDivisor R.family (d.level+1)*I.forcedPrice)
local notation "c" => MarkedPackets.uniformModelCost J.inputPacketRankCap (Fintype.card ι) (A.admittedCost d.level)*
    Real.exp ((Fintype.card ι:ℝ)*I.regularPrice)
local notation "Fine" => Config G (R.family.side (d.level+1) d.period)

def entry (U : Fine) (i : ℕ × Finset ℕ) :=
  carried R d I x U*term (D) U i

/-- The support of the distinguished real marked address, the remaining
vacuum- and mark-carrying rows and the live physical flags are all literal. -/
theorem incidence (U : Fine) (i : ℕ × Finset ℕ) (live : entry R d I x U i≠0) :
    i.1∈i.2 ∧ CoveredSignedCofactors.Pinned
      (fun j=>((P).activities.forced j).support) (fun j=>((P).activities.forced j).inventory)
      (flags (P).p.threshold U) i.1 (i.2.erase i.1) := by
  apply cofactor_support (D) U
  intro gone
  exact live (by simp only [entry,term,gone,mul_zero])

theorem paid (hi : Retained.NativeIntake I)
    (hs : R.family.path.levels.clock.forcedAllowance (d.level+1)+pay≤1) (U : Fine) :
    Summable (entry R d I x U) ∧
    compulsory R d I x U=(Real.exp ((P).exponent U):ℂ) • ∑' i,entry R d I x U i ∧
    SumBudget (fun i : ℕ × Finset ℕ=>(p).mass ((P).activities.forced i.1).support
      (Poly.price (w) (entry R d I x U i))) ((c)*pay) := by
  have hw v : 0<(w) v := div_pos (H.input_radius_positive v) (H.kernel_positive v)
  have hcoeff := (WilsonReceivedMarkedCofactor.price R d I x U).2
  have hn : 0≤c := (Poly.nonnegative hw _).trans hcoeff
  let B := I.prepared.remainder_price
  have one := support_price B H.kernel_positive hi.reserved hs x U
  have bill : SumBudget (fun i : ℕ × Finset ℕ=>(p).mass ((P).activities.forced i.1).support
      (Poly.price (w) (entry R d I x U i))) ((c)*pay) := by
    apply budget_mono (budget_scale hn one) (fun i=>mul_nonneg (Real.exp_nonneg _) (Poly.nonnegative hw _))
    intro i
    change Real.exp _ * Poly.price (w) ((carried R d I x U)*term (D) U i) ≤ c*(Real.exp _*_)
    calc
      _ ≤ Real.exp _ * ((c)*Poly.price (w) (term (D) U i)) :=
        mul_le_mul_of_nonneg_left ((Poly.multiplication hw _ _).trans
          (mul_le_mul_of_nonneg_right hcoeff (Poly.nonnegative hw _))) (Real.exp_nonneg _)
      _ = _ := mul_left_comm _ _ _
  have simpler := budget_mono bill (fun i=>Poly.nonnegative hw (entry R d I x U i))
    (fun i=>(p).loMass _ _ (Poly.nonnegative hw _))
  have joint := (Poly.budgeted hw simpler.2.1 (fun i=>le_refl (Poly.price (w) (entry R d I x U i)))).1
  obtain ⟨parts,all,exactSum⟩ := relative_series B H.kernel_positive hi.reserved hs x U
  letI : IsTopologicalSemiring (Poly Γ) :=
    { toContinuousAdd := inferInstance, toContinuousMul := inferInstance }
  let row (i : ℕ) := (D).contents.each i U-scalarRow (P) U i
  have cof (i) : Summable (cofactor (D) U i) := parts i
  have rows : Summable (fun i => row i*∑' s,cofactor (D) U i s) := all
  have stated : forcedClusterError (D) U=NativeTasteCoveredCofactor.series (D) U := exactSum
  have expand : (∑' i,entry R d I x U i)=carried R d I x U*NativeTasteCoveredCofactor.series (D) U := by
    rw [joint.tsum_prod]
    calc
      _ = ∑' i,carried R d I x U*(row i*∑' s,cofactor (D) U i s) := by
        apply tsum_congr
        intro i
        simp only [entry,term,←mul_assoc]
        change (∑' s, (carried R d I x U * row i) * cofactor (D) U i s) = _
        rw [(cof i).tsum_mul_left,mul_assoc]
      _ = _ := rows.tsum_mul_left _
  refine ⟨joint,?_,bill⟩
  rw [expand,←stated]
  simp only [compulsory,carried,forcedNumerator,Handoff.legacyCarrier,mul_smul_comm,mul_assoc]

/-- The original late date is chosen before every cutoff, period, intake,
test, aperture or signed occurrence. -/
theorem original (hG : G.Simple) (J : Request ι) (A : NumericSchedule R.family J) :
    ∀ᶠ m : ℕ in atTop,∀ (d : LocalFormal.Datum R.family Γ),d.level=m →
      ∀ {H : AnalyticInput J A d} {η : ℝ} (I : FullPreparedInputAt H η),Retained.NativeIntake I →
      ∀ (x : IndependentTests J.tests) U,
        Summable (entry R d I x U) ∧
          compulsory R d I x U=(Real.exp (I.carrier.rep.exponent U):ℂ) • ∑' i,entry R d I x U i := by
  filter_upwards [eventually_retained_forced_smallness (V:=ι) R.family hG J.forcedConstant] with m small d rd H η I hi x U
  subst m
  have h := paid R d I x hi (small I.forcedPrice I.forced_bound) U
  exact ⟨h.1,h.2.1⟩

end YM.Integration.WilsonReceivedMarkedForcedSeries
