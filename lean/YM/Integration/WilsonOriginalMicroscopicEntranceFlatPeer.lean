import YM.Integration.WilsonOriginalMicroscopicEntrancePairRefund

/-! The upper physical signed column on the same deposited grid under the
two actually paid masked sources and their original fixed-flat posterior. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceFlatPeer
open QuadraticLocal QuadraticLocal.Earn Function Filter Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push
open Ac GridApprox.Nil MergeProof MergeProof.Accent Extra.Histories Extra.Trajectories
open RG05Readout RG05Readout.Native RG05Readout.Many PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Mallow Motion Bandage Next.Foundations Trace.Physical.GermGraph Pert.Asymptotics
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP QuadraticLocal.Advent
open WilsonMeasuredCoefficientTransport WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCompanionFace
open WilsonMeasuredCompanionWage WilsonThermometerUnitFilingCoarse WilsonThermometerSolitaryExchange
open WilsonOriginalCompanionCellRoots WilsonThermometerOwnOffsetJoint
open Extraction Cells XSpace WilsonThermometerAlignedCells
open WilsonPositionProgramOriginalBlockedTrial WilsonAddressedRestartedColumn
open WilsonOriginalMicroscopicGuardedReporters WilsonThermometerUnitFilingFieldRange
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G)
local notation "C₀" => R.family
local notation "A" => (C₀).path.levels
local notation "J" => Stock.census (Fin 3)

theorem original (simple : G.Simple) (cater : Cater C₀ R.doors)
    (bank : WilsonThermometerClusterProjectionBudget.Ready A) (book : WilsonReportLampForecast.Ready A)
    (φ : Test 3) (c q r cap d ℓ : ℕ) (grade:d≤cap) :
    ∃ onset : ℕ, ∀ j ≥ onset, ∀ b ≥ onset, ∀ N p f (height : j+2 ≤ f) (_ : f ≤ N),
    (f-(j+2):ℕ) ≤ (c:ℝ)*Real.log (RG16.Lambda A f)+2 → 0 ≤ ((A).budget f).supportExponent-2 →
    ∀ r : ℝ, |r| ≤ (C₀).S.a (j+1) →
    ∀ z : Site ((C₀).side N p)×Site ((C₀).side N p), mass (R:=R) r (N,p) φ z≠0 →
    let o := origins R (atOrigin z) f
    ∀(m k : ℕ)(π : ℕ → Layout G)(Γ : ℕ → Pace.Coin)(Ψ : ∀i,Rep G ((C₀).side i p)),
    Concourse R.alloy R.kit R.T π Γ m N p k Ψ → m ≤ f →
    ∀(T I I' : Type)[Countable I][Countable I'](a : Lamps T I G (Ψ f).p o J)
      (a' : Lamps T I' G (Ψ f).p o J)(w : Fin 3 → ℝ), (∀v,0 < w v) →
    (∀i,(w i)⁻¹≤((A).clock.hatBeta f)^ℓ) →
    a.Paid w (Ψ f).p.B (((A).budget f).supportExponent-2) 1 →
    a'.Paid w (Ψ f).p.B (((A).budget f).supportExponent-2) 1 →
    ∀ v : Fin 3, ∀K (before : b ≤ K) (high : K ≤ N), b ≤ f → f ≤ K →
    ∀ target η (M : (C₀).label d ≃ₗ[ℂ] (C₀).label d) (y : (C₀).label d),
    let e := page (C:=C₀) d p b (((C₀).factory d N p).entries b y)
    let vK := M.symm e
    let H := hike C₀ K f rate*((1+4*stock C₀ K)*((C₀).labels.level d).coeffSize vK)
    Arrived R d b K N p target before high η M e →
    ∀ u : ℕ,(C₀).ref 0 ≤ u → ∀ uj : u ≤ j, Opened C₀ 0 u p → Opened C₀ 0 j p →
    ∀ x : T, ∀ s : (J).Mode, v∈s.val →
    let X := track R d N p K (numerator R d N p K 0 vK) f-calValues (C:=C₀) d N p f y
    ∀ Z₀:store C₀ d p f,WilsonAddressedRestartedFiled.Filed R d N p f (o v) X H Z₀ →
    ∀V:ℝ,0≤V → WilsonReflectedAffordableArm.charge R d f*H≤((C₀).S.a f)^d*((((A).clock.hatBeta f)^(q+2*ℓ+cap))⁻¹*V) →
    let EH:=fun U=>share (fun i=>(a.log x U).part ((J).fire i)) (fun i=>(a'.log x U).part ((J).fire i)) v s
    let Z := fun U =>
      (track R d N p K (numerator R d N p K 0 vK) f - calValues (C:=C₀) d N p f y)
        (Lattice.translate (o v) U) *
      share (fun i => (a.log x U).part ((J).fire i)) (fun i => (a'.log x U).part ((J).fire i)) v s
    Integrable Z (prior G _) ∧
    ‖actualTransport C₀ (N:=N) (fun U=>WilsonOriginalMicroscopicEntranceGridRow.signed R (fun _=>d) (N:=N)
         v (o v) Z₀ U*EH U) (uj.trans (by omega)) 1‖ ≤
       4*(((A).clock.hatBeta f)^q)⁻¹*(V*WilsonOriginalMicroscopicEntrancePeerChart.tariff G d) := by
  obtain ⟨onset,sale⟩:=WilsonOriginalMicroscopicEntrancePeerSchool.original R simple cater bank book φ c (q+2*ℓ) r cap d grade
  refine ⟨onset,?_⟩
  intro j late b start N p f height live dates room t rise loc resident o m k π Γ Ψ course admitted
    T I I' _ _ a a' w pos aperture cover cover' v K before high bf fK target η M y e vK H arrived
    u ref uj ou oj x s used X Z₀ filed V vp salary EH Z
  obtain ⟨bill,price⟩:=sale j late b start N p f height live dates room t rise loc resident m k π Γ Ψ course admitted
    T I I' a a' w pos cover cover' v K before high bf fK target η M y arrived u ref uj ou oj x s used Z₀ filed V vp salary
  refine ⟨bill,?_⟩
  have ep:0≤WilsonMeasuredCompanionSoft.expense 1:=by unfold WilsonMeasuredCompanionSoft.expense;positivity
  have cost₀:0≤basisCost G d:=zero_le_one.trans (Next.Foundations.full_value_bound (G:=G) d).choose_spec.1
  have tariff₀:0≤WilsonOriginalMicroscopicEntrancePeerChart.tariff G d:=
    add_nonneg (abs_nonneg _) (mul_nonneg (by linarith only [cost₀]) ep)
  rw [mul_assoc] at price
  exact WilsonOriginalMicroscopicEntrancePairRefund.original w ℓ q (((A).fits.delayed f).le) (mul_nonneg vp tariff₀)
    pos aperture v s price

end YM.Integration.WilsonOriginalMicroscopicEntranceFlatPeer
end
