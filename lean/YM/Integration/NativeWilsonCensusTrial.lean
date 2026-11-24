import YM.Integration.NativeRegulatorWilsonExpansion
import YM.Integration.NativeWilsonCensusIdentity
import YM.Integration.NativeRegulatorAdmittedTrials
import YM.IterationFour.Running

/-! The positive-coupling Census low-action identity for the actual moving
first-block program through each fixed demand below its horizon. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.NativeWilsonCensusTrial

open Function Filter Lattice Wilson Precision RG Labels PhysicalNext.Repeat.Legato
open RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Moving
open Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Geometry Prim Diagram Diagram.Formal
open PertExtension Series Series.Radial Series.Tested Chart Binding Ledger Gauge Booth
open Comparison.RG02 Comparison.RG02.Bulk Comparison.RG02.Adjacent Comparison.RG02.FVAAlt2
open Integral Exterior Arm Marker Multi Pipeline Pipeline.See Period.Field Sound
open NativeFormalSharedCoupling NativeFormalPrescriptionAgreement NativeFormalRegulatorCollector
open WilsonLimitConstruction.FundedFormalEconomy NativeFormalDiagonalCollector PowerSeries
open scoped Classical BigOperators

variable {G : Gauge} {R : Run G} {hG : G.Simple} {W : Bank R hG} {μ : ℝ}
  {P : MS.Land.Prescription (nativeDeck R)} {Z : branches R}
  {C : Lodge.Contract R (program R) Z} {A : table R} {g : G.ColorIndex}
  {I : Type} [Fintype I] [DecidableEq I] {i : I} {S : Marker.Census I}
  (T : Trial W μ P Z C A g i S)

local notation "𝓑" => C.profile (program R) Z R (schedule Z C T.order) (above Z C T.order)
local notation "periodSystem" => Period.Field.LodgeT.instance_real (program R) Z R C
  (schedule Z C T.order) (above Z C T.order)
local notation "𝓛" => Calibration.sheet T.calibrate
local notation "σ" => T.stop T.station

variable {n : ℕ} (v : Pegs.Motor (C.profile (program R) Z R (schedule Z C T.order) (above Z C T.order)) n T.station)
  (d : Fin n → ℕ) (u : (a : Fin n) → (R.family.labels.level (d a)).Index)
local notation "𝓐" => T.stamp.traces T.station n σ v d u
local notation "𝓕" => Figure.prop R (ProgramT.spend (program R) Z R C
  (schedule Z C T.order) (above Z C T.order) T.location T.station n v) d u
variable (j : ℕ) (x : fieldDir G (R.family.side (NativeRegulatorInitialDatum.level T j) (T.stop T.station)) 1)
local notation "step₀" => NativeRegulatorInitialDatum.first T j
local notation "Y₁" => (periodSystem).records (𝓑).desk R.family.path σ (step₀).next
local notation "L₁" => T.stamp.menu.cloth (step₀).next
local notation:max "data₀" a:max => NativeRegulatorInitialDatum.datum T v d u j a
open Comparison.RG02.Moving.Path



open Comparison.RG02.Laplace
open RG FullQLocal.RenderedStep
local notation "m₀" => NativeRegulatorInitialDatum.level T j
local notation "Δ₀" => R.family.path.levels.clock.op m₀ σ
local notation "V₁" => R.family.path.rep (m₀+1) σ m₀
local notation "τ₀" => Pert.Asymptotics.regulatorRun R.family (m₀+1) σ (m₀+1)
local notation "K₀" => (RunFormalChain.fromRun R).step (m₀+1) m₀ σ (Nat.lt_succ_self m₀)
local notation "F₀" => (data₀ x).forest
local notation "o₀" => (data₀ x).tag
local notation "C₀" => Boot.ink S i R.family.path (m₀+1) σ (𝓕 j)
local notation:max "visible₁" q:max y:max => See.visible S (Y₁).clip (Y₁).path L₁ (𝓐 (step₀).next) q y

/-- Every lower demanded order gives the same outgoing vacuum coefficient.
Both native series expand the same unmasked, varying Wilson integral. -/
theorem coefficient (r : ℕ) (hr : r ≤ T.order) (k : ℕ) (hk : k ≤ r) :
    visible₁ k x = Symmetry.Orbit.ground K₀ F₀ o₀ C₀ r k x - Symmetry.Orbit.ground K₀ F₀ o₀ C₀ r k 0 := by
  exact Laplace.trial_gap (Laplace.trial_earlier hr (NativeRegulatorWilsonExpansion.vacuum T v d u j x))
    (NativeWilsonBlockExpansion.centered K₀ F₀ C₀ o₀ x r (R.family.path.levels.budget m₀)
      (Boot.Revenue.receiving R σ m₀ S (𝓕 j) i)) k hk

theorem polynomial (r : ℕ) (hr : r ≤ T.order) (t : ℝ) :
    peval (fun k => visible₁ k x) r t =
      Adjacent.cover (Symmetry.Orbit.ground K₀ F₀ o₀ C₀ r) r t x -
      Adjacent.cover (Symmetry.Orbit.ground K₀ F₀ o₀ C₀ r) r t 0 := by
  simp only [peval,Zone.eval,Adjacent.cover,Complex.real_smul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [coefficient T v d u j x r hr k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)),mul_sub,Complex.ofReal_pow]

local notation:max "err" r:max y:max => NativeWilsonCensusIdentity.remainder R S i m₀ σ (𝓕 j) F₀ o₀ r y

/-- At the actual Run coupling the measured centered error is the difference
of the original local nonlinear RG02 vacuum remainders. -/
theorem error_at (r : ℕ) (hr : r ≤ T.order) :
    (NativeRegulatorWilsonExpansion.logarithm T j x τ₀ - peval (fun k => visible₁ k x) r τ₀).re =
      err r x - err r 0 := by
  have H := NativeWilsonCensusIdentity.centered R S i m₀ σ (𝓕 j) F₀ o₀ r x
  have h z : 0 < (V₁).eval z := RG02.Actual.eval_pos R.makes.wilson (Nat.le_succ m₀) z
  rw [Real.log_div (h _).ne' (h _).ne'] at H
  rw [NativeRegulatorWilsonExpansion.logarithm_at T j x, polynomial T v d u j x r hr]
  simp only [NativeWilsonCensusIdentity.formal] at H
  simp only [Complex.sub_re, Complex.ofReal_re] at H ⊢
  linarith only [H]

variable {I₀ : Type} {J : FullQLocal.RenderedStep.Request I₀}
  (A₀ : NumericSchedule R.family J) {ε : ℝ}

/-- On the paid Census support the retained action, running channel and signed
original discarded activities reconstruct the selected outgoing vacuum series
up to its exact nonlinear local error at the same physical coupling. -/
theorem retained (H : OriginalWilsonCensusStep.Receipt R A₀ ε m₀ σ) (hr : J.order ≤ T.order)
    (hx : flags (V₁).p.threshold (Integral.sample τ₀ x) = ∅) :
    let Z₀ := OriginalCensusBarcode.carrier R A₀ m₀ (m₀+1) σ (Nat.lt_succ_self m₀)
    let a := OriginalWilsonCensusStep.keptAction R m₀ σ J.order
    let z := Integral.sample τ₀ x
    a z - a 1 + (V₁).path.inChannels (V₁).clip (V₁).p (V₁).beta z +
      Z₀.activities.additive (A₀.outputNorm m₀) z +
      (peval (fun k => visible₁ k x) J.order τ₀).re = err J.order 0 - err J.order x := by
  intro Z₀ a z
  rw [polynomial T v d u j x J.order hr]
  exact NativeWilsonCensusIdentity.kept R S i m₀ σ (𝓕 j) F₀ o₀ A₀ H x hx


open scoped Topology
variable (U : Demand R.family.labels → Trial W μ P Z C A g i S)
  (fund : ∀ z, z.2+1 ≤ (U z).order)

def coupling (j : ℕ) : ℝ :=
  let m := NativeRegulatorInitialDatum.level T j
  Pert.Asymptotics.regulatorRun R.family (m+1) (T.stop T.station) (m+1)

theorem positive : 0 < coupling T j :=
  IterationFour.Currency.g_pos R.makes _ _ _ le_rfl

include fund

private theorem eventually_levels {b : ℕ} : ∀ᶠ z in atTop,
    b ≤ (U z).order ∧ ∀ j, b ≤ NativeRegulatorInitialDatum.level (U z) j := by
  apply (eventually_ge_atTop ((∅,b) : Demand R.family.labels)).mono
  intro z hz
  have hb : b ≤ z.2 := hz.2
  have hs : b ≤ (U z).order := by have h := fund z; omega
  exact ⟨hs,fun j => hs.trans (NativeRegulatorAdmittedTrials.level (U z) j)⟩


/-- The actual chosen physical couplings tend to zero simultaneously over
all first stations and all the original periods of the funded family. -/
theorem small (δ : ℝ) (hδ : 0 < δ) : ∀ᶠ z in atTop, ∀ j, 0 < coupling (U z) j ∧ coupling (U z) j < δ := by
  obtain ⟨b,hb⟩ := eventually_atTop.1 (IterationFour.Currency.g_small hG R.makes δ hδ)
  filter_upwards [eventually_levels U fund (b := b)] with z hz
  intro j
  let m := NativeRegulatorInitialDatum.level (U z) j
  exact ⟨positive (U z) j,hb (m+1) ((hz.2 j).trans (Nat.le_succ _)) _ _ le_rfl⟩

theorem running (route : Demand R.family.labels → ℕ) :
    Tendsto (fun z => coupling (U z) (route z)) atTop (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨tendsto_order.2 ⟨?_,?_⟩,Eventually.of_forall (fun z => positive (U z) (route z))⟩
  · intro a ha
    exact Eventually.of_forall (fun z => ha.trans (positive (U z) (route z)))
  · intro a ha
    exact (small U fund a ha).mono (fun z hz => (hz (route z)).2)

/-- Every actual first station of the same family eventually receives the
original Census certificate and lies past the requested expansion order. -/
theorem funded (h : OriginalCensusFusion.AtOrder R A₀ ε) : ∀ᶠ z in atTop,
    J.order ≤ (U z).order ∧ ∀ j, OriginalWilsonCensusStep.Receipt R A₀ ε
      (NativeRegulatorInitialDatum.level (U z) j) ((U z).stop (U z).station) := by
  obtain ⟨b,hb⟩ := eventually_atTop.1 (OriginalWilsonCensusStep.first R A₀ h)
  filter_upwards [eventually_levels U fund (b := max b J.order)] with z hz
  exact ⟨(le_max_right _ _).trans hz.1,fun j => hb _ ((le_max_left _ _).trans (hz.2 j)) _⟩


/-- On the original preselected Run every supported request and its numeric
schedule obtains the joint first-stage certificate with no additional local
field or asymptotic assumptions. -/
theorem original (hReadout : RG05Preconstruction.ReadoutPurchase R.b)
    (horders : ∀ q, q ≤ (R.metals.p.profile q).order ∧ q ≤ (R.metals.p.profile q).power)
    (hreserve : J.outputSupport ≤ (R.family.path.levels.budget 0).supportExponent) (hε : 0 < ε) :
    ∀ᶠ z in atTop, J.order ≤ (U z).order ∧ ∀ j, OriginalWilsonCensusStep.Receipt R A₀ ε
      (NativeRegulatorInitialDatum.level (U z) j) ((U z).stop (U z).station) :=
  funded A₀ U fund (OriginalCensusFusion.realized R hG hReadout horders A₀ hreserve hε)

end YM.Integration.NativeWilsonCensusTrial
end
