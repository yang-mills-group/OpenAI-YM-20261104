import YM.Integration.QuadraticVacuumReentry
import YM.Integration.ActualCanonicalInputPayload
import YM.Integration.ActualRunRetunedVacuum

/-! Descent on one unmarked physical family, with the stopping scale chosen
before arbitrarily high Wilson cutoffs. Every edge uses the concrete canonical
output of that same family and retains its native regular reset on its carrier. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QuadraticVacuumHistory

open Filter Lattice Wilson RG Marker
open PhysicalNext.Repeat.Legato Comparison.RG02 IterationFour.Vacuum
open LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Canonical
open scoped Classical Topology

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]

/-- An actual rough state at a finite scale, on the same request throughout. -/
structure State (R : Run G) (Γ : Census V) (J : Request V)
    (A : NumericSchedule R.family J) (η : ℕ → ℕ → ℕ → ℝ) where
  datum : LocalFormal.Datum R.family Γ
  analytic : AnalyticInput J A datum
  prepared : FullPreparedInputAt analytic (η datum.cutoff datum.period datum.level)
  intake : Retained.NativeIntake prepared
  actual : prepared.carrier.rep.eval =
    (R.family.path.rep datum.cutoff datum.period (datum.level + 1)).eval

variable {R : Run G} {Γ : Census V} {J : Request V} {A : NumericSchedule R.family J}
    {η : ℕ → ℕ → ℕ → ℝ} {caps : Handoff.OutputCapacities}
    {Y : Bulk.Chain R.family.path} {floor n : ℕ → ℕ}
    {models : Retained.ModelFamily (R := Γ) caps Y J A floor n}
    (Φ : CompleteFamily models η)
local notation "Paid" => State R Γ J A η

/-- Each edge remembers the fixed family's exact physical output, its
canonical affine-null error, the price and the auxiliary vacuum sources. -/
def Selected (old next : Paid) : Prop :=
  ∃ (hfirst : Φ.joint.first ≤ old.datum.level)
    (hfloors : Handoff.LocalFloors floor n old.datum)
    (hulls : Retained.ShortHulls models.prices old.datum),
    let model := models.realize old.datum (Φ.joint.after_model.trans hfirst) hfloors hulls old.analytic
    let chosen := Φ.joint.select old.datum hfirst hfloors hulls old.analytic old.prepared old.intake
    let output := Φ.canonical old.datum hfirst hfloors hulls old.analytic old.prepared old.intake
    HEq next.prepared.carrier output.output.carrier ∧
    HEq next.prepared.error (ActualCanonicalInputPayload.error R chosen) ∧
    next.prepared.inherited = ActualCanonicalInputPayload.errorPrice R old.prepared models.prices ∧
    next.prepared.regularPrice = 0 ∧ next.prepared.forcedPrice = 0 ∧
    HEq next.analytic.layers (ActualRunRetunedVacuum.retunedLayers R model) ∧
    next.analytic.packets = VacuumAuxiliaryInput.packets J.tests G _ Γ ∧
    ∃ C : CalibrationPresentation output.output.carrier.rep (A.inputNorm next.datum.level)
        (η next.datum.cutoff next.datum.period next.datum.level),
      HEq next.prepared.calibration C ∧ ∀ U, C.amount U =
        (output.output.carrier.rep.beta - R.family.path.β old.datum.cutoff old.datum.period old.datum.level) *
        Push.BetaTransport.kinetic (R.family.path.rep old.datum.cutoff old.datum.period old.datum.level).path
          (R.family.path.levels.params old.datum.level).clip (A.inputNorm next.datum.level) U

/-- The local threshold precedes both states, the physical period, and the
height of the original represented cutoff. -/
def Steps : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ (old : Paid) (hm : old.datum.level = m+1)
    (W : Bulk.Colors Γ G (R.family.side (m+1) old.datum.period))
    (field : Exterior.fieldDir G (R.family.side m old.datum.period) 1),
    ∃ next : Paid, next.datum = ActualNextLocalDatum.descend old.datum hm W field ∧
      Selected Φ old next

variable (colors : ∀ _N per m : ℕ, Bulk.Colors Γ G (R.family.side (m+1) per))
    (fields : ∀ _N per m : ℕ, Exterior.fieldDir G (R.family.side m per) 1)

/-- The input colors and external field on every edge are literally those
prescribed at the original cutoff, physical period, and coarse level. -/
def Edge (old next : Paid) : Prop :=
  Selected Φ old next ∧ ∃ (m : ℕ) (hm : old.datum.level = m+1),
    next.datum = ActualNextLocalDatum.descend old.datum hm
      (colors old.datum.cutoff old.datum.period m) (fields old.datum.cutoff old.datum.period m)

private theorem larger_invoice {n : Side} {E : Payload G n} {p : BudgetPoint}
    {a b : ℝ} (h : E.Invoice p a) (hab : a ≤ b) : E.Invoice p b := by
  obtain ⟨v, hv, hb⟩ := h.credit
  exact { h with credit := ⟨v, hv, fun x => ⟨(hb x).1, (hb x).2.1, (hb x).2.2.trans hab⟩⟩ }

/-- One stopping threshold works at *every* larger cutoff. The original
datum, torus and prescribed chart history stay attached to the trace, and
the last state's true regular invoice is in the fixed requested norm. -/
theorem all_cutoffs (hs : Steps Φ) :
    ∃ first : ℕ, ∀ i N : ℕ, first ≤ i → i ≤ N →
      ∀ (colors : ∀ _N per m : ℕ, Bulk.Colors Γ G (R.family.side (m+1) per))
        (fields : ∀ _N per m : ℕ, Exterior.fieldDir G (R.family.side m per) 1) (old : Paid),
      old.datum.cutoff = N → old.datum.level + 1 = N →
      ∃ last : Paid, Relation.ReflTransGen (Edge Φ colors fields) old last ∧
        last.datum.cutoff = N ∧ last.datum.period = old.datum.period ∧
        last.datum.level + 1 = i ∧
        last.prepared.error.Invoice (A.inputNorm (i-1)) (J.inheritedConstant *
          Pert.Asymptotics.regulatorRun R.family N old.datum.period i ^ ((J.order : ℝ)+1-J.eta)) := by
  obtain ⟨start, hstep⟩ := eventually_atTop.1 hs
  refine ⟨start+1, ?_⟩
  intro i N hfirst hi colors fields old hN htop
  have iterate (m : ℕ) (hstart : start ≤ m) (k : ℕ) : ∀ old : Paid,
      old.datum.level = m+k →
      ∃ last : Paid, Relation.ReflTransGen (Edge Φ colors fields) old last ∧
        last.datum.cutoff = old.datum.cutoff ∧ last.datum.period = old.datum.period ∧
        last.datum.level = m := by
    induction k with
    | zero =>
      intro old h
      exact ⟨old, .refl, rfl, rfl, by simpa only [Nat.add_zero] using h⟩
    | succ k ih =>
      intro old h
      have hl : old.datum.level = m+k+1 := by omega
      obtain ⟨mid, hm, hedge⟩ := hstep (m+k) (by omega) old hl
        (colors old.datum.cutoff old.datum.period (m+k))
        (fields old.datum.cutoff old.datum.period (m+k))
      have hm' : mid.datum.level = m+k := by rw [hm]; rfl
      obtain ⟨last, htrace, hN, hp, hlast⟩ := ih mid hm'
      have hmidN : mid.datum.cutoff = old.datum.cutoff := by rw [hm]; rfl
      have hmidP : mid.datum.period = old.datum.period := by rw [hm]; rfl
      exact ⟨last, .head ⟨hedge, m+k, hl, hm⟩ htrace, hN.trans hmidN, hp.trans hmidP, hlast⟩
  obtain ⟨last, htrace, hc, hp, hl⟩ := iterate (i-1) (by omega) (N-i) old (by omega)
  have hscale : last.datum.level + 1 = i := by omega
  have native := larger_invoice last.prepared.error_paid last.prepared.inherited_bound
  have heq : J.inheritedConstant *
      Pert.Asymptotics.regulatorRun R.family last.datum.cutoff last.datum.period
        (last.datum.level+1) ^ ((J.order : ℝ)+1-J.eta) =
      J.inheritedConstant * Pert.Asymptotics.regulatorRun R.family N old.datum.period i ^
        ((J.order : ℝ)+1-J.eta) := by rw [hc, hN, hp, hscale]
  exact ⟨last, htrace, hc.trans hN, hp, hscale,
    (congrArg₂ (fun p b => last.prepared.error.Invoice p b) (congrArg A.inputNorm hl) heq).mp native⟩

end YM.Integration.QuadraticVacuumHistory
