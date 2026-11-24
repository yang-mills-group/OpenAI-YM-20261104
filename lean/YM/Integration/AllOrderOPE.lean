import YM.Integration.WilsonInversionSchur
import YM.Integration.WilsonFormalSupplier
import YM.FormalOPE.RG10.FiniteTop

/-!
The actual calibrated Wilson coefficient dictionary supplies the all-order
coupling-shifted marks of the finite inversion-regulator OPE machinery.
The original horizon and engineering factor of every insertion are retained.
This identifies all finite marked products and their connected formal log;
it does not assert a physical IR limit or an infinite convergent OPE sum.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration
open Lattice Wilson PowerSeries RG06 RG06.WilsonCompiler
open FormalOPE.RG10 FormalOPE.RG10.InversionTop
open PertExtension PertExtension.Orb PertExtension.Series.Tested Marker Extra.Trajectories
open scoped BigOperators Classical

variable {G : Gauge} (C : Family G) (N p d : ℕ)
    (hC : C.Makes) {hG : G.Simple}
    (hF : UVExtension.Oasis.Floral (hG := hG) C)

/-- A genuine RG10 stamp of the actual calibrated physical insertion. Its
valuation is proved from the existing RG06 supplier on this same family. -/
def actualOPEStamp (x : Site (C.side N p)) (i : (C.labels.level d).Index) :
    InversionTop.Stamp G (C.side N p) where
  stencil := physicalInversionObservable C N p d x i
  test := physicalInversion_pretest C N p d hC x i
  slots := ((C.labels.level d).grades i).2
  cleared k hk := by
    funext z
    rcases z with ⟨⟨⟩,u⟩
    unfold row
    rw [wilsonInversion_raw_source C N p d hC x i u]
    rw [wilsonIRSeries, PowerSeries.coeff_mk,
      wilsonIRSource_below_grade (C := C) (d := d) (N := N) (p := p) (i := i) hF x k hk]
    simp

/-- The shifted formal input has exactly the RG09 real source coefficients,
read in the very same cotree coordinates, with the original grade shift. -/
def actualOPEFactor (x : Site (C.side N p)) (i : (C.labels.level d).Index) :
    Kernel (Unit × Orb.Dir G (C.side N p)) := fun z =>
  lower ((C.labels.level d).grades i).2
    (wilsonIRSeries C N p d x i (wilsonInversionCoordinates C N p z.2))

theorem actualOPEStamp_factor (x : Site (C.side N p)) (i : (C.labels.level d).Index) :
    (actualOPEStamp C N p d hC hF x i).couplingMark =
      actualOPEFactor C N p d x i := by
  funext z
  rcases z with ⟨⟨⟩,u⟩
  unfold InversionTop.Stamp.couplingMark actualOPEStamp actualOPEFactor
  rw [wilsonInversion_raw_source C N p d hC x i u]

/-- Coefficient extraction keeps the RG06 grade shift and the ordinary Taylor
coefficient convention, without an extra factorial. -/
theorem actualOPEFactor_coeff (x : Site (C.side N p)) (i : (C.labels.level d).Index)
    (u : Orb.Dir G (C.side N p)) (k : ℕ) :
    PowerSeries.coeff k (actualOPEFactor C N p d x i ((),u)) =
      (MvPolynomial.eval (wilsonInversionCoordinates C N p u)
        (wilsonIRSource C N p d x i (((C.labels.level d).grades i).2 + k)) : ℂ) := by
  simp only [actualOPEFactor, lower, PowerSeries.coeff_mk, wilsonIRSeries]

variable {I : Type}
    (degree : I → ℕ) (positions : I → Site (C.side N p))
    (basis : (j : I) → (C.labels.level (degree j)).Index)

def actualOPEStamps (j : I) : InversionTop.Stamp G (C.side N p) :=
  actualOPEStamp C N p (degree j) hC hF (positions j) (basis j)

def actualOPEFactors (j : I) : Kernel (Unit × Orb.Dir G (C.side N p)) :=
  actualOPEFactor C N p (degree j) (positions j) (basis j)

theorem actualOPEFactors_stamps :
    actualOPEFactors C N p degree positions basis =
      InversionTop.Stamp.factors (actualOPEStamps C N p hC hF degree positions basis) := by
  funext j
  exact (actualOPEStamp_factor C N p (degree j) hC hF (positions j) (basis j)).symm

include hC hF in
/-- Every finite product of the same actual source series is integrable in
RG10's prescribed full Gaussian/interaction/measure coefficient formula. -/
theorem actualOPE_funded (hn : Even (C.side N p).val) (s : Finset I) :
    (InversionTop.feed hn).Funded ((InversionTop.vertices G (C.side N p)).weight *
      ∏ j ∈ s, actualOPEFactors C N p degree positions basis j) := by
  rw [actualOPEFactors_stamps C N p hC hF degree positions basis]
  exact InversionTop.Stamp.integrals hn _ s

include hC hF in
/-- Exact normalized all-order finite-product identity for the actual Wilson
source. The right side retains the original physical insertion per slot. -/
theorem actualOPE_product (hn : Even (C.side N p).val) (s : Finset I) :
    (InversionTop.feed hn).ordinary (InversionTop.vertices G (C.side N p)) s
      (actualOPEFactors C N p degree positions basis) =
    lower (∑ j ∈ s, ((C.labels.level (degree j)).grades (basis j)).2)
      (InversionTop.into (PowerSeries.mk (Orb.diag
        (Orb.restrictedO (∏ j ∈ s,
          physicalInversionObservable C N p (degree j) (positions j) (basis j)))))) := by
  rw [actualOPEFactors_stamps C N p hC hF degree positions basis]
  exact InversionTop.Stamp.orbit_coeff hn (actualOPEStamps C N p hC hF degree positions basis) s

include hC hF in
/-- The same finite-regulator product also has the accepted all-order
small-coupling asymptotic expansion, with each original insertion grade.
This is an asymptotic statement on the inversion regulator, not on C.omega. -/
theorem actualOPE_asymptotic (hn : Even (C.side N p).val) (s : Finset I) :
    Aspiration (fun g : ℝ =>
      (g⁻¹) ^ (∑ j ∈ s, ((C.labels.level (degree j)).grades (basis j)).2) *
        Orb.preExpectation (∏ j ∈ s,
          physicalInversionObservable C N p (degree j) (positions j) (basis j)) g)
      (fun k => (PowerSeries.coeff k ((InversionTop.feed hn).ordinary
        (InversionTop.vertices G (C.side N p)) s
        (actualOPEFactors C N p degree positions basis))).re) := by
  rw [actualOPEFactors_stamps C N p hC hF degree positions basis]
  exact InversionTop.Stamp.pre_formula hn
    (actualOPEStamps C N p hC hF degree positions basis) s

variable [DecidableEq I] [Fintype I] (R : Census I)

/-- Input to the marked OPE compiler, built directly from the actual RG09
coefficient dictionary with its proven RG06 valuation. -/
def actualOPEWord : (Unit × Orb.Dir G (C.side N p)) → Word R := fun z =>
  Word.emit R (fun j => actualOPEFactors C N p degree positions basis j z)

theorem actualOPEWord_publish :
    actualOPEWord C N p degree positions basis R =
      InversionTop.publish R (actualOPEStamps C N p hC hF degree positions basis) := by
  unfold actualOPEWord
  rw [actualOPEFactors_stamps C N p hC hF degree positions basis]

include hC hF in
/-- All-order connected and ordinary marked series share the same actual
source and full vacuum denominator. No independent test/slot is identified
with another one, and coincident physical positions remain allowed. -/
theorem actualOPE_marked (hn : Even (C.side N p).val) :
    let A := actualOPEWord C N p degree positions basis R
    let F := InversionTop.feed hn
    let W := InversionTop.vertices G (C.side N p)
    F.markedFunded W A ∧
      Word.vac R (F.contraction W A) = 0 ∧
      Word.expMark (F.contraction W A) = Word.package (R := R) (fun s =>
        lower (∑ j ∈ s.val, ((C.labels.level (degree j)).grades (basis j)).2)
          (InversionTop.into (PowerSeries.mk (Orb.diag
            (Orb.restrictedO (∏ j ∈ s.val,
              physicalInversionObservable C N p (degree j) (positions j) (basis j))))))) := by
  dsimp only
  rw [actualOPEWord_publish C N p hC hF degree positions basis R]
  obtain ⟨hf,hv,he⟩ := InversionTop.markedOrbit hn R
    (actualOPEStamps C N p hC hF degree positions basis)
  exact ⟨hf,hv,he.trans (InversionTop.ordinaryOrbit hn R
    (actualOPEStamps C N p hC hF degree positions basis))⟩

include hC hF in
/-- Restricting the allowed marker census preserves every finite order of
the connected and ordinary series. Every retained insertion keeps its own
original horizon, site and basis label. -/
theorem actualOPE_restrict (hn : Even (C.side N p).val)
    {J : Type} [Fintype J] [DecidableEq J] (S : Census J) (u : Names S R) (r : ℕ) :
    let c := (InversionTop.feed hn).contraction (InversionTop.vertices G (C.side N p))
      (actualOPEWord C N p degree positions basis R)
    let c' := (InversionTop.feed hn).contraction (InversionTop.vertices G (C.side N p))
      (actualOPEWord C N p (fun j => degree (u.e j)) (fun j => positions (u.e j))
        (fun j => basis (u.e j)) S)
    PowerSeries.trunc (r+1) c' = PowerSeries.trunc (r+1) (Word.eraseMarks u c) ∧
      PowerSeries.trunc (r+1) (Word.expMark c') =
        PowerSeries.trunc (r+1) (Word.eraseMarks u (Word.expMark c)) := by
  dsimp only
  rw [actualOPEWord_publish C N p hC hF degree positions basis R,
    actualOPEWord_publish C N p hC hF
      (fun j => degree (u.e j)) (fun j => positions (u.e j)) (fun j => basis (u.e j)) S]
  exact InversionTop.existing_subset hn R
    (actualOPEStamps C N p hC hF degree positions basis) r S u

/-- Finite insertion lists on the existing family admit all-order normalized
inversion-regulator expansions using the exact actual Wilson dictionary. -/
def ActualOPEProducts (C : Family G) : Prop :=
  ∀ (N p : ℕ) (hn : Even (C.side N p).val) (r : ℕ)
    (degree : Fin r → ℕ) (positions : Fin r → Site (C.side N p))
    (basis : (j : Fin r) → (C.labels.level (degree j)).Index) (s : Finset (Fin r)),
    (InversionTop.feed hn).Funded ((InversionTop.vertices G (C.side N p)).weight *
      ∏ j ∈ s, actualOPEFactors C N p degree positions basis j) ∧
    Aspiration (fun g : ℝ =>
      (g⁻¹) ^ (∑ j ∈ s, ((C.labels.level (degree j)).grades (basis j)).2) *
        Orb.preExpectation (∏ j ∈ s,
          physicalInversionObservable C N p (degree j) (positions j) (basis j)) g)
      (fun k => (PowerSeries.coeff k ((InversionTop.feed hn).ordinary
        (InversionTop.vertices G (C.side N p)) s
        (actualOPEFactors C N p degree positions basis))).re)

include hC hF in
theorem actualOPE_products : ActualOPEProducts C := by
  intro N p hn r degree positions basis s
  exact ⟨actualOPE_funded C N p hC hF degree positions basis hn s,
    actualOPE_asymptotic C N p hC hF degree positions basis hn s⟩

end YM.Integration
