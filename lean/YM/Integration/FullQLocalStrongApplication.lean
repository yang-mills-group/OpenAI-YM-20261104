import YM.Integration.LocalComparisonGlobalContract

/-!
# Strong-input application of the full local comparison lemma

This interface restricts the full local comparison lemma to strong inputs.
`UniformContract` does not formalize its complete weak domain.
The full local comparison lemma is the one allowed analytic input. Its strong-input
restriction below retains all three conclusions, actual primary extraction,
and one common re-expression before every loss/power request and every test.
No hb or normalized-integral estimate is an input field. This compatibility
interface still reuses Global.Input, including its assumed prescribed-model,
output packet-payment and coarse whole-action receipts. A theorem using only fine input must construct those receipts as
conclusions. This interface assumes them as part of `Global.Input`.

The original native Sheet and the finite request precede an EXISTENTIALLY
selected profile-width family and required floor function, then C_J/degree
and the block family. A later Chain retains the native floor raise of that
original Sheet as its preCosts. At a physical step the widths are pulled back through
the actual two profile indices. A fixed half is reserved internally; stored
profile widths may plateau. The width fields of the supplied Setup are
replaced, rather than imposing a strict shrink on stored adjacent profiles.
All other Setup fields, the exact Input/Output/PrimaryData and price formulas
are those specified in `LocalComparisonGlobalContract`.

The displayed Admission, Input, strong intake and whole-action receipts must
be CONSTRUCTED on the original Run in the application. They are not additional
external analytic assumptions. Inherited full-Q error is carried separately
by the original linear transport; it is not falsely declared Prepared.
The weaker intake is not identified with the old same-scale WeakReserve.

This projection deliberately does not encode the entire finite Psi/A0/Gaussian/
Ward width graph. The source
fixed-polynomial reciprocal-width condition is retained explicitly as
WidthPayment. The SAME returned Run must purchase it for the whole family
of later finite requests; neither positivity nor the upper bound by stored
widths proves it, and a new Run cannot be chosen for each later request.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FullQLocal

open Filter Lattice Wilson RG Marker
open RG3.Script.Picnic Comparison.RG02
open IterationFour IterationFour.Vacuum
open scoped Topology BigOperators Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
  {R : Census V} {C : Family G}

/-- Pre-block widths at the ORIGINAL profile indices. -/
structure ProfileWidths where
  width : ℕ → ℝ
  positive i : 0 < width i

def ProfileWidths.pair (W : ProfileWidths) (C : Family G) (m : ℕ) : ℝ :=
  min (W.width (C.path.levels.clock.J (m + 1)))
    (W.width (C.path.levels.clock.J m))

theorem ProfileWidths.pair_positive (W : ProfileWidths) (C : Family G) (m : ℕ) :
    0 < W.pair C m := lt_min_iff.mpr ⟨W.positive _, W.positive _⟩

/-- The literal reference scale z_i from TeX 28781. -/
def widthScale (C : Family G) (m : ℕ) : ℝ :=
  1 + Real.log (Real.log (C.path.levels.clock.hatBeta m))

/-- The concrete strengthened-delay condition from TeX 28783/28810.
This is part of the original schedule admission, not a new analytic estimate.
Its construction on ONE original Run for all finite requests remains an
internal obligation. In particular it is not inferred from positive widths. -/
structure WidthPayment (C : Family G) (W : ProfileWidths) where
  coefficient : ℝ
  coefficient_nonnegative : 0 ≤ coefficient
  degree : ℕ
  first : ℕ
  scale_ge_one m : first ≤ m → 1 ≤ widthScale C m
  reciprocal m : first ≤ m →
    (W.pair C m)⁻¹ ≤ coefficient * (widthScale C m) ^ degree

/-- Fixed internal fractional loss, on the two original profile indices. -/
def onFamily (J : LocalComparison.Global.Setup V) (W : ProfileWidths)
    (C : Family G) : LocalComparison.Global.Setup V :=
  { J with
    inputWidth := W.pair C
    outputWidth := fun m => W.pair C m / 2
    input_width_pos := W.pair_positive C
    output_width_pos := fun m => div_pos (W.pair_positive C m) (by norm_num)
    width_reserve := fun m => by
      have hp := W.pair_positive C m
      linarith }

omit [DecidableEq V] [Fintype V] in
theorem onFamily_fraction (J : LocalComparison.Global.Setup V)
    (W : ProfileWidths) (C : Family G) (m : ℕ) :
    (onFamily J W C).outputWidth m = (onFamily J W C).inputWidth m / 2 := rfl

omit [DecidableEq V] [Fintype V] in
/-- Any fixed component rescaling cost is paid once the actual block is large
 enough. This is a numerical implication, not a substitute for identifying
 the original component cost in the application. -/
theorem onFamily_rescaling (J : LocalComparison.Global.Setup V)
    (W : ProfileWidths) (C : Family G) (m : ℕ) (cost : ℝ)
    (hcost : cost ≤ ((C.S.block m).val : ℝ)) :
    2 * cost * (onFamily J W C).outputWidth m ≤
      ((C.S.block m).val : ℝ) * (onFamily J W C).inputWidth m := by
  have hp := le_of_lt (W.pair_positive C m)
  have h := mul_le_mul_of_nonneg_right hcost hp
  change 2 * cost * (W.pair C m / 2) ≤ ((C.S.block m).val : ℝ) * W.pair C m
  nlinarith

/-- One selected output family, before all delta/power requests. The source
 Input retains the COMPLETE all-test polynomial; the strong alternative is
 the original actual-stage K bound AND the fixed input-norm K bound. -/
structure SelectedFamily (Y : Bulk.Chain C.path)
    (J : LocalComparison.Global.Setup V) (W : ProfileWidths)
    (A : LocalComparison.Global.Admission C (onFamily J W C)) where
  prices : LocalComparison.Global.Prices A
  first : ℕ
  select (datum : LocalFormal.Datum C R) (hfirst : first ≤ datum.level)
    (hulls : LocalComparison.Global.ShortHulls prices datum)
    (I : LocalComparison.Global.Input Y (onFamily J W C) A datum)
    (intake : LocalComparison.Global.StrongIntake I) :
    LocalComparison.Global.SelectedOutput prices I
  bounds (delta : ℝ) (hdelta : 0 < delta) (forcedOrder : ℕ) :
    ∃ later : ℕ, ∃ hlater : first ≤ later,
      ∀ (datum : LocalFormal.Datum C R) (hm : later ≤ datum.level)
        (hulls : LocalComparison.Global.ShortHulls prices datum)
        (I : LocalComparison.Global.Input Y (onFamily J W C) A datum)
        (intake : LocalComparison.Global.StrongIntake I),
      Nonempty (LocalComparison.Global.RequestBounds
        (select datum (hlater.trans hm) hulls I intake) delta forcedOrder)

/-- The strong-domain projection of the ONE supplied full manuscript lemma.
 This definition is an assumption type, not a proof of local comparison.
 The full weak alternative is not replaced by the older candidate domain. -/
def StrongInstance : Prop :=
  G.Simple → ∀ (V : Type) [DecidableEq V] [Fintype V] (R : Census V)
    (s : RG.Supply.Sheet G) (J : LocalComparison.Global.Setup V),
    ∃ W : ProfileWidths, (∀ i, W.width i ≤ (s.profile i).width) ∧
      ∃ floor : ℕ → ℕ, s.floorL ≤ floor ∧
        ∃ K : LocalComparison.Global.PreBlockConstant,
          ∀ (n : ℕ → ℕ), floor ≤ n → ∀ (C : Family G) (Y : Bulk.Chain C.path),
            Y.preCosts = PhysicalNext.ThroughLaunch.raise s n → C.Makes →
            WidthPayment C W → ∀ A : LocalComparison.Global.Admission C (onFamily J W C),
            Nonempty { H : SelectedFamily (R := R) Y J W A //
              H.prices.vacuumConstant = K.value ∧ H.prices.polynomialDegree = K.degree }

/-- Use the SAME Run after its native floor raise. Widths and required floors
are chosen first from the original Sheet. The actual construction must then
supply the larger-floor identity, WidthPayment and A; none is an additional
external analytic assumption in the final core theorem. -/
theorem StrongInstance.atRun (H : StrongInstance (G := G)) (hG : G.Simple)
    (s : RG.Supply.Sheet G) (J : LocalComparison.Global.Setup V) :
    ∃ W : ProfileWidths, (∀ i, W.width i ≤ (s.profile i).width) ∧
      ∃ floor : ℕ → ℕ, s.floorL ≤ floor ∧
        ∀ (n : ℕ → ℕ), floor ≤ n →
          ∀ (run : PhysicalNext.Repeat.Legato.Run G),
            run.metals.p = PhysicalNext.ThroughLaunch.raise s n →
            WidthPayment run.family W →
            ∀ A : LocalComparison.Global.Admission run.family (onFamily J W run.family),
              Nonempty (SelectedFamily (R := R) (RunFormalChain.fromRun run) J W A) := by
  obtain ⟨W, hW, floor, hfloor, K, hK⟩ := H hG V R s J
  refine ⟨W, hW, floor, hfloor, ?_⟩
  intro n hn run hpre hWidth A
  obtain ⟨F⟩ := hK n hn run.family (RunFormalChain.fromRun run) hpre run.makes hWidth A
  exact ⟨F.val⟩

end YM.Integration.FullQLocal
