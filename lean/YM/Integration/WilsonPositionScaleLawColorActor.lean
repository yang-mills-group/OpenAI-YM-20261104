import YM.Integration.WilsonPositionScaleLawColorNative
import YM.Integration.WilsonPositionScaleLawColorReading

/-! The four-action and one original signed Cartan reading suffice on the
elected candidate for every asymmetric independent position prescription. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawColorActor
open Function Filter Set Spec Table Extraction OPE Climb Trace.Pilot PhysMS Maxwell Maxwell.Free
open XSpace XSpace.Stab XSpace.Normalize MS MS.Land FVA2 FVA2.Dframe FVA2.Position.OpenAxis
open WilsonPhysicalPositionDiscreteBranches (field)
open WilsonPhysicalPositionBornCandidates (possible)
open WilsonPhysicalPositionBornTransition (present)
open WilsonPositionScaleLawColorReading (reader Bill)
open WilsonPositionThermometerGradedSource (source)
open WilsonPositionScaleLawColorAtHome (Quote)
open WilsonPositionPrescribedFormalTest (raw)
open scoped Classical Topology
variable {G : Gauge}

def Cone (C : Family G) {d : ℕ} (h : 6 ≤ d) (a : MoveSpace G d) : Prop :=
  let w := WilsonMeasuredPublicEntranceActionColor.field C (by omega : 4≤d)
  ∃ t : ℝ, 0 ≤ t ∧ ∃ k : ℂ, present (C:=C) (field a) w = (t:ℂ) • w + k • (Bel C.book).unit d

def Faculty {C : Family G} {f : Extraction.Order} {S : Table C.book} (F : Final C f S)
    (J : ℝ → tower S) {d : ℕ} (B : ℝ) (a : MoveSpace G d) : Prop :=
  ∃ b ∈ possible C d B, field a ∘ₗ field b = 1 ∧ field b ∘ₗ field a = 1 ∧
    ∀ (V : Store G) (ν : ℝ) (M : MS_Data G (Plot (Press.portDeck G))) (q : ℕ),
      Quote F J a b V ν M q (raw ν M d q)

theorem original [PreconnectedSpace G.El] (C : Family G) (simple : G.Simple) :
    ∃ z : Fin 3 → G.Color,
      (∀ (s : Rose.Badge), (0:Fin 3)∈s → 0 < (reader C z (source C s 0)).re) ∧
      ∀ {f : Extraction.Order} {S : Table C.book} (F : Final C f S)
        (J : ℝ → tower S), Leading F J → ∀ {d : ℕ} (h : 6 ≤ d) (s : Rose.Badge),
        (0:Fin 3)∈s → ∀ {B : ℝ} (a : MoveSpace G d), a ∈ possible C d B →
        Cone C h a → Bill C z s h a → Faculty F J B a := by
  obtain ⟨z,positive,positioned⟩ := WilsonPositionScaleLawColorReading.original C simple
  refine ⟨z,positive,?_⟩
  intro f S F J lead d h s upper B a chosen four six
  obtain ⟨c,hand,common⟩ := WilsonPositionScaleLawColorNative.original C simple h a chosen four
  exact positioned F J lead h s upper a chosen c hand common six

end YM.Integration.WilsonPositionScaleLawColorActor
end
