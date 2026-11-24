import YM.Integration.WilsonPositionScaleLawColorAxis
import YM.Integration.WilsonSurveyedColorVacuumKernel
import YM.Integration.WilsonPositionScaleLawColorAtHome

/-! A signed original color action fixes the full independently integrated MS
kernel. Position measurements may be asymmetric in the named fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawColorOriented
open Function Filter Set Spec Table Extraction OPE Climb Trace.Pilot PhysMS
open Maxwell Maxwell.Free XSpace XSpace.Stab XSpace.Normalize MS MS.Land FVA2
open FVA2.Dframe FVA2.Arrival FVA2.Position.OpenAxis
open WilsonPhysicalPositionDiscreteBranches (field)
open WilsonPhysicalPositionBornCandidates (possible)
open WilsonPositionScaleLawColorPrinted (painted)
open WilsonPositionPrescribedFormalTest (raw)
open WilsonPositionScaleLawColorAtHome (Quote)
open WilsonSurveyedColorNormalizers (groupAction)
open WilsonSurveyedColorVacuumKnight (isometry)
open scoped Topology Classical
variable {G : Gauge} [PreconnectedSpace G.El] (simple : G.Simple)
variable {d : ℕ}
local notation "N" => MoveSpace G d

theorem recorded (a : N) (c : Knight G) (sign : conn c 1)
    (same : ∀ i : Toon G d, records G d (field a (theory i)) =
      changing c (records G d (theory i))) :
    field a = WilsonSurveyedColorVacuumBasis.axis (isometry c)
      (groupAction simple (isometry c) (WilsonPositionScaleLawColorAxis.oriented c sign)) d := by
  apply (MS.Theater.Daylight (Press.portDeck G) d).ext
  intro i
  rw [theory_sig]
  apply Subtype.ext
  calc (field a (theory i)).val = appears G d (records G d (field a (theory i))) := (opensR _).symm
    _ = appears G d (changing c (records G d (theory i))) := by rw [same i]
    _ = _ := (WilsonPositionScaleLawColorAxis.original c _ _).symm

include simple in
theorem measured (a : N) (c : Knight G) (sign : conn c 1)
    (same : ∀ i : Toon G d, records G d (field a (theory i)) =
      changing c (records G d (theory i)))
    (M : MS_Data G (Plot (Press.portDeck G))) (ν : ℝ) (k : ℕ) :
    painted a (Reg.State.kernel ν M d k) = Reg.State.kernel ν M d k := by
  rw [WilsonPositionScaleLawColorPrinted.painted,recorded simple a c sign same]
  exact WilsonSurveyedColorVacuumKernel.tested simple (isometry c)
    (WilsonPositionScaleLawColorAxis.oriented c sign) M ν d k

omit [PreconnectedSpace G.El] in
theorem inverse (a b : N) (ab : field a ∘ₗ field b = 1) (P : Prediction G d)
    (fixed : painted a P = P) : painted b P = P := by
  calc painted b P = recruit (field b) (painted a P) := by rw [fixed];rfl
    _ = P := WilsonPositionScaleLawColorPrinted.unpaint b a ab P

variable {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (J : ℝ → tower S) (lead : Leading F J)
include simple lead in
theorem original {B : ℝ} (a : N) (chosen : a ∈ possible C d B)
    (c : Knight G) (sign : conn c 1)
    (same : ∀ i : Toon G d, records G d (field a (theory i)) =
      changing c (records G d (theory i))) :
    ∃ b ∈ possible C d B, field a ∘ₗ field b = 1 ∧ field b ∘ₗ field a = 1 ∧
      ∀ (V : Store G) (ν : ℝ) (M : MS_Data G (Plot (Press.portDeck G))) (q : ℕ),
      Quote F J a b V ν M q (raw ν M d q) := by
  obtain ⟨b,selected,ab,ba,quoted⟩ := WilsonPositionScaleLawColorAtHome.original F J lead a chosen
  refine ⟨b,selected,ab,ba,?_⟩
  intro V ν M q
  apply (quoted V ν M q).2
  intro k _
  exact inverse a b ab _ (measured simple a c sign same M ν k)

end YM.Integration.WilsonPositionScaleLawColorOriented
end
