import YM.Integration.WilsonPositionScaleLawColorMark
import YM.Integration.WilsonPositionScaleLawColorOriented

/-! One enrolled measured degree-six field selects the orientation of every
named input in the real position conditions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawColorReading
open Function Filter Set Spec Table Extraction OPE Climb Trace.Pilot PhysMS Maxwell Maxwell.Free
open XSpace XSpace.Stab XSpace.Normalize MS MS.Land FVA2 FVA2.Dframe
open FVA2.Position.OpenAxis Further.CorrectedLift Labels
open WilsonPhysicalPositionDiscreteBranches (field)
open WilsonPhysicalPositionBornCandidates (possible)
open WilsonPhysicalPositionBornTransition (present)
open WilsonPositionScaleLawColorAtHome (Quote)
open WilsonPositionPrescribedFormalTest (raw)
open WilsonPhysicalChiralNonfreeCurvatureTest (ear reading)
open WilsonPhysicalChiralNonfreeCartanColor (direction)
open WilsonPositionThermometerGradedSource (source)
open WilsonPositionScaleLawColorMark (mark)
open scoped Classical BigOperators
variable {G : Gauge} {d : ℕ}
private abbrev Field (C : Family G) (d : ℕ) := (Bel C.book).Field d

def meter (F : Labels.Frame G d) (X : Fin 3 → PositionX.Tri.PanelL G) : F.Coeff →ₗ[ℂ] ℂ :=
  ∑ i : F.Index, if F.grades i=(d,d/2) then (ear F X i) • LinearMap.proj i else 0

theorem measured (F : Labels.Frame G d) (X : Fin 3 → PositionX.Tri.PanelL G) (v : F.Coeff) :
    meter F X v = reading F X v := by
  rw [meter,LinearMap.sum_apply,WilsonPhysicalChiralNonfreeCurvatureTest.reading]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp [smul_eq_mul]

def reader (C : Family G) (z : Fin 3 → G.Color) : Field C 6 →ₗ[ℂ] ℂ :=
  meter (C.labels.level 6) (fun j => direction j (z j)) ∘ₗ (ladder C 6).toLinearMap

theorem printed (C : Family G) (z : Fin 3 → G.Color) (v : Field C 6) :
    reader C z v = reading (C.labels.level 6) (fun j => direction j (z j)) (ladder C 6 v) :=
  measured _ _ _

theorem raised (C : Family G) (h : 6 ≤ d) : Injective ((scheme C.labels).rise h) := by
  intro x y eq
  apply address_inj C.labels 6
  simpa only [address_rise] using congrArg (address C.labels d) eq

def Bill (C : Family G) (z : Fin 3 → G.Color) (s : Rose.Badge) (h : 6 ≤ d)
    (a : MoveSpace G d) : Prop :=
  ∃ v : Field C 6, (scheme C.labels).rise h v =
    present (C:=C) (field a) ((scheme C.labels).rise h (source C s 0)) ∧
    -(reader C z (source C s 0)).re < (reader C z v).re

theorem sign (C : Family G) (z : Fin 3 → G.Color) (s : Rose.Badge) (upper : (0:Fin 3)∈s)
    (h : 6 ≤ d) (a : MoveSpace G d) (c : Knight G) (hand : conn c 1 ∨ conn c (-1))
    (same : records G d (field a (mark G h)) = changing c (records G d (mark G h)))
    (paid : Bill C z s h a) : conn c 1 := by
  rcases hand with keep | reverse
  · exact keep
  obtain ⟨v,seat,paid⟩ := paid
  let u : Field C 6 := source C s 0
  have opposite := WilsonPositionScaleLawColorMark.original C h s upper a c (-1) reverse same
  have placement : (scheme C.labels).rise h v = (scheme C.labels).rise h (-u) := by
    calc _ = (present (C:=C) (field a)) ((scheme C.labels).rise h u) := seat
      _ = ((-1:ℝ):ℂ) • ((scheme C.labels).rise h u) := opposite
      _ = -((scheme C.labels).rise h u) := by rw [Complex.ofReal_neg,Complex.ofReal_one,neg_one_smul]
      _ = _ := (((scheme C.labels).rise h).map_neg u).symm
  have exactV : v = -u := raised C h placement
  have value : (reader C z v).re = -(reader C z u).re := by
    calc _ = (reader C z (-u)).re := congrArg (fun w : Field C 6 => (reader C z w).re) exactV
      _ = _ := congrArg Complex.re ((reader C z).map_neg u)
  exact (lt_irrefl _ (paid.trans_le value.le)).elim

theorem original [PreconnectedSpace G.El] (C : Family G) (simple : G.Simple) :
    ∃ z : Fin 3 → G.Color,
      (∀ (s : Rose.Badge), (0:Fin 3)∈s → 0 < (reader C z (source C s 0)).re) ∧
      ∀ {f : Extraction.Order} {S : Table C.book} (F : Final C f S)
        (J : ℝ → tower S), Leading F J → ∀ {d : ℕ} (h : 6 ≤ d) (s : Rose.Badge),
        (0:Fin 3)∈s → ∀ {B : ℝ} (a : MoveSpace G d), a ∈ possible C d B →
        ∀ c : Knight G, (conn c 1 ∨ conn c (-1)) →
        (∀ p : Sec G d, records G d (field a p) = changing c (records G d p)) →
        Bill C z s h a →
        ∃ b ∈ possible C d B, field a ∘ₗ field b = 1 ∧ field b ∘ₗ field a = 1 ∧
          ∀ (V : Store G) (ν : ℝ) (M : MS_Data G (Plot (Press.portDeck G))) (q : ℕ),
            Quote F J a b V ν M q (raw ν M d q) := by
  obtain ⟨z,positive⟩ := WilsonPhysicalChiralNonfreeCartanOrientation.positive simple C
  refine ⟨z,fun s hs => ?_,?_⟩
  · rw [printed]
    exact positive s hs
  intro f S F J lead d h s upper B a chosen c hand same paid
  exact WilsonPositionScaleLawColorOriented.original simple F J lead a chosen c
    (sign C z s upper h a c hand (same _) paid) (fun i => same (theory i))

end YM.Integration.WilsonPositionScaleLawColorReading
end
