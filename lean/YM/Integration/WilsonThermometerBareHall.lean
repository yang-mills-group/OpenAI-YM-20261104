import YM.Integration.WilsonThermometerLiteralCredit
import YM.Push.LOCAL_SPLITTING.Products

/-! All marked faces of the same original microscopic thermometer, read on
their genuine joined support and with all of their tested derivatives. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerBareHall
open Finset Function Lattice Wilson RG Source Marker Push.Local Extra.Histories
open FVA1 PhysicalNext.Repeat.Legato Next.Rank MergeProof.East
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonPositionThermometerGradedReading
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) (A : Group R.family 6) {N per : ℕ}
local notation "J" => Stock.census (Fin 3)
local notation "C" => R.family
local notation "P" => R.family.path.rep N per N
local notation "V" => Config G (R.family.side N per)
local notation "v" j:max => A.station.wheel.atCut (N,per) (index A (grade j)) (vector A univ j)
variable (o : Positions (Fin 3) (R.family.side N per)) (s : (J).Mode)
local notation "face" => WilsonThermometerCourseHot.bare R A o s

def hall (y : Site (R.family.side N per)) : Support (R.family.side N per) :=
  insert y (s.val.biUnion (fun j=>((C).localSection (grade j)).footprint (o.origin j)))

def localFee (j : Fin 3) :=
  ActualRunPhysicalPages.price R N (grade j) (Price.awake C (grade j) N N per (v j))

def tested (rad : ℕ) :=
  (((s.val.card+1:ℕ) : ℝ)*(1+(rad:ℝ))^(P).p.power)^(P).p.order * ∏ j∈s.val,localFee R A (N:=N) (per:=per) j

theorem germ (refs : ∀ j : Fin 3,(C).ref (grade j) ≤ N) (y : Site (R.family.side N per)) (rad : ℕ)
    (near : ∀ j∈s.val,separation (o.origin j) y ≤ rad) :
    (P).p.Regular (hall (R:=R) o s y) (face) ∧
      (P).p.supBounds y (hall (R:=R) o s y) (face) (tested R A (N:=N) (per:=per) s rad) := by
  let f (j:Fin 3):= (C).O N per (v j) (o.origin j)
  let X (j:Fin 3):= ((C).localSection (grade j)).footprint (o.origin j)
  have q (j:Fin 3) : (P).p.Regular (X j) (f j) ∧ (P).p.supBounds (o.origin j) (X j) (f j)
      (localFee R A (N:=N) (per:=per) j) := by
    have paid := ActualRunPhysicalPages.priced R N per N (grade j) le_rfl (refs j)
      (Price.awake C (grade j) N N per (v j)) (o.origin j)
    rw [WilsonPositionThermometerStationBirth.kernel R N per (grade j) (refs j) (v j) (o.origin j)] at paid
    exact paid
  have contains (j : Fin 3) (hj : j∈s.val) : X j ⊆ hall (R:=R) o s y := by
    intro x hx
    exact mem_insert_of_mem (mem_biUnion.mpr ⟨j,hj,hx⟩)
  have result:=price_product (B:=(P).p) (Y:=hall (R:=R) o s y) s.val f
    (localFee R A (N:=N) (per:=per)) y o.origin rad near X contains (fun j _=>(q j).1) (fun j _=>(q j).2)
  have applyprod : (∏ j∈s.val,f j)=(face) := by funext U;exact prod_apply U _ _
  rw [applyprod] at result
  exact result

def slip (y : Site (R.family.side N per)) : V → ℂ :=
  (face)-masked (P).p.threshold (hall (R:=R) o s y) (face)

theorem attaches (refs : ∀ j : Fin 3,(C).ref (grade j) ≤ N) (y : Site (R.family.side N per)) (rad : ℕ)
    (near : ∀ j∈s.val,separation (o.origin j) y ≤ rad) :
    Attaches (P).p.threshold (hall (R:=R) o s y) (slip R A o s y) := by
  have h := (germ R A o s refs y rad near).1
  refine ⟨fun U W agree flags=>congrArg₂ (·-·) (h.sites U W agree) (uses_mask _ h.sites U W agree flags),
    fun t U=>congrArg₂ (·-·) (h.symmetry t U) (invariant_mask h.symmetry _ _ t U),
    h.borel.sub (masked_measurable _ _ _ h.borel),fun U healthy=>?_⟩
  exact sub_eq_zero.mpr (masked_eq _ _ _ _ healthy).symm

theorem slip_cap (y : Site (R.family.side N per)) {E : ℝ} (envelope : ∀ U,‖(face) U‖ ≤ E) (U : V) :
    ‖slip R A o s y U‖ ≤ E := by
  by_cases good : Healthy (P).p.threshold (hall (R:=R) o s y) U
  · simp only [slip,Pi.sub_apply,masked_eq _ _ _ _ good,sub_self,norm_zero]
    exact (norm_nonneg _).trans (envelope U)
  · simpa only [slip,Pi.sub_apply,masked_ne _ _ _ _ good,sub_zero] using envelope U

end YM.Integration.WilsonThermometerBareHall
