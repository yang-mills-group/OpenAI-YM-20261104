import YM.Integration.WilsonPositionThermometerReading
import YM.AllOrder.Leading.Solve

/-! The three genuine field grades of the measured Wilson thermometer. The
quadratic fields are kept on their original four-dimensional filtration step. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionThermometerGradedSource
open Function Filter Set Finset Lattice Wilson Extraction Table Spec Climb PhysMS PhysicalNext.Repeat.Legato
open XSpace XSpace.Normalize XSpace.Rose Maxwell Maxwell.Free
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G}

def grade : Fin 3 → Fin 7 := Fin.cases 6 (fun _ => 4)

def lower (G : Gauge) : Sec G 4 := ((Rose.f:ℂ)^2) • en (le_refl 4) (XSpace.Chiral.Ufield G)

def base (G : Gauge) : (i : Fin 3) → Sec G (grade i) :=
  Fin.cases (Rose.toll G) (fun _ => lower G)

def source (C : Family G) (s : Badge) (i : Fin 3) : RG17.Free C (grade i) :=
  (Maxwell.Free.fields C.labels _).symm (if i∈s then base G i else leaf G (grade i))

theorem promoted (C : Family G) (s : Badge) (i : Fin 3) :
    (Maxwell.Free.scheme C.labels).rise (Nat.le_of_lt_succ (grade i).isLt) (source C s i) =
    WilsonPositionThermometerReading.leg C s i := by
  apply Maxwell.Free.address_inj C.labels 6
  rw [Maxwell.Free.address_rise,WilsonPositionThermometerReading.literal,source,
    Maxwell.Free.address_eval, LinearEquiv.apply_symm_apply]
  unfold Rose.missing
  by_cases hi : i∈s
  · simp only [if_pos hi]
    fin_cases i <;> rfl
  · rw [if_neg hi,if_neg hi]
    rfl

theorem unit (C : Family G) (s : Badge) (i : Fin 3) (absent : i ∉ s) :
    source C s i = (Bel C.book).unit (grade i) := by
  apply Maxwell.Free.address_inj C.labels _
  rw [source, if_neg absent,Maxwell.Free.address_eval,LinearEquiv.apply_symm_apply,Maxwell.Free.unit_address]
  rfl

variable {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ → PhysMS.tower S)

/-- After the genuine regulator limits, the independent three physical
horizons represent the very same continuum seven-face assay. -/
theorem measured (lead : PhysMS.Leading F J) : ∀ᶠ r in Trace.Pilot.trail,
    ∀ (x : Points 3), x∈conf 3 → ∀ s : Badge,
    WilsonPositionThermometerReading.sample F J r x s =
    PhysMS.measured F none (J r) (d:=fun i => (grade i).val) (source R.family s) r x := by
  have raises := Filter.eventually_all.mpr (fun i : Fin 3 =>
    lead.raised (Nat.le_of_lt_succ (grade i).isLt))
  filter_upwards [raises,RG17.positiveLength] with r ready hr x hx s
  change S.classMoment S _ (r • x) (fun i => J r 6 (WilsonPositionThermometerReading.leg _ s i)) = _
  simp_rw [←promoted,ready]
  exact AllOrder.Leading.moment_inclusion F.room.kernel.laws.toSymmetric F.phase.transport.injection
    (fun i => Nat.le_of_lt_succ (grade i).isLt) (Work.A05.smul_conf hr hx)
    (fun i => J r (grade i) (source R.family s i))

end YM.Integration.WilsonPositionThermometerGradedSource
end
