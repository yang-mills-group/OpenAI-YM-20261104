import YM.Integration.WilsonPositionThermometerConnected

/-! The physical three-point thermometer uses the original signed cubic
curvature and the two quadratic curvature fields, inserted through the
chosen run's genuine Maxwell field equivalence. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionThermometerReading
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Source Extraction Table Spec
open Climb Next.UVStress RG12 RG17 PhysMS PhysicalNext.Repeat.Legato
open XSpace XSpace.Normalize XSpace.Rose
open FVA2
open scoped Topology BigOperators Classical
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book} (F : Final R.family f S)
variable (J : ℝ → PhysMS.tower S)
variable {V : XSpace.Normalize.Store G} (K : XSpace.Rose.Pick V)

/-- Missing slots are the original unit polynomial of the same horizon.
The three occupied slots are exactly Rose.tag, including its normalizations. -/
def leg (C : Family G) (s : Badge) (i : Fin 3) : RG17.Free C 6 :=
  (Maxwell.Free.fields C.labels 6).symm (Rose.missing (Rose.tag G) s i)

theorem literal (C : Family G) (s : Badge) (i : Fin 3) :
    Maxwell.Free.address C.labels 6 (leg C s i) = (Rose.missing (Rose.tag G) s i).val := by
  rw [Maxwell.Free.address_eval,leg,LinearEquiv.apply_symm_apply]

theorem occupied (C : Family G) (i : Fin 3) :
    Maxwell.Free.address C.labels 6 (leg C univ i) = (Rose.tag G i).val := by
  rw [literal,Rose.full]

/-- Every subset on the same chosen physical hierarchy and positions.
The positions x are in units of the measuring length r. -/
def sample (r : ℝ) (x : Points 3) (s : Badge) : ℂ :=
  PhysMS.measured F none (J r) (d:=fun _ : Fin 3 => 6) (leg R.family s) r x

def tested (r : ℝ) : ℂ :=
  (Rose.test K).applyTo fun x => WilsonPositionThermometerConnected.value (sample F J r x)

/-- The manuscript's normalized real position reading on the given physical
frame. Comparison with any Wilson or MS series is a separate estimate. -/
def reading (r : ℝ) : ℝ := (tested F J K r).re / Rose.cT K.cut G K.image

theorem calibrated_denominator (r : ℝ) :
    (Rose.cT K.cut G K.image) * reading F J K r = (tested F J K r).re := by
  unfold reading
  field_simp [K.fresh.ne]

/-- The genuine underlying free book gives zero on *each* nonempty subset
of these same three input fields, at each separated configuration. -/
theorem free (C : Family G) (hG : G.Simple) {x : Points 3} (hx : x∈conf 3)
    (s : Badge) (hs : s.Nonempty) :
    PhysMS.WickGoal (C:=C) (d:=fun _ : Fin 3 => 6) (leg C s) x = 0 := by
  let t (i : Fin 3) : (Bel C.book).Tag := ⟨6,leg C s i⟩
  change (Bel C.book).useAt (Bel C.book) x t = 0
  rw [Maxwell.Free.display]
  have exact_inputs : Maxwell.Free.supply C.labels ∘ t =
      fun i => (Rose.missing (Rose.tag G) s i).val := funext fun i => literal C s i
  rw [exact_inputs]
  exact Rose.silent (XSpace.Initialize.standard G) hG hx s hs

/-- Hence the tested triple's free connected constant is identically zero;
no normalization constant is fitted from the measured Wilson array. -/
theorem blank (C : Family G) (hG : G.Simple) {x : Points 3} (hx : x∈conf 3) :
    WilsonPositionThermometerConnected.value (fun s => PhysMS.WickGoal (C:=C) (d:=fun _ : Fin 3=>6) (leg C s) x) = 0 := by
  simp [WilsonPositionThermometerConnected.value,free C hG hx _ (by decide : (Finset.univ : Badge).Nonempty),
    free C hG hx _ (by decide : ({0,1} : Badge).Nonempty),free C hG hx _ (by decide : ({0,2} : Badge).Nonempty),
    free C hG hx _ (by decide : ({1,2} : Badge).Nonempty),free C hG hx _ (by decide : ({0} : Badge).Nonempty),
    free C hG hx _ (by decide : ({1} : Badge).Nonempty),free C hG hx _ (by decide : ({2} : Badge).Nonempty)]

end YM.Integration.WilsonPositionThermometerReading
