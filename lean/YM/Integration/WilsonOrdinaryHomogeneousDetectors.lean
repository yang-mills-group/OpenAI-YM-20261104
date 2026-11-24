import YM.Integration.WilsonOrdinaryEngineering

/-! One simultaneous, genuine homogeneous real basis for the physical reflected mixed
detector matrix. Each slot is a true free comparator class in the stated engineering
grade, obtained by raising an original homogeneous source. -/

noncomputable section
namespace YM.Integration.WilsonOrdinaryHomogeneousDetectors
open Spec Climb OPE RG12 RG12.Frames RG17 SharpGram Trace.Pilot
open WilsonOrdinaryEngineering
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S) (d : ℕ)
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field d
local notation "V" => Desk.Sector F.sector.derivatives d
abbrev Handle := Σ i : Grade d, Fin (Module.finrank ℝ (V i))

def basis : Module.Basis (Handle F d) ℝ D :=
  (Pi.basis (fun i : Grade d => Module.finBasis ℝ (V i))).map ((chart F d).restrictScalars ℝ)

theorem entry (i : Handle F d) :
    basis F d i = Roof.cones F i.1.val d i.1.is_le (Module.finBasis ℝ (V i.1) i.2) := by
  rw [basis,Module.Basis.map_apply,Pi.basis_apply]
  exact Roof.listL F d i.1 _

theorem raised (i : Handle F d) : ∃ v : Roof.Peak C.labels i.1.val,
    basis F d i = (Maxwell.Free.scheme C.labels).rise i.1.is_le v.val := by
  rw [entry]
  exact ⟨Roof.beacon S F.sector.derivatives F.room.kernel.laws.toSymmetric F.room.kernel.spin
    F.phase.transport.comparator F.phase.transport.injection i.1.val (Module.finBasis ℝ (V i.1) i.2),rfl⟩

theorem eigenvalue (i : Handle F d) (t : ℝ) : Pert.Scale.gear C.labels d t (basis F d i) =
    (t:ℂ)^i.1.val • basis F d i := by
  rw [entry,Roof.gauged]

end YM.Integration.WilsonOrdinaryHomogeneousDetectors
