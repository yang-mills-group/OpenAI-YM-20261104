import YM.FVAAlt2.Rocket.Licenses

/-! The regulated FVA window request on the selected sheet and its actual block lengths. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeFVAPlateau

open Lattice Precision RG RG.Supply RegulatorIR
open PhysicalNext.Repeat.Legato

variable {G : Gauge}

/-- The length request is known from the original kernel before the Rolls is chosen. -/
def floor (s : Sheet G) : ℕ → ℕ :=
  RegulatorIR.FVAAlt2.Lodge.anticipate G (Oracle.books s.kernel)

/-- The plateau request uses the purchased block length and branches of the same kernel. -/
def width (s : Sheet G) : ℕ → Side → ℕ :=
  RegulatorIR.FVAAlt2.Lodge.shoulder (Oracle.books s.kernel) s.has

/-- One branch family licenses every requested window of the selected physical clock. -/
def Funded (a : Levels G) : Prop :=
  ∃ Z : ∀ P : Patch, P.Branches a.clock.kernel G,
    PhysicalNext.Repeat.Legato.FVAAlt2.Windows a
      (RegulatorIR.FVAAlt2.Lodge.anticipate G (Oracle.books a.clock.kernel))
      (RegulatorIR.FVAAlt2.Lodge.shoulder (Oracle.books a.clock.kernel) Z)

/-- A paid Wait realizes every window using the same Rolls, start point and clock. -/
theorem of_paid {s : Sheet G} {P : Rolls s} {T : Protection P}
    {V : Delays T} {D : Bar V} {W : Wait D} {a : Levels G}
    (h : Paid W a)
    (hfloor : ∀ i, floor s i ≤ (P.L i).val)
    (hwidth : ∀ i t, width s i (P.L i) ≤ W.window i t) : Funded a := by
  unfold Funded
  rw [h.kernel]
  refine ⟨s.has, ?_⟩
  unfold PhysicalNext.Repeat.Legato.FVAAlt2.Windows
  rw [h.lengths]
  refine ⟨hfloor, s.first, ?_⟩
  intro i hi
  obtain ⟨k, _, hk, hJ⟩ := h.run i hi
  refine ⟨k, (hwidth i _).trans hk, fun j hj hl => hJ j ?_ ?_⟩
  · exact (Nat.sub_le_sub_left (hwidth i _) k).trans hj
  · exact hl.trans (Nat.add_le_add_left (hwidth i _) k)

/-- The selected Run supplies the formal FVA correlation supplier's actual contract. -/
theorem contract (R : Run G) (h : Funded R.family.path.levels) :
    ∃ Z : ∀ P : Patch, P.Branches R.family.path.levels.clock.kernel G,
      RegulatorIR.FVAAlt2.Lodge.Contract R (Oracle.books R.family.path.levels.clock.kernel) Z := by
  obtain ⟨Z, hZ⟩ := h
  exact ⟨Z, rfl, hZ⟩

end YM.Integration.NativeFVAPlateau
end
