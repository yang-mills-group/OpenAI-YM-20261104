import YM.Integration.WilsonEpochPositionCoefficients
import YM.Integration.WilsonEpochRegulator
import YM.Next.WARD_BIN.Stencils

/-! The original Run's actual temperature-scaled, terminally transported
source for a fixed epoch term. Its only change of bare stencil is a genuine
projected-null insertion at the very marked site, once its finite support
fits in the torus. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEpochCalibratedInsertion

open Function Lattice Wilson Source Source.Drops Labels XSpace FVA2 FVA2.Arrival
open PhysicalNext.Repeat.Legato WilsonEpochPositionCoefficients
open scoped Classical BigOperators ContDiff
variable {G : Gauge} (R : PhysicalNext.Repeat.Legato.Run G)

/-- Exact physical finite source with the true terminal calibration matrix
and the native physical threshold. This holds on all group fields. -/
theorem calibrated (Y : Initialize G) (N p : ℕ) (s : Folio G)
    (U : Config G (R.family.side N p)) :
    R.family.O N p (Dict06.Actual.calibrate R.family N p s.u.size (s.item Y))
      (wrap (R.family.side N p) s.addr) U =
      Dict06.Actual.factor R.family N s.u.size *
        (placed R Y (R.family.side N p) s U : ℂ) := by
  rw [Dict06.Actual.names,Dict06.Actual.meet,(phase R Y _ s U).1]
  rfl

private theorem supplied {H : Hol G} {d : ℕ} (A : Survey G H d) (v : Label G d) :
    ∃ T : SectionData (R.family.labels.level d), T.Sound R.family.params ∧
      ∀ U, T.evaluate ((R.family.labels.level d).coords v) U = Press.wheel A v.val U := by
  obtain ⟨T, hT, _, hread⟩ := A.prepares (R.family.labels.level d)
  exact ⟨T,holonomy H R.family.params ▸ hT,hread v⟩

/-- A finite cutoff, before the physical period and all directions. The actual
single changed factor in the signed cylinder telescope satisfies the original
microscopic `PiVanish` test at exactly its own wrapped address. -/
theorem projected (Y : Initialize G) (s : Folio G) :
    ∃ b : ℕ, ∀ n : Side, b ≤ n.val → R.family.params.PiVanish s.u.size (wrap n s.addr)
      (fun U => (placed R Y n s U : ℂ) - (Folio.placard Y s n U : ℂ)) := by
  let A := R.family.localSection s.u.size
  let c := (R.family.labels.level s.u.size).coords (s.item Y)
  obtain ⟨T,hT,hread⟩ := supplied R (Y.surveys s.u.size) (s.item Y)
  obtain ⟨b,hab⟩ := WardBin.large_fits A.stencil
  obtain ⟨e,hte⟩ := WardBin.large_fits T.stencil
  refine ⟨max b e,?_⟩
  intro n hn J
  let o := wrap n s.addr
  let H := R.family.params
  let Z (h : ℝ) := H.links s.u.size J h
  have left (h : ℝ) : (placed R Y n s (H.testLinks s.u.size o J h) : ℂ) =
      A.evaluate c (Z h) :=
    (phase R Y n s _).1.trans (WardBin.fromAbove (A.cylinder_local c)
      (hab n ((le_max_left _ _).trans hn)) o (Z h))
  have right (h : ℝ) : (Folio.placard Y s n (H.testLinks s.u.size o J h) : ℂ) =
      T.evaluate c (Z h) :=
    (phase R Y n s _).2.trans ((hread _).symm.trans (WardBin.fromAbove
      (T.cylinder_local c) (hte n ((le_max_right _ _).trans hn)) o (Z h)))
  let u := fun h : ℝ => (placed R Y n s (H.testLinks s.u.size o J h) : ℂ) -
    (Folio.placard Y s n (H.testLinks s.u.size o J h) : ℂ)
  let v := fun h : ℝ => A.evaluate c (Z h) - T.evaluate c (Z h)
  have eq : u = v := funext fun h => congrArg₂ (·-·) (left h) (right h)
  change ContDiffAt ℝ _ u 0 ∧ ∀ k ≤ s.u.size, iteratedDeriv k u 0 = 0
  rw [eq]
  have a := (R.makes.sections s.u.size).projects c J
  have t := hT.projects c J
  refine ⟨a.1.sub t.1,fun k hk => ?_⟩
  exact (iteratedDeriv_fun_sub (a.1.of_le (Nat.cast_le.mpr hk))
    (t.1.of_le (Nat.cast_le.mpr hk))).trans (sub_eq_zero.mpr ((a.2.2 k hk).trans (t.2.2 k hk).symm))

end YM.Integration.WilsonEpochCalibratedInsertion
end

