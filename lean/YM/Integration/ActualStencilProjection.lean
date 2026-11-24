import YM.Integration.ActualStencilJets
import YM.RG06.Section.Lens

/-! The original cylinder's leading coupling jet recovers the original
classical label on the existing integrated chord tests.  The hard projection
input is the proved `Section.Lens.recovery`, using the same Sound/Projects
witness and original slot presentation.  No momentum `Fits` estimate is
assumed or asserted here. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualStencilProjection
open Function Lattice Wilson Source Labels
open RG06 RG06.Weak Push.CutoffProjectors
open PertExtension.Series ActualStencilCylinder ActualStencilJets
open scoped BigOperators Classical ContDiff

variable {G : Gauge} {d : ℕ} {F : Labels.Frame G d}

theorem book_direct (S : SectionData F) (c : F.Coeff)
    (A : Links ℤ G.Color) :
    Dict06.Wil.book S c A = Section.direct S (tile A) c := by
  ext k
  rw [← Dict06.Wil.echo_book, Dict06.Series.ps_at]
  exact (Section.direct_eq S (ray_tiled A) c).coeff k

theorem casing_start (S : SectionData F) (i : F.Index)
    (A : Links ℤ G.Color) (e : ℕ) :
    Tokens.applyHere A (Tokens.stencil S i e) =
      PowerSeries.coeff e (Section.start S A i) := by
  rw [Tokens.stencil, ← book_casing, book_direct, Section.start, PowerSeries.coeff_mk]

theorem radial_start (S : SectionData F) {H : Hol G} (hS : S.Sound H)
    (i : F.Index) (A : Links ℤ G.Color) (e : ℕ) :
    (Radial.jet (realEcho S (Pi.single i 1)) (e + (F.grades i).2)
      (Dict06.Wil.restrictLog S.stencil A) : ℂ) =
      PowerSeries.coeff e (Section.start S A i) :=
  (radial_stencil S hS i A e).trans (casing_start S i A e)

private theorem radial_leading (S : SectionData F) {H : Hol G} (hS : S.Sound H)
    (i : F.Index) (A : Links ℤ G.Color) :
    (Radial.jet (realEcho S (Pi.single i 1)) (F.grades i).2
      (Dict06.Wil.restrictLog S.stencil A) : ℂ) =
      PowerSeries.constantCoeff (Section.start S A i) := by
  simpa only [Nat.zero_add, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    using radial_start S hS i A 0

/-- The chord is the original integrated radial-potential test, and the
derivative order remains the original classical engineering order. -/
theorem basis_projection (S : SectionData F) {H : Hol G} (hS : S.Sound H)
    (hV : Bid.pop S) (i : F.Index) (J : Lens G d) :
    iteratedDeriv J.2.val (fun r : ℝ =>
      (Radial.jet (realEcho S (Pi.single i 1)) (F.grades i).2
        (Dict06.Wil.restrictLog S.stencil (Section.chordLine (d := d) J.1 r)) : ℂ)) 0 =
      probe F J (Pi.single i 1) := by
  simp_rw [radial_leading S hS]
  exact Section.recovery S hS hV i J

def profile (S : SectionData F) (c : F.Coeff) (J : Lens G d) : ℂ :=
  iteratedDeriv J.2.val (fun r : ℝ => ∑ i, c i *
    (Radial.jet (realEcho S (Pi.single i 1)) (F.grades i).2
      (Dict06.Wil.restrictLog S.stencil (Section.chordLine (d := d) J.1 r)) : ℂ)) 0

/-- Independent original coefficients are combined only after each slot's
own coupling rank has been extracted. -/
theorem all_projection (S : SectionData F) {H : Hol G} (hS : S.Sound H)
    (hV : Bid.pop S) (c : F.Coeff) (J : Lens G d) :
    profile S c J = probe F J c := by
  unfold profile
  simp_rw [radial_leading S hS]
  exact Section.all_recovers S hS hV c J

theorem coordinate_restore (S : SectionData F) {H : Hol G} (hS : S.Sound H)
    (hV : Bid.pop S) (c : F.Coeff) :
    Section.leadingProject F (profile S c) = c := by
  have he : profile S c = Section.profiles S c := by
    funext J
    unfold profile
    simp_rw [radial_leading S hS]
    rfl
  rw [he]
  exact Section.project hS hV c

end YM.Integration.ActualStencilProjection
