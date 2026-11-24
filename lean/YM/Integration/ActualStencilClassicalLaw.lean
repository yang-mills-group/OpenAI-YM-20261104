import YM.Integration.ActualStencilProjection
import YangMills.WilsonProof.NativeSupport.YM.MS.Theater.BrightK

/-! The native classical law of the original frame polynomial.  Its allowed
status follows from the original grade, invariance and reality.  The original
cylinder's chord jets read that very polynomial.  This does not assert the
remaining momentum-space `Fits` estimate or identify prescribed fee tables. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualStencilClassicalLaw
open Function Lattice Wilson Source Labels
open MS MS.Local.Physical MS.Theater
open Push.CutoffProjectors PertExtension.Series ActualStencilCylinder
open scoped BigOperators Classical ContDiff

variable {G : Gauge} {d : ℕ} (F : Labels.Frame G d)

def law (i : F.Index) : MS.Landau.Detect.Law G := MS.Theater.orbit G (F.basis i).val

theorem allowed (i : F.Index) :
    law F i ∈ MS.Local.Physical.Allowed G (F.grades i).1 (F.grades i).2 := by
  apply (MS.Theater.Governed (F.pure i)).mpr
  exact ⟨(F.basis i).property.2,
    congrArg (fun x : Labels.Label G d => x.val) (F.realForm i)⟩

/-- The native finite reader is supplied by the existing `covers` theorem;
no comparison equation is made an additional hypothesis. -/
theorem reader (i : F.Index) (X : Labels.Jet G) :
    ∃ P : MS.Theater.Probe G, MS.Theater.Board P d X ∧
      MS.Theater.back P (F.grades i).2 (law F i) =
        ((F.grades i).2.factorial : ℂ) * Labels.read X (F.basis i).val := by
  obtain ⟨P, hP⟩ := MS.Theater.covers d X
  exact ⟨P, hP, MS.Theater.KP P X hP (F.pure i) (F.bound i)⟩

/-- The same original polynomial read by the native law is recovered from
the original cylinder at every retained classical derivative order. -/
theorem chord_read (S : SectionData F) {H : Hol G} (hS : S.Sound H)
    (hV : Bid.pop S) (i : F.Index) (J : Lens G d) :
    iteratedDeriv J.2.val (fun r : ℝ =>
      (Radial.jet (realEcho S (Pi.single i 1)) (F.grades i).2
        (Dict06.Wil.restrictLog S.stencil (RG06.Section.chordLine (d := d) J.1 r)) : ℂ)) 0 =
      iteratedDeriv J.2.val (fun r : ℝ =>
        Labels.read (Source.scaleJet J.1 r) (F.basis i).val) 0 := by
  rw [ActualStencilProjection.basis_projection S hS hV i J, probe_eq]
  congr 1
  funext r
  rw [show F.coords.symm (Pi.single i 1) = F.basis i from
    (congrArg F.coords.symm (F.coords_basis i)).symm.trans
      (F.coords.symm_apply_apply (F.basis i))]

end YM.Integration.ActualStencilClassicalLaw
