import YM.Integration.WilsonOriginalPublicTrialInput
import YM.Integration.WilsonPositionOriginalDiagnosticReflected
import YM.OPE.Strobe.Flick
import YM.Push.GRID_APPROXIMATION.Candidates

/-! The reflected, uncentered fixed-date trial on the original Wilson law.
The two blocking kernels factor on their actual disjoint dependence cones. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicReflectedTrace
open Function Set MeasureTheory Lattice RG Wilson Source Labels Cells
open PhysicalNext.Repeat.Legato Push.GridApprox OPE.Strobe OPE.Therm
open MergeProof.Ribbons.ManyCopies.Patrol
open WilsonPositionProgramBlockedTrialAddBack
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {K N p : ℕ}
local notation "X" k:max => Config G (R.family.side k p)
local notation "H" => R.family.path

theorem local_trial (d : ℕ) (v : R.family.label d) (x : Site (R.family.side K p)) :
    Interior (window x (stencilRadius R.family d)) (uncut R d N p K x v) := by
  let S := R.family.localSection d
  let u := names R d N p K v
  have cont := S.continuous_places (n:=R.family.side K p) u x
  have inside : Interior (S.footprint x) (S.places u x) :=
    ⟨S.placed_invariant (R.makes.sections d) x u,cont.measurable,
      S.placed_local x u,(Envelope.compactC cont).cost⟩
  exact (Interior.constant _ (v 0)).plus (inside.enlarges (stencil_fits R.family d x))

private theorem pair {r : ℕ} {x y : Site (R.family.side K p)} {P Q : X K → ℂ}
    (hP : Interior (window x r) P) (hQ : Interior (window y r) Q)
    (far : 2*muzzle (H).levels K r < separation x y) (live : K ≤ N) :
    backTo (H) N p live (P*Q) = backTo (H) N p live P * backTo (H) N p live Q := by
  let o : Bool → Site (R.family.side K p) := fun b => cond b y x
  let F : Bool → X K → ℂ := fun b => cond b Q P
  have loc b : Interior (window (o b) r) (F b) := by cases b <;> first | exact hP | exact hQ
  have sep (b c : Bool) (bc : b ≠ c) :
      2*muzzle (H).levels K r < separation (o b) (o c) := by
    cases b <;> cases c <;> first | exact False.elim (bc rfl) | exact far |
      exact (separation_comm x y) ▸ far
  have each := backs_many (H) r N p K N o Finset.univ loc sep live
  have prod {n : Side} (f : Bool → Config G n → ℂ) :
      fineJob f Finset.univ = f false * f true := by funext U; simp [fineJob,mul_comm]
  simpa only [prod,F,Bool.cond_false,Bool.cond_true] using each

/-- The microscopic cut is real. Its translation is the lift of the chosen
coarse seam. The inequality on K already guarantees disjointness through N. -/
theorem original (live : K ≤ N) (cut : Cut (R.family.side N p))
    (seam x y : Site (R.family.side K p)) (matched : anchor R.family.S p live seam = cut.slide)
    (r : ℕ) {P Q : X K → ℂ} (hP : Interior (window x r) P) (hQ : Interior (window y r) Q)
    (far : 2*muzzle (H).levels K r < separation x (affine cut.flip seam y)) :
    (∫ U, P U * star (Q (pull cut.flip seam U)) ∂scene (H) N p K) =
      Cells.form (R.family.beta N p) cut (backTo (H) N p live P) (backTo (H) N p live Q) := by
  let T : X K → ℂ := Q ∘ pull cut.flip seam
  have loc : Interior (window (affine cut.flip seam y) r) T :=
    hQ.unchanged cut.flip seam (window_affine y seam cut.flip)
  have joint := pair R hP loc.real far live
  have zero : anchor R.family.S p (le_refl K) seam = seam := by
    unfold anchor Ratio.embed Schedule.toDepth
    simp only [tsub_self,Schedule.steps]
    rw [show ((1 : Side).val : ℕ) = 1 from rfl,one_smul,wrap_lift]
  have turns := backTo_orient (H) N p (le_refl K) live seam cut.flip (cylinder_env hQ)
  rw [zero,matched] at turns
  have conj := backTo_star (H) N p live (cylinder_env loc)
  have invoice := OPE.Therm.retro R.makes.wilson live le_rfl
    (P*(fun U => star (T U))) ((cylinder_env hP).mulC (cylinder_env loc.real))
  refine invoice.symm.trans ?_
  change (∫ U, backTo (H) N p live (P*(fun U => star (T U))) U ∂scene (H) N p N) = _
  rw [WilsonPositionOriginalDiagnosticReflected.same R N p, joint, conj]
  change Wilson.moment _ (fun U => _ * star (backTo (H) N p live T U)) = _
  rw [show backTo (H) N p live T = _ from turns]
  rfl

end YM.Integration.WilsonOriginalPublicReflectedTrace

