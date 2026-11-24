import YM.OPE.Frame.Mode
import YM.OPE.Frame.Slew
/-!
# The invariant scheme

All further estimates will be on this **single** prescription independent
of external requests. The finite projection in each exact-grade row stays
fixed eventually. At any positive radius activation uses finitely many
nonzero rows, only to implement smooth formulas on a common domain. This
does not enter any error estimate as a replacement summing over unfixed
horizons; no assertion about accuracy summing all the active rows is made.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Function Filter Set
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
namespace YM.OPE.Frame
open Table
open MultipleContact (Detector Splitting)
variable {G : Gauge} {C : Family G} {U : Extraction.Order} {S : Table C.book}
    {I J : Type} [Fintype I] [Fintype J] {x : I → E4} {o : E4} {d m : ℕ} (F : Spec.Final C U S)
local notation "ν" => normalizedRotations
local notation "Λ" => F.sector.derivatives
local notation "X" => F.sector.turns
local notation "H" => F.room.kernel
local notation "P" => F.phase.transport

/-- Spectrum and detectors of the actual hierarchy, not a perturbative/kinematic rank factor.
All choices retained in every phase and in multiple-scale estimates. Includes biorthogonality
of the fixed row detector convention with the filtration: even on high fields. -/
structure Scheme where
  rings : Splitting Λ
  sampling (d : ℕ) : Detector S d
  representation : Grid rings F.room.kernel.spin
  coherent (d m : ℕ) (v : S.Field m) : rings.part d d (notch H F.phase.transport.spots (sampling d) m v) = rings.part d m v
  orientations : rings.Covariant X F.room.kernel.spin

def equi : Scheme F :=
 let D (d) := Classical.choice (MultipleContact.detector_exists d S)
 let B := splitMeasured H F.phase.transport.spots D F.phase.transport.injection F.phase.transport.motion
 let h := splitCovariant H F.phase.transport.spots D F.phase.transport.injection F.phase.transport.motion F.phase.transport.rights
 ⟨B,D,Classical.choice (grid_exists B h), fun _ _ _ => coherent_row ..,h⟩

namespace Scheme
variable {F} (Z : Scheme F) (r : ℝ) (w : Row Z.rings) (A : I → S.Tag)
/-- Exact coefficients (smooth on `Seen`). Scale declaration fixed independently of later exteriors. -/
def coeff (x : I → E4) (o : E4) : ℂ := (gate (Z.sampling w.fst) r : ℂ) * (Z.representation.coord w w.fst (assess X F.room.kernel.spin (Z.sampling w.fst) x A o))
lemma finitely (hr : 0 < r) : ∃ n : ℕ, ∀ w : Row Z.rings, n < w.fst → Z.coeff r w A x o = 0 := by
  obtain ⟨n,hn⟩ := eventually_atTop.mp (eventually_dark Z.sampling r hr); exact ⟨n,fun w h=> by rw [coeff,hn w.fst h.le]; simp⟩
lemma on_tail {K : Type} {l : Filter K} {r : K → ℝ} (h : Tendsto r l (𝓝[>]0)) :
    ∀ᶠ k in l, ∀ x : I→E4, ∀ o, Z.coeff (r k) w A x o = Z.representation.coord w w.fst (assess X F.room.kernel.spin (Z.sampling w.fst) x A o) := by
  filter_upwards [h.eventually (activated (Z.sampling w.fst))] with k hk x o; unfold coeff; rw [hk]; simp
lemma smooth (h : Seen r x o) : ContDiffAt ℝ ∞ (fun p : ℝ × (I→E4) × E4 => Z.coeff p.1 w A p.2.1 p.2.2) (r,x,o) := by
  unfold coeff; by_cases hr : r ≤ (threshold (Z.sampling w.fst))^2
  · have ho (i : I) : ‖x i-o‖ < 2*threshold (Z.sampling w.fst) := lt_of_lt_of_le (h.housed i)
      (((Real.sqrt_le_left (threshold_positive _).le).mpr hr).trans (by linarith only [threshold_positive (Z.sampling w.fst)]))
    refine ContDiffAt.mul ?_ (((LinearMap.toContinuousLinearMap ((Z.representation.coord w w.fst).restrictScalars ℝ)).contDiff.contDiffAt.comp (x,o) (assess_at _ F.phase.transport.spots H A h.separated ho)).comp (r,x,o) (f := Prod.snd) contDiffAt_snd)
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp r (gate_smooth _).contDiffAt).comp (r,x,o) contDiffAt_fst
  refine contDiffAt_const.congr_of_eventuallyEq (f:=fun _=>0) ?_
  filter_upwards [(show ContinuousAt Prod.fst (r,x,o) from continuousAt_fst).eventually (p:=fun p:ℝ=> (threshold (Z.sampling w.fst))^2<p) (lt_mem_nhds (lt_of_not_ge hr))] with p hp; rw [switched _ hp.not_gt]; simp -- hp <?
lemma rotated (K : Ortho) (w : RowAt Z.rings d) (h : Seen r x o) :
    Z.coeff r ⟨d,w⟩ (F.sector.turns.label K ∘ A) (Ortho.move K ∘ x) (Ortho.move K o) = ∑ v : RowAt Z.rings d,
      Z.coeff r ⟨d,v⟩ A x o * (Z.representation.axes d).coord w ⟨_,thick_spin Z.rings Z.orientations K (Z.representation.axes d v)⟩ := by
   by_cases hr : r < (threshold (Z.sampling d))^2
   · unfold coeff; rw [assess_spin X _ F.phase.transport.spots H F.phase.transport.motion _ K (gate_fitted (Z.sampling d) hr.le h), Z.representation.coord_spin Z.orientations F.phase.transport.spots,Finset.mul_sum]
     exact Finset.sum_congr rfl fun v _ => (mul_assoc ..).symm
   simp [coeff, switched _ hr]
lemma mirrored (h : Seen r x o) : Z.coeff r w (bar F.room.kernel.spin ∘ A) x o = star (Z.coeff r w A x o) := by
  by_cases hr : r < (threshold (Z.sampling w.fst))^2
  · unfold coeff; rw [assess_conj X F.room.kernel.spin F.phase.transport.spots H _ (gate_fitted _ hr.le h), show Z.representation.coord w _ (S.conj _ _ _)=_ from Z.representation.coord_bars Z.orientations F.phase.transport.rights _ w.snd]
    rw [star_mul', Complex.star_def ]; simp only [Complex.conj_ofReal]
  simp [coeff, switched _ hr]
lemma translated (z : E4) (h : Seen r x o) : Z.coeff r w A (fun i=> x i+z) (o+z) = Z.coeff r w A x o := by
  unfold coeff; by_cases hr : r < (threshold (Z.sampling w.fst))^2
  · rw [assess_shift X F.room.kernel.spin H A z (gate_fitted _ hr.le h)]
  simp [switched _ hr]
lemma permuted (a : J ≃ I) (h : Seen r x o) : Z.coeff r w (A ∘ a) (x ∘ a) o = Z.coeff r w A x o := by
  unfold coeff; by_cases hr : r < (threshold (Z.sampling w.fst))^2; swap; · simp [switched _ hr]
  have he (e : (Z.sampling w.fst).probes) (b : Bool) (K : Ortho) : inspect X F.room.kernel.spin e b (x ∘ a) (A ∘ a) o K = inspect X F.room.kernel.spin e b x A o K := by
    let E := a.sumCongr (Equiv.refl (Fin e.val.n))
    unfold inspect; rw [show beside (A ∘ a) _=beside A (counted X F.room.kernel.spin e b K) ∘ E from funext fun i => by cases i <;> rfl,
      show beside (x ∘ a) _=beside x (escorts e.val o K) ∘ E from funext fun i => by cases i <;> rfl]
    exact same_read _ _ F.room.kernel.laws.toSymmetric (gate_fitted _ hr.le h e K)
  unfold assess investigate; simp_rw [he]
lemma lifted [DecidableEq I] (hz : d ≤ m) (h : Seen r x o) (v : S.Field d) (i : I) :
    Z.coeff r w (update A i ⟨m,F.sector.derivatives.rise hz v⟩) x o = Z.coeff r w (update A i ⟨d,v⟩) x o := by
  unfold coeff; by_cases hr : r < (threshold (Z.sampling w.fst))^2; swap; · simp [switched _ hr]
  have he (e : (Z.sampling w.fst).probes) (b : Bool) (K : Ortho) : inspect X F.room.kernel.spin e b x (update A i ⟨m,F.sector.derivatives.rise hz v⟩) o K = inspect X F.room.kernel.spin e b x (update A i ⟨d,v⟩) o K := by
    let B := counted X F.room.kernel.spin e b K
    have hh (v:S.Tag) : beside (update A i v) B = update (beside A B) (Sum.inl i) v := by
      funext t; rcases t with t|t
      · by_cases ht : t=i; subst t; · simp
        simp [ht]
      simp
    change sense S _ (beside (update A i _) B) = sense _ _ (beside (update A i _) B)
    rw [hh,hh]; exact raised _ _ _ v F.room.kernel.laws.toSymmetric (fun _=>le_rfl) F.phase.transport.injection (gate_fitted _ hr.le h e K)
  unfold assess investigate; simp_rw [he]

lemma literal (v : S.Field m) : Z.coeff r w (sole (⟨m,v⟩ : S.Tag)) (sole o) o = (gate (Z.sampling w.fst) r : ℂ) * Z.representation.coord w m v := by
  rw [coeff, ← realized H F.phase.transport.spots]
  exact congrArg ((gate (Z.sampling w.fst) r:ℂ) * ·) (congrArg ((Z.representation.axes w.fst).coord w.snd) (show sheaf Z.rings w.fst w.fst _ = sheaf Z.rings w.fst m v from Subtype.ext (Z.coherent ..)))
end Scheme
end YM.OPE.Frame
