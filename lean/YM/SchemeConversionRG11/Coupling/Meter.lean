import YM.SchemeConversionRG11.Coupling.Entry
import YM.SchemeConversionRG11.Field.Variation

/-!
# The coupling test is a test on the connected correlation

Here third cumulant on an ordered word of separably smeared fields. The arrays on this port
must be the corresponding ordinary smeared correlations, not moments without their denominator.
(Profile.trio factorization.) Only claim coupling prescription for real readings (real part
projection made explicit to avoid real/complex assumptions). Need independent checks of that
reality from both prescriptions. The centering in `meter` is the zero-order *regulator* reading,
not its putative continuum limit. For the real field-frame orbit it has, about the continuum
free point, a particularly useful first derivative test on ORDINARY correlations.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.Coupling
open Function Filter Maxwell Issue Series Tape Pert.Triangle Pert.Position Affine MeasureTheory
open scoped Topology ContDiff BigOperators

variable {G : Gauge} {F : Labels.Frames G}

/-- Inventory in this order: triad, three singleton readings (indices 1..3),
  then the pair readings with the complementary singleton omitted (indices 4..6). -/
def cabinet (F : Labels.Frames G) : Fin 7 → Section F 6 :=
  ![⟨3,basic F,profileChoice⟩,
    ⟨1,fun _ ↦ basic F 0,single 0⟩,
    ⟨1,fun _ ↦ basic F 1,single 1⟩,
    ⟨1,fun _ ↦ basic F 2,single 2⟩,
    ⟨2,![basic F 1,basic F 2],duo 1 2 (by decide)⟩,
    ⟨2,![basic F 0,basic F 2],duo 0 2 (by decide)⟩,
    ⟨2,![basic F 0,basic F 1],duo 0 1 (by decide)⟩]

def locker (A : Issue F 6) : Series (Fin 7 → ℂ) := fun j i ↦ A _ (cabinet F i).f j (cabinet F i).p

/-- Normalized third-cumulant rule (symmetrically ordered bosonic insertions). -/
def tree (v : Fin 7 → ℂ) := v 0 - v 1*v 4 - v 2*v 5 - v 3 * v 6 + 2*v 1*v 2*v 3

def connected (A : Issue F 6) : Series ℂ := liftJet tree (locker A)

/-- Inverse units fixed by the independently computed reduced triangle integral. -/
def readout (G : Gauge) : ℂ → ℝ := fun w ↦ w.re / (cTest G).re

theorem cTest_real : cTest G = ↑(∫ p : Points 3, (testReal p * response G p)) := by
  unfold cTest Test.applyTo
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  refine Eventually.of_forall fun p ↦ ?_
  change ↑(stamp * testReal p) * (↑(fullTransfer G p) : ℂ) = ↑(testReal p * response G p)
  unfold Pert.Triangle.response; push_cast; ring

theorem cTest_positive (h : G.Simple) : 0 < (cTest G).re :=
  (by rw [cTest_real]; exact firstTestPositive h)

def meter (A : Issue F 6) : Series ℝ :=
  liftJet (fun v : ℂ ↦ readout G (v-connected A 0)) (connected A)

theorem meter_at_zero (A : Issue F 6) : meter A 0 = 0 := by simp [meter,readout]

lemma tree_smooth : ContDiff ℝ ω tree := by unfold tree; fun_prop
lemma reading (s : ℂ) : ContDiff ℝ ω (fun x ↦ readout G (x-s)) := by
  have he := (Complex.reCLM.contDiff (n:=ω)).comp (contDiff_id.sub (contDiff_const (c:=s)))
  exact he.div_const _

theorem meter_through {n : ℕ} {A B : Issue F 6} (h : Identifies n A B) : Through n (meter A) (meter B) := by
  have he : Through n (locker A) (locker B) := fun j hj ↦ funext
    (fun i ↦ congrArg (fun m : Tape F 6 (cabinet F i).r ℂ ↦ m ((cabinet F i).p)) (h _ _ j hj))
  have hs : Through n (connected A) (connected B) := he.lift tree_smooth.contDiffAt
  rw [meter, meter, hs.zero]
  exact hs.lift (reading _ |>.contDiffAt)

theorem locker_sub (A : Issue F 6) {z : Series ℝ} (hz : z 0 = 0) :
    locker (insertSeries z A) = subJet (locker A) z := by
  funext j i
  let L := ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Fin 7 ↦ ℂ) i
  let d := cabinet F i
  let Q := ContinuousMultilinearMap.apply ℝ (fun _ : Fin d.r ↦ E F 6) ℂ d.p
  have hv := trunc_represents z j
  have hb := trunc_represents (locker A) j
  have ha := trunc_represents (A d.r d.f) j
  have he : subJet (fun n ↦ L (locker A n)) z j = subJet (locker A) z j i :=
    ((hb.linear (F:=ℂ) L).subJet hv hz).unique ((hb.subJet hv hz).linear (F:=ℂ) L) j le_rfl
  rw [← he]
  exact ((ha.subJet hv hz).linear (F:=ℂ) Q).unique ((ha.linear (F:=ℂ) Q).subJet hv hz) j le_rfl

theorem meter_sub (A : Issue F 6) {z : Series ℝ} (hz : z 0 = 0) :
    meter (insertSeries z A) = subJet (meter A) z := by
  have he : connected (insertSeries z A) = subJet (connected A) z := by
    rw [connected,locker_sub _ hz,liftJet_subst tree_smooth.contDiffAt hz]; rfl
  rw [meter,meter,he,subJet_base hz]
  exact liftJet_subst (reading _|>.contDiffAt) hz

lemma free_locker (h : G.Simple) {A : Issue F 6} (ht : Twist A) : locker A 0 = 0 := by
  funext i
  unfold locker; rw [ht]; fin_cases i
  · exact (finiteTest h F).inert
  · exact kill_single 0 (single 0)
  · exact kill_single 1 (single 1)
  · exact kill_single 2 (single 2)
  · exact kill_even_pair _
  · exact kill_odd_pair h _ (j:=2) (by decide)
  exact kill_odd_pair h _ (j:=1) (by decide)

lemma tree_first (a : Series (Fin 7 → ℂ)) (hz : a 0 = 0) : liftJet tree a 1 = a 1 0 := by
  rw [Tape.lift_one tree_smooth,hz]
  let p := fun t : ℝ ↦ t • a 1
  have ht : HasDerivAt p (a 1) 0 := by
    convert! (hasDerivAt_id' (0:ℝ)).smul_const (a 1) using 1; simp
  have he : HasFDerivAt tree (fderiv ℝ tree 0) (p 0) := by
    rw [show p 0 = 0 by simp [p]]; exact (tree_smooth.differentiable (by simp) _).hasFDerivAt
  have H : ∀ i : Fin 7, HasDerivAt (fun t : ℝ ↦ p t i) (a 1 i) 0 := hasDerivAt_pi.mp ht
  apply (he.comp_hasDerivAt 0 ht).unique
  have hy := (((H 0|>.sub ((H 1).mul (H 4))).sub ((H 2).mul (H 5))).sub ((H 3).mul (H 6))).add
    ((((H 1).const_mul 2).mul (H 2)).mul (H 3))
  simp [p] at hy; exact hy

lemma readout_first (s : Series ℂ) :
    liftJet (fun t ↦ readout G (t-s 0)) s 1 = readout G (s 1) := by
  rw [Tape.lift_one (reading _)]
  let L : ℂ →L[ℝ] ℝ := (cTest G).re⁻¹ • Complex.reCLM
  have hl (x : ℂ) : readout G x = L x := by simp [L, readout, mul_comm, div_eq_mul_inv]
  have he : fderiv ℝ (fun t ↦ readout G (t-s 0)) (s 0) = L := by
    rw [show (fun t ↦ readout G (t - s 0)) = fun t ↦ L t - L (s 0) from funext fun t ↦ by rw [hl,map_sub]]
    exact (L.hasFDerivAt.sub_const _).fderiv
  rw [he,hl]

/-- Nontrivial first-order test: normalization tangent is entirely from the true first order of
 the triangle array; no contribution from any of the free filtration-buffer shifts, Ward, or
 disconnected or readout shifts. This is only a statement about formal series. -/
theorem leading_response (h : G.Simple) {A : Issue F 6} (ht : Twist A)
    {V : Series (Buffer F 6)} (hv : V 0 = 0) :
    meter (imprint V A) 1 = readout G (A 3 profileChoice 1 (basic F)) := by
  rw [meter, readout_first, connected, tree_first _ (free_locker h (Issue.aims ht hv))]
  let T := A 3 profileChoice
  change readout G (Tape.hinge V T 1 (basic F)) = readout G (T 1 (basic F))
  have H : Tape.vary (T 0) (V 1) (basic F) = 0 := by
    rw [Tape.vary_at, show T 0 = _ from ht 3 profileChoice]
    exact Finset.sum_eq_zero fun i _ ↦ (finiteTest h F).detectorIndependent (V 1) i
  apply congrArg (readout G)
  rw [Tape.leading _ _ hv, add_apply,H,zero_add]

theorem orient_meter (h : G.Simple) {A : Issue F 6} (ht : Twist A) {a : ℝ} (ha : 0 < a)
    (he : A 3 profileChoice 1 (basic F) = a • cTest G) {V : Series (Buffer F 6)} (hv : V 0 = 0) :
    meter (imprint V A) 1 = a ∧ Good (meter (imprint V A)) := by
  have hh : meter (imprint V A) 1 = a := by
    rw [leading_response h ht hv, he, readout]
    simpa using mul_div_cancel_right₀ a (cTest_positive h).ne'
  exact ⟨hh,meter_at_zero _,hh.trans_ne ha.ne'⟩

end YM.SchemeConversionRG11.Coupling
