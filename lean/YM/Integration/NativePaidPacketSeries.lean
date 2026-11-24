import YM.Integration.NativeBoundedAtomSeries
import YM.Integration.NativePaidPacketGroups

/-! The actual paid packet series, without changing its rows, roots or tests. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

namespace YM.Integration.NativePaidPacketSeries

open Function Filter Set Metric Finset Lattice Wilson RG Marker Precision Exterior
open LocalComparison NativePaidPacketGroups
open Comparison.Density.RenderM Comparison.RG02.Assembly
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius

variable {V : Type} [DecidableEq V] {R : Census V}
variable {D : V → ComparisonDensity.Address.Orbit} {G : Gauge} {n : Side}
variable (P : MarkedPackets D G n R)

def value (s : R.Mode) (z : ℤ) (x : TestSpace D) (U : Config G n) : ℂ :=
  ∑' i : (NativePaidPacketGroups.Fiber P) s z, ((NativePaidPacketGroups.token P) s z i).read x U

variable {P} {p : BudgetPoint} {address : V → Support n}
variable {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n}
variable {w : V → ℝ} {g width budget : ℝ} {offset slope : ℕ}
variable (paid : P.Paid p address region w g width budget offset slope)

include paid in
private lemma real_summable (hg : g ≠ 0) (s : R.Mode) (hs : s ≠ R.quiet)
    (z : ℤ) (x : TestSpace D) (b : Bool) (U : Config G n) :
    Summable (fun i : (NativePaidPacketGroups.Fiber P) s z =>
      (component ((NativePaidPacketGroups.token P) s z i) x b).unmasked U ((NativePaidPacketGroups.token P) s z i).root) :=
  NativeBoundedAtomSeries.value_summable _ _ paid.width_pos
    ((NativePaidPacketGroups.rank_le P) s z) (budget_summable paid hg s hs z x b) U

include paid in
theorem value_summable (hg : g ≠ 0) (s : R.Mode) (hs : s ≠ R.quiet)
    (z : ℤ) (x : TestSpace D) (U : Config G n) :
    Summable (fun i : (NativePaidPacketGroups.Fiber P) s z => ((NativePaidPacketGroups.token P) s z i).read x U) := by
  have hr := real_summable paid hg s hs z x false U
  have hi := real_summable paid hg s hs z x true U
  have hr' := (hr.hasSum.mapL Complex.ofRealCLM).summable
  have hi' := ((hi.hasSum.mapL Complex.ofRealCLM).summable).mul_left Complex.I
  apply (hr'.add hi').congr
  intro i
  simpa only [component, Bool.false_eq_true, if_false, if_true,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.comp_def,
    Complex.ofRealCLM_apply] using
    (congr_fun (((NativePaidPacketGroups.token P) s z i).reading x) U).symm

include paid in
theorem value_decomposition (hg : g ≠ 0) (s : R.Mode) (hs : s ≠ R.quiet)
    (z : ℤ) (x : TestSpace D) (U : Config G n) :
    value P s z x U =
      Complex.ofRealCLM
        (NativeBoundedAtomSeries.value
          (fun i : (NativePaidPacketGroups.Fiber P) s z => component ((NativePaidPacketGroups.token P) s z i) x false)
          (fun i => ((NativePaidPacketGroups.token P) s z i).root) U) +
      Complex.I * Complex.ofRealCLM
        (NativeBoundedAtomSeries.value
          (fun i : (NativePaidPacketGroups.Fiber P) s z => component ((NativePaidPacketGroups.token P) s z i) x true)
          (fun i => ((NativePaidPacketGroups.token P) s z i).root) U) := by
  have hr := real_summable paid hg s hs z x false U
  have hi := real_summable paid hg s hs z x true U
  have hr' := (hr.hasSum.mapL Complex.ofRealCLM).summable
  have hi' := ((hi.hasSum.mapL Complex.ofRealCLM).summable).mul_left Complex.I
  unfold value NativeBoundedAtomSeries.value
  rw [show (fun i : (NativePaidPacketGroups.Fiber P) s z => ((NativePaidPacketGroups.token P) s z i).read x U) =
    (fun i => Complex.ofRealCLM
      ((component ((NativePaidPacketGroups.token P) s z i) x false).unmasked U ((NativePaidPacketGroups.token P) s z i).root) +
      Complex.I * Complex.ofRealCLM
      ((component ((NativePaidPacketGroups.token P) s z i) x true).unmasked U ((NativePaidPacketGroups.token P) s z i).root)) from by
      funext i
      simpa only [component, Bool.false_eq_true, if_false, if_true,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.comp_def,
        Complex.ofRealCLM_apply] using
        congr_fun (((NativePaidPacketGroups.token P) s z i).reading x) U]
  rw [hr'.tsum_add hi', tsum_mul_left,
    ← Complex.ofRealCLM.map_tsum hr, ← Complex.ofRealCLM.map_tsum hi]

include paid in
theorem value_grade (hg : g ≠ 0) (s : R.Mode) (hs : s ≠ R.quiet)
    (z : ℤ) (x : TestSpace D) :
    GradeAt (-z).toNat
      (fun A : fieldDir G n 1 => value P s z x (represent A)) := by
  have hb (b : Bool) := NativeBoundedAtomSeries.value_grade
    (fun i : (NativePaidPacketGroups.Fiber P) s z => component ((NativePaidPacketGroups.token P) s z i) x b)
    (fun i => ((NativePaidPacketGroups.token P) s z i).root) paid.width_pos ((NativePaidPacketGroups.rank_le P) s z)
    (budget_summable paid hg s hs z x b) ((NativePaidPacketGroups.grade_le P) s z)
  have hr := GradeAt.linear_contact Complex.ofRealCLM (hb false)
  have hi := GradeAt.linear_contact (Complex.I • Complex.ofRealCLM) (hb true)
  have he := hr.add hi
  convert he using 1
  funext A
  exact value_decomposition paid hg s hs z x (represent A)

omit [DecidableEq V] in
private lemma atom_envelope {ι : Type*} [Countable ι] {r : ι → ℕ} {cap : ℕ}
    (a : (i : ι) → Atom G (r i)) (o : ι → Site n)
    (hw : 0 < width) (hc : ∀ i, r i ≤ cap)
    (hb : Summable (fun i => (a i).budget width)) :
    Envelope (NativeBoundedAtomSeries.value a o) := by
  have hbound (i : ι) (U : Config G n) :
      ‖(a i).unmasked U (o i)‖ ≤ (a i).budget width * (2 : ℝ) ^ cap := by
    calc
      _ ≤ (a i).magnitude * (2 : ℝ) ^ r i := (a i).unmasked_bound U (o i)
      _ ≤ (a i).budget width * (2 : ℝ) ^ r i :=
        mul_le_mul_of_nonneg_right ((a i).lower_budget width hw) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num) (hc i))
        (by unfold Atom.budget Atom.magnitude; positivity)
  refine ⟨Measurable.tsum (fun i => ((a i).unmasked_cont (o i)).measurable),
    (∑' i, (a i).budget width) * (2 : ℝ) ^ cap, fun U => ?_⟩
  have hn := (NativeBoundedAtomSeries.value_summable a o hw hc hb U).norm
  apply (norm_tsum_le_tsum_norm hn).trans
  exact (hn.tsum_le_tsum (fun i => hbound i U) (hb.mul_right _)).trans_eq
    tsum_mul_right

include paid in
theorem value_envelope (hg : g ≠ 0) (s : R.Mode) (hs : s ≠ R.quiet)
    (z : ℤ) (x : TestSpace D) :
    Envelope (value P s z x) := by
  letI : Countable ((NativePaidPacketGroups.Fiber P) s z) := by
    unfold NativePaidPacketGroups.Fiber
    infer_instance
  have he (b : Bool) := atom_envelope
    (fun i : (NativePaidPacketGroups.Fiber P) s z => component ((NativePaidPacketGroups.token P) s z i) x b)
    (fun i => ((NativePaidPacketGroups.token P) s z i).root) paid.width_pos ((NativePaidPacketGroups.rank_le P) s z)
    (budget_summable paid hg s hs z x b)
  obtain ⟨Cr, hr⟩ := (he false).cost
  obtain ⟨Ci, hi⟩ := (he true).cost
  have hv : value P s z x = fun U =>
      Complex.ofRealCLM
        (NativeBoundedAtomSeries.value
          (fun i : (NativePaidPacketGroups.Fiber P) s z => component ((NativePaidPacketGroups.token P) s z i) x false)
          (fun i => ((NativePaidPacketGroups.token P) s z i).root) U) +
      Complex.I * Complex.ofRealCLM
        (NativeBoundedAtomSeries.value
          (fun i : (NativePaidPacketGroups.Fiber P) s z => component ((NativePaidPacketGroups.token P) s z i) x true)
          (fun i => ((NativePaidPacketGroups.token P) s z i).root) U) :=
    funext (value_decomposition paid hg s hs z x)
  rw [hv]
  refine ⟨(Complex.ofRealCLM.continuous.measurable.comp (he false).meas).add
    (measurable_const.mul
      (Complex.ofRealCLM.continuous.measurable.comp (he true).meas)),
    Cr + Ci, fun U => ?_⟩
  apply (norm_add_le _ _).trans
  simpa only [Complex.ofRealCLM_apply, Complex.norm_real, norm_mul,
    Complex.norm_I, one_mul] using
    add_le_add (hr U) (hi U)

include paid in
theorem value_gauge (s : R.Mode) (z : ℤ) (x : TestSpace D) :
    GaugeInvariant (value P s z x) := by
  intro q U
  apply tsum_congr
  intro i
  unfold Token.read
  simp only [Work.F05.slot_gauge]
  exact paid.symmetry i.val ((NativePaidPacketGroups.token P) s z i) ((NativePaidPacketGroups.token_eq P) s z i) x _ _

end YM.Integration.NativePaidPacketSeries
