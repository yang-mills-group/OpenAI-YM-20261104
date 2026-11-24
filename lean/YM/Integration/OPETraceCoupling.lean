import YM.FVA2.StratParity
import YM.FVA2.ThePitch
import YM.TraceExtension.Endpoint

/-! Finite evaluation of the independently chosen odd formal scheme
conversion on the actual position-normalized coupling. The trace
comparison retains its numerical quartic remainder at every fixed
truncation of the ordinary conversion series. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.OPETraceCoupling
open Filter Set Asymptotics FVA2 FVA2.Verne FVA2.Plot
open Trace Trace.Pilot Trace.Sundial Trace.Over
open scoped BigOperators Topology Classical

variable {G : Gauge} {F : Labels.Frames G} (p : Hop F)

/-- Ordinary coefficients through degree k+2, evaluated as a finite sum. -/
def finiteCoupling (k : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k+3), p.f j * x^j

def cubicTail (k : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range k, p.f (j+3) * x^j

theorem finite_factor (hp : sloping p) (k : ℕ) (x : ℝ) :
    finiteCoupling p k x = x + x^3 * cubicTail p k x := by
  have h0 : p.f 0 = 0 := p.rooted
  have h2 : p.f 2 = 0 := parity0 hp.1 2 (by decide)
  rw [finiteCoupling, add_comm k 3, Finset.sum_range_add, cubicTail, Finset.mul_sum]
  apply congrArg₂ (· + ·)
  · simp [Finset.sum_range_succ, h0, p.primary, h2]
  · apply Finset.sum_congr rfl
    intro j _
    rw [add_comm 3 j, pow_add]
    ring

private theorem continuous_tail (k : ℕ) : Continuous (cubicTail p k) := by
  unfold cubicTail
  fun_prop

variable {g : ℝ → ℝ} (hg : Coupling G g) (hG : G.Simple)
    (hp : sloping p)

include hg hG hp

theorem ratio (k : ℕ) :
    Tendsto (fun r => finiteCoupling p k (g r) / g r) trail (𝓝 1) := by
  have h0 := hg.conforms hG
  have hh := ((continuous_tail p k).continuousAt (x := 0)).tendsto.comp h0
  have ht : Tendsto (fun r => 1 + (g r)^2 * cubicTail p k (g r)) trail (𝓝 1) := by
    simpa using tendsto_const_nhds.add ((h0.pow 2).mul hh)
  apply ht.congr'
  filter_upwards [hg.positive] with r hr
  rw [finite_factor p hp]
  field_simp [hr.ne']

/-- The finite converted coupling stays on the positive physical branch
and has the original logarithmic running constant. -/
theorem calibrated (k : ℕ) : Coupling G (fun r => finiteCoupling p k (g r)) := by
  have h := ratio p hg hG hp k
  constructor
  · filter_upwards [h.eventually (lt_mem_nhds zero_lt_one), hg.positive] with r hf hr
    exact (div_pos_iff_of_pos_right hr).mp hf
  · have hr := hg.running.mul (h.pow 2)
    simp only [one_pow, mul_one] at hr
    apply hr.congr'
    filter_upwards [hg.positive] with r hl
    field_simp [hl.ne']

theorem squared_error (k : ℕ) :
    (fun r => (finiteCoupling p k (g r))^2 - (g r)^2) =O[trail]
      (fun r => (g r)^4) := by
  let q := cubicTail p k
  let b (x : ℝ) := 2 * q x + x^2 * (q x)^2
  have hq : Continuous q := continuous_tail p k
  have hc : Continuous b := by unfold b; fun_prop
  have hb := (hc.continuousAt (x := 0)).tendsto.comp (hg.conforms hG)
  obtain ⟨C,hC⟩ := isBigO_iff.mp (hb.isBigO_one ℝ)
  refine isBigO_iff.mpr ⟨C, ?_⟩
  filter_upwards [hC] with r hr
  rw [finite_factor p hp, show (g r + (g r)^3 * cubicTail p k (g r))^2 - (g r)^2 =
    b (g r) * (g r)^4 by unfold b q; ring, norm_mul]
  exact mul_le_mul_of_nonneg_right (by simpa using hr) (norm_nonneg _)

/-- A calibrated numerical fourth-order remainder survives conversion of
both the displayed quadratic term and the quantity used to price its error. -/
theorem quartic_remainder (d : ℝ → ℝ) (a : ℝ) (k : ℕ)
    (hd : (fun r => d r - a * (g r)^2) =O[trail] fun r => (g r)^4) :
    (fun r => d r - a * (finiteCoupling p k (g r))^2) =O[trail]
      (fun r => (finiteCoupling p k (g r))^4) := by
  have hi := (isEquivalent_iff_tendsto_one (hg.positive.mono fun _ h => h.ne')).mpr
    (ratio p hg hG hp k)
  have hh := hd.sub ((squared_error p hg hG hp k).const_mul_left a)
  have he : (fun r => d r - a * (finiteCoupling p k (g r))^2) =O[trail]
      (fun r => (g r)^4) := hh.congr_left fun r => by ring
  exact he.trans (hi.isBigO_symm.pow 4)

omit hg hG hp

variable {C : Family G} {f : Extraction.Order} {S : Table C.book}
    {A : Spec.Final C f S} {H : (Climb.Bel C.book).Hierarchy} {Z : Trace.Terrace.Arch C}
    {P P' : ℝ → Spin.change S 4} {κ d e : ℝ → ℝ}

/-- The actual tensor diagnostic on this particular physical comparison,
with the conversion taken from the formal scheme on C's own label tower. -/
theorem physical_trace (p : Hop C.labels) (hp : sloping p)
    (hG : G.Simple) (h : Trace.Target.FieldComparison A H Z P P' κ d e) (k : ℕ) :
    let g := fun r => finiteCoupling p k (glo P' r)
    Coupling G g ∧ (fun r => 4 * d r - (-2*b0 G) * (g r)^2) =O[trail]
      (fun r => (g r)^4) :=
  ⟨calibrated p h.coupling hG hp k,
    quartic_remainder p h.coupling hG hp (fun r => 4*d r) (-2*b0 G) k h.traced_O⟩

/-- Specialization to the actual transfer selected by the common
warehouse's independent continuum MS data and its Wilson calibration. -/
theorem selected_trace (hC : C.Makes) (hV : ∀ i, Bid.pop (C.localSection i))
    {Q : MS.Land.Booked (FVA2.ColorCode.wings G)} (M : MS.Land.MS_Data G Q)
    {c : ℝ} (B : PositionX.Bend.Booth c C.labels) (s : ℝ) (hG : G.Simple)
    (W : Pic.pass (Atoll.share C hC hV) hG M B)
    (h : Trace.Target.FieldComparison A H Z P P' κ d e) (k : ℕ) :
    let p := Forge.transfer (Atoll.share C hC hV) M B s W
    let g := fun r => finiteCoupling p k (glo P' r)
    Coupling G g ∧ (fun r => 4*d r - (-2*b0 G)*(g r)^2) =O[trail]
      (fun r => (g r)^4) :=
  physical_trace _ (turnZ (Atoll.share C hC hV) M B s W) hG h k

end YM.Integration.OPETraceCoupling
