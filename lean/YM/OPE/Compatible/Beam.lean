import YM.OPE.Compatible.Catalogue
import YM.OPE.Schemes.Rearrange

/-!
# Active detectors and all-horizon germ

Finite smooth gate, ensuring clearance for *all* the active detectors, not
just one pre-selected truncation. Term at weight w is exactly the tower
coefficient on all sufficiently small r, independently of positions. See
`Display.valid_geometry`: at sufficiently small r on each compact geometry,
every component is well-defined using only separated values and has all its
permutation, unit and real rotation laws.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cov
open Function Set Filter Table Survey MeasureTheory
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {L : Register G} {S : Table L} {I J : Type} [Fintype I] [Fintype J]
namespace Signal
variable (D : Sheets S)

def spare : ℕ → ℝ
  | 0 => gap (D 0)
  | k+1 => min (spare k) (gap (D (k+1)))
lemma spare_pos (w : ℕ) : 0 < spare D w := by
  induction w with
  | zero => exact gap_pos _
  | succ w ih => exact lt_min ih (gap_pos _)
lemma spare_mono : Antitone (spare D) := antitone_nat_of_succ_le (fun _ => min_le_left _ _)
lemma spare_le (w : ℕ) : spare D w ≤ gap (D w) := by cases w <;> first| exact le_rfl| exact min_le_right _ _

-- Gate ensuring arrivals fit also the smoothness neighborhoods for all compact shapes
def period (w : ℕ) : ℝ := spare D w/(4*(w+1:ℝ))
lemma period_pos (w) : 0 < period D w := div_pos (spare_pos D _) (by positivity)
lemma period_mono : Antitone (period D) := fun i j h => by
  change period D j ≤ period D i
  unfold period
  exact (div_le_div_of_nonneg_right (spare_mono D h) (by positivity : 0 ≤ 4*(j+1:ℝ))).trans
    (div_le_div_of_nonneg_left (spare_pos D i).le (by positivity)
      (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.succ_le_succ h) (by norm_num)))
lemma period_zero : Tendsto (period D) atTop (𝓝 (0:ℝ)) := by
  have ht : Tendsto (fun i : ℕ => 4*(i+1:ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  refine squeeze_zero (fun i => (period_pos D i).le) (fun i => ?_)
    (tendsto_const_nhds.div_atTop ht (a:=spare D 0))
  exact div_le_div_of_nonneg_right (spare_mono D (Nat.zero_le i)) (by positivity)

def ramp (w : ℕ) : ContDiffBump (0:ℝ) :=
  ⟨period D w, 2*period D w, period_pos D w, by linarith only [period_pos D w]⟩
lemma off (w : ℕ) {r : ℝ} (hr : 2*period D w < r) : ramp D w r = 0 := by
  apply ContDiffBump.zero_of_le_dist
  change 2*period D w ≤ dist r 0
  rw [Real.dist_0_eq_abs]; exact hr.le.trans (le_abs_self r)
lemma lit (w : ℕ) {r : ℝ} (hr : 0<r) (hl : r≤ period D w) : ramp D w r = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  simpa only [Metric.mem_closedBall,ramp,Real.dist_0_eq_abs,abs_of_pos hr] using hl

/-- Domain on relative positions. Includes Conf even if no active weight. -/
def Valid (r : ℝ) (x : I → E4) : Prop :=
  0 < r ∧ Injective x ∧ ∀ w, r ≤ 2*period D w → Visible D w x
lemma fitEventually (M : ℝ) (I : Type) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ x : I → E4, Injective x → (∀ i, ‖x i‖ ≤ M*r) → Valid D r x := by
  obtain ⟨n,hn⟩ := exists_nat_gt M
  have hh : ∀ᶠ r : ℝ in 𝓝 (0:ℝ), M*r < spare D n :=
    (tendsto_const_nhds.mul tendsto_id).eventually (gt_mem_nhds (by simpa using spare_pos D n))
  filter_upwards [self_mem_nhdsWithin,hh.filter_mono nhdsWithin_le_nhds] with r hr h x hx hu
  change 0 < r at hr
  refine ⟨hr,hx,fun w hw j hj => ⟨hx,fun i => ?_⟩⟩
  apply lt_of_le_of_lt (hu i)
  by_cases hl : w ≤ n
  · exact lt_of_lt_of_le h ((spare_mono D (hj.trans hl)).trans (spare_le ..))
  have hm : M*r ≤ (w+1:ℝ)*r := mul_le_mul_of_nonneg_right (hn.le.trans (le_trans (Nat.cast_le.mpr (le_of_not_ge hl)) (by linarith))) hr.le
  have hz : (w+1:ℝ)*r ≤ spare D w/2 := by
    apply (mul_le_mul_of_nonneg_left hw (show 0 ≤ (w+1:ℝ) by positivity)).trans_eq
    unfold period
    field_simp
    ring
  exact lt_of_le_of_lt (hm.trans hz) ((half_lt_self (spare_pos D w)).trans_le ((spare_mono D hj).trans (spare_le ..)))
omit [Fintype I] [Fintype J] in
lemma permutation (r : ℝ) {x : I → E4} (hx : Valid D r x) (e : J ≃ I) : Valid D r (x ∘ e) :=
  ⟨hx.1,hx.2.1.comp e.injective,fun w hw j hj => sized_perm _ e (hx.2.2 w hw j hj)⟩
omit [Fintype I] in
lemma rotated {r : ℝ} {x : I → E4} (hx : Valid D r x) (K : Ortho) : Valid D r (Ortho.move K ∘ x) :=
  ⟨hx.1,(Ortho.move_injective _).comp hx.2.1, fun w hw j hj => sized_move _ K (hx.2.2 w hw j hj)⟩
end Signal

namespace Display
variable {C : Family G} {f : Extraction.Order} {S : Table C.book} (U : Spec.Final C f S)

-- Particular choices shared across all assertions
abbrev facets := splitting (supplies S) U.phase.transport.spots U.room.kernel
  U.phase.transport.motion U.phase.transport.injection
lemma facets_covariant : (facets U).Covariant U.sector.turns U.room.kernel.spin :=
  covariant _ U.phase.transport.spots U.room.kernel U.phase.transport.motion U.phase.transport.rights U.phase.transport.injection

def legends := Classical.choice (palette (facets U) (facets_covariant U) U.room.kernel)
abbrev Tones := Colour (facets U)

def title (a : Tones U) : S.Tag := ⟨a.fst,(legends U).axis a⟩

variable (p : I → S.Tag)
/-- Our internal, exact coherent vector of matches at the horizon k. Uses
all the detectors through k, no scale gates. -/
def ray (k : ℕ) (x : I → E4) (p : I → S.Tag) (o : E4) : S.Field k :=
  ascend (supplies S) U.sector.derivatives U.sector.turns U.room.kernel.spin k (away x o) p

def lens (a : Tones U) (x : I → E4) (p : I → S.Tag) (o : E4) : ℂ :=
  (legends U).readIn a.fst a (ray U a.fst x p o)
lemma lens_exact (a : Tones U) (x : I → E4) (p : I → S.Tag) (o : E4) (k : ℕ) (hk : a.fst ≤ k) :
    lens U a x p o = (legends U).readIn k a (ray U k x p o) := by
  unfold lens; rw [Catalogue.readIt,Catalogue.readIt]; apply congr_arg
  exact Subtype.ext ((weight_ascend _ U.phase.transport.spots U.room.kernel U.phase.transport.motion U.phase.transport.injection hk (away x o) p).symm)

/-- **The** common OPE coefficient representative. `Coefficients` in all
tested statements refer to this same function. At weight w includes a
smooth gate; no infinite sum at any scale needed to define it. -/
def beam (a : Tones U) (r : ℝ) (x : I → E4) (p : I → S.Tag) (o : E4) : ℂ :=
  (Signal.ramp (supplies S) a.fst r : ℂ) * lens U a x p o

lemma fully (a : Tones U) (k : ℕ) (hk : a.1 ≤ k) {r : ℝ} (hr : 0 < r)
    (hl : r ≤ Signal.period (supplies S) k) (x : I → E4) (p : I → S.Tag) (o : E4) :
    beam U a r x p o = lens U a x p o := by
  unfold beam
  rw [Signal.lit _ _ hr (hl.trans (Signal.period_mono _ hk)),Complex.ofReal_one,one_mul]

lemma beam_finite {r : ℝ} (hr : 0 < r) : ∃ n, ∀ a : Tones U, a ∉ shades (facets U) n →
    ∀ (I : Type) [Fintype I] (x : I → E4) (p : I → S.Tag) o, beam U a r x p o = 0 := by
  have hf : ∀ᶠ n : ℕ in atTop, 2*Signal.period (supplies S) n < r :=
    ((Signal.period_zero (supplies S)).const_mul 2).eventually (gt_mem_nhds (by simpa using hr))
  obtain ⟨n,hn⟩ := hf.exists
  refine ⟨n,fun a ha I _ x p o => ?_⟩
  unfold beam
  have hh : n ≤ a.fst := le_of_lt (not_le.mp (mt (shadows ..).mpr ha))
  rw [Signal.off _ _ (lt_of_le_of_lt (mul_le_mul_of_nonneg_left (Signal.period_mono _ hh) (by norm_num)) hn),
    Complex.ofReal_zero,zero_mul]

/-- Field vector truncation built *directly* from the common C[r]. -/
def trunc (k : ℕ) (r : ℝ) (x : I → E4) (p : I → S.Tag) (o : E4) : S.Field k :=
  ∑ a ∈ shades (facets U) k, beam U a r x p o • (legends U).there k a

lemma trunc_ray (k : ℕ) {r : ℝ} (hr : 0 < r) (hl : r ≤ Signal.period (supplies S) k)
    (x : I → E4) (p : I → S.Tag) (o : E4) : trunc U k r x p o = ray U k x p o := by
  unfold trunc
  conv_rhs => rw [← (legends U).encode U.room.kernel.laws.toSymmetric U.phase.transport.injection k (ray U k x p o)]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [fully U i k ((shadows ..).mp hi) hr hl,lens_exact U i x p o k ((shadows ..).mp hi)]

/-- Convenient domain for beam and later estimators. -/
def Covered (S : Table L) (r : ℝ) (x : I → E4) (o : E4) : Prop := Signal.Valid (supplies S) r (away x o)
lemma valid_geometry (M : ℝ) : ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ (x : I → E4) (o : E4), Injective x →
    (∀ i, ‖x i-o‖ ≤ M*r) → Covered S r x o := by
  filter_upwards [Signal.fitEventually (supplies S) M I] with r hr x o hx hp
  exact hr (away x o) ((away_inject x o).mpr hx) hp
end Display
end YM.OPE.Cov
