import YM.RG3.Forms.Caption
import YM.RG3.Press.Sitting
/-!
# Counting old support terms behind a slip letter

Only aggregated **representation corrections** use the finite slip factor
alphabet. The supplies & their footprint and per-marker HIT prices are all
on the old explicit labels (no `inf` over presentations here, and no use of
numerical cancellation to meet a Hit hypothesis). Each term touches an
actual flag when used (at the fixed p threshold)---including field-independent
rank zero terms produced on, or moved across, a mask. Exact algebra at n
arbitrary and on entire Config. Downstream analytics holding arbitrary indexes
cannot infer bounds on the flags or analyticity of this identity on a moving
coupling disk; it is an all-field operation at each p, to be implemented on
their side *after* derivative/error estimates holding actual masks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Forms
open Overlay Press Marker Lattice Wilson RG Function MeasureTheory Ac Extra.Trajectories Finset Push.Corrected Push.AbsoluteSums
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {α : Type*} {V : Type*} [DecidableEq V] {R : Census V} {n : Side} {G : Gauge} {p : BudgetPoint} {v : V → Site n}

abbrev Column (R : Census V) (n : Side) := {X : Support n // X.Nonempty} × R.Mode

/-- Simultaneous complete additive corrections. Their quiet-free part is an
addend to the log-polynomial, their quiet part an addend to the ordinary
vacuum/scalar exponent. Sign convention: input = output regular + this
addendum (retain also signed regular remainders on `output`). All footprints
mandatorily visible on the input list. -/
structure Feed (G : Gauge) (n : Side) (R : Census V) (α : Type*) where
  column : α → Column R n
  value : α → Config G n → ℂ

namespace Feed
variable (k : Feed G n R α) {w : V → ℝ}

abbrev mode (i : α) := (k.column i).2
abbrev locus (i : α) := (k.column i).1.val

def domain (c : Column R n) := c.2
-- p-budget numeral geometry can use B-specific hulls independently
abbrev region (c : Column R n) := c.1.val

def hot {R : Census V} (i : R.Mode) := i≠R.quiet
instance (i : R.Mode) : Decidable (hot i) := inferInstanceAs (Decidable (i≠R.quiet))

structure Keeps (p : BudgetPoint) (v : V → Site n) : Prop where
  real i U : ¬ hot (k.mode i) → (k.value i U).im=0
  gauge i : GaugeInvariant (k.value i)
  borel i : Measurable (k.value i)
  read i : UsesFinal p.threshold (k.locus i) (k.value i)
  flags i U : k.value i U≠0 → ¬Healthy p.threshold (k.locus i) U
  origin i U x : k.value i U≠0 → x∈ (k.mode i).val → v x ∈ k.locus i

def bare (U : Config G n) := ∑' i, if hot (k.mode i) then 0 else (k.value i U).re
def text (U : Config G n) := ∑' i, if hot (k.mode i) then Poly.send (k.mode i) (k.value i U) else 0

def office (c : Column R n) := {i : α // k.column i=c}
instance [Countable α] (c : Column R n) : Countable (k.office c) := by unfold office; infer_instance

def address {c : Column R n} (a : k.office c) : α := a.val
lemma address_inj (c : Column R n) : Injective (k.address (c:=c)) := Subtype.val_injective
@[simp] theorem serves (c : Column R n) (a : k.office c) : k.column (k.address a)=c := a.property

def fee (u : α → ℝ) (w : V → ℝ) (B : ℕ) (a : ℝ) x (i : α) :=
  if x∈ k.locus i then Poly.toll w (k.mode i) * u i * Real.exp (a*coverNumber B (k.locus i)) else 0

structure Worth (w : V→ℝ) (B : ℕ) (a : ℝ) (u : α → ℝ) (δ : ℝ) : Prop where
  positive i : 0 ≤ u i
  always i U : ‖k.value i U‖ ≤ u i
  budget : Hit k.locus B (fun i => Poly.toll w (k.mode i)*u i) a δ

namespace Worth
variable {k} {B : ℕ} {a δ : ℝ} {u : α → ℝ} (h : k.Worth w B a u δ)

include h in
/-- For summability only, fixed torus and marker set. Use `fee` root/site
prices for quantitative statements. No controlled constant in V here. -/
lemma enough (ha : 0 ≤ a) (hw : ∀ i,0 < w i) : Summable u := by
  have hs := (Letters.Frame.from_hit B a δ (fun i => Poly.toll w (k.mode i)*u i) (fun i => (k.column i).1.property)
    (fun i => mul_nonneg (Poly.worth hw _).le (h.positive i)) ha h.budget).2.1
  obtain ⟨z,_,hz⟩ := Finset.exists_min_image (univ : Finset R.Mode) (Poly.toll w) (⟨R.quiet,mem_univ _⟩)
  refine (hs.mul_left (Poly.toll w z)⁻¹).of_nonneg_of_le h.positive (fun i => ?_)
  rw [←mul_assoc]
  refine le_mul_of_one_le_left (h.positive i) ?_
  rw [inv_mul_eq_div,le_div_iff₀ (Poly.worth hw _),one_mul]
  exact hz _ (mem_univ _)

include h in
lemma weighted_enough (ha : 0 ≤ a) (hw : ∀ i,0 < w i) : Summable (fun i => Poly.toll w (k.mode i)*u i) :=
  (Letters.Frame.from_hit B a δ _ (fun i => (k.column i).1.property)
    (fun i => mul_nonneg (Poly.worth hw _).le (h.positive i)) ha h.budget).2.1

include h in
lemma usage (ha : 0 ≤ a) (hw : ∀ i,0 <w i) (U) : Summable fun i => ‖k.value i U‖ :=
  (h.enough ha hw).of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => h.always i U)

include h in
lemma quiet_text (ha : 0 ≤ a) (hw : ∀ i,0 < w i) (U) : (k.text U).part R.quiet=0 := by
  let f (i) : Poly R := if hot (k.mode i) then Poly.send (k.mode i) (k.value i U) else 0
  have he : Summable f := (Poly.budgeted hw (h.weighted_enough ha hw) (fun i => show Poly.price w (f i) ≤ _ from by
    unfold f; split
    · rw [Poly.solo]; exact mul_le_mul_of_nonneg_left (h.always i U) (Poly.worth hw _).le
    rw [Poly.zero_price]; exact mul_nonneg (Poly.worth hw _).le (h.positive _))).1
  rw [text,Poly.share he]
  refine (tsum_congr (g:=fun _ => 0) (fun i => ?_)).trans tsum_zero
  unfold f; split
  next hi => exact (Poly.part_send _ _ _).trans (if_neg (Ne.symm hi))
  rfl
end Worth

def row (c : Column R n) (U : Config G n) := ∑' i : k.office c, k.value (k.address i) U

def markRow (c : Column R n) (U : Config G n) := if hot (domain c) then Poly.send (domain c) (k.row c U) else 0
def pureRow (c : Column R n) (U : Config G n) := if hot (domain c) then 0 else (k.row c U).re

def slip (c : Column R n) (U : Config G n) : Poly R := if hot (domain c) then Poly.send (domain c) (k.row c U) else Poly.bead R (Real.exp (k.row c U).re - 1 : ℂ)

lemma used [Countable α] (h : k.Keeps p v) (c : Column R n) : Width.LocalCharge p v (region c) (k.slip c) := by
  have hm : Measurable (k.row c) := Measurable.tsum fun i => h.borel (k.address i)
  have ht (t U) : k.row c (gauge t U) = k.row c U := tsum_congr fun i => h.gauge _ t U
  refine ⟨fun t U => ?_,?_, fun U W ha hb => ?_,fun U i hi x hx => ?_⟩
  · rw [slip,slip,ht]
  · by_cases hi : hot (domain c)
    · unfold slip; simp_rw [if_pos hi]; exact (Bands.sends _).measurable.comp hm
    unfold slip; simp_rw [if_neg hi,Poly.bead]
    exact (Bands.sends R.quiet).measurable.comp ((Complex.continuous_ofReal.measurable.comp (Real.continuous_exp.measurable.comp (Complex.continuous_re.measurable.comp hm))).sub measurable_const)
  · have hi i : k.locus (k.address (c:=c) i) = region c := congrArg (fun x : Column R n => region x) (k.serves c i)
    rw [slip,slip,show k.row c U=k.row c W from tsum_congr (fun i => (hi i ▸ h.read _ : UsesFinal p.threshold (region c) (k.value _)) U W ha hb)]
  unfold slip at hi
  split at hi
  · have he : i=domain c := by by_contra hh; exact hi ((Poly.part_send _ _ _).trans (if_neg hh))
    subst i
    rw [Poly.part_send,if_pos rfl] at hi
    by_contra hX; apply hi
    unfold row
    refine (tsum_congr (g:=fun _ => 0) (fun a => ?_)).trans tsum_zero
    by_contra hO
    have HE := h.origin (k.address a) U x hO
    apply hX
    have Hslot := k.serves _ a
    unfold mode locus at HE
    rw [Hslot] at HE
    exact HE hx
  · change (Poly.send _ _).part _ ≠ 0 at hi
    rw [Poly.part_send] at hi
    have he : i≠R.quiet := by rintro rfl; exact notMem_empty _ hx
    exact (hi (if_neg he)).elim

lemma profits (h : k.Keeps p v) (c : Column R n) (U : Config G n) (he : k.slip c U≠0) : ¬ Healthy p.threshold (region c) U := by
  intro h'
  apply he
  have hr (i:k.office c) : k.value (k.address i) U = 0 := by
    have hi : k.locus (k.address i) = region c := congrArg region (k.serves c i)
    exact not_ne_iff.mp fun H => h.flags _ _ H (hi.symm ▸ h')
  have hs : k.row c U = 0 := Eq.trans (tsum_congr hr) tsum_zero
  unfold slip; rw [hs]; split
  · exact Poly.send_zero _
  simp

lemma admitted (c : Column R n) (U : Config G n) : ((k.slip c U).part R.quiet).im=0 := by
  unfold slip; split
  next h => simp [Ne.symm h]
  simp [Poly.bead]

section Exp
variable [Fintype V]

lemma atom_factor (c : Column R n) (U : Config G n) :
    Poly.bead R (Real.exp (k.pureRow c U) : ℂ)*Poly.pass (k.markRow c U) = 1+k.slip c U := by
  unfold pureRow markRow slip; split
  next h =>
    rw [Real.exp_zero,Complex.ofReal_one,map_one,one_mul]
    exact pass_send (nonempty_iff_ne_empty.mpr (fun H => h (Subtype.ext H))) _
  rw [pass_zero,mul_one]
  have he : (Real.exp ((k.row c U).re) : ℂ)-1 = ((Real.exp ((k.row c U).re)-1:ℝ):ℂ) := by push_cast; rfl
  rw [map_sub,map_one]
  abel

omit [Fintype V] in
lemma roster (U) {B a u δ} (hw : ∀ i,0 < w i) (ha : 0≤a) (h : k.Worth w B a u δ) :
    ∑ c : Column R n,k.markRow c U=k.text U ∧
      ∑ c : Column R n,k.pureRow c U=k.bare U := by
  have H0 := h.usage ha hw U
  have H1 := h.weighted_enough ha hw
  let f i := if hot (k.mode i) then Poly.send (k.mode i) (k.value i U) else 0
  let g i := if hot (k.mode i) then (0:ℝ) else (k.value i U).re
  have he : Summable f := (Poly.budgeted hw H1 fun i => by
    unfold f; split
    · rw [Poly.solo]; exact mul_le_mul_of_nonneg_left (h.always i U) (Poly.worth hw _).le
    exact Poly.zero_price.le.trans (mul_nonneg (Poly.worth hw _).le (h.positive _))).1
  have ho : Summable g := (H0.of_nonneg_of_le (g:=fun i => ‖g i‖) (fun _ => norm_nonneg _) (fun i => by
    unfold g; split
    · exact norm_zero.le.trans (norm_nonneg _)
    exact Complex.abs_re_le_norm _)).of_norm
  have hC (c : Column R n) : Summable (fun i : k.office c => k.value (k.address i) U) := H0.of_norm.comp_injective (k.address_inj c)
  constructor
  · have hsum := he.hasSum.tsum_fiberwise k.column
    change HasSum (fun c => ∑' i : k.office c, f (k.address i)) (k.text U) at hsum
    rw [← hsum.tsum_eq,tsum_fintype]; refine sum_congr rfl fun c _ => ?_
    unfold markRow f; simp_rw [mode, serves]
    unfold domain; split_ifs
    next H =>
      let z : ℂ →+ Poly R := { toFun := Poly.send c.2,map_add' := fun x y => by ext; simp only [Poly.part_plus,Poly.part_send]; split <;> simp, map_zero' := Poly.send_zero _ }
      exact ((hC c).hasSum.map z (Bands.sends _)).tsum_eq.symm
    next H => simp_rw [tsum_zero]
  · have hsum := ho.hasSum.tsum_fiberwise k.column
    change HasSum (fun c => ∑' i : k.office c, g (k.address i)) (k.bare U) at hsum
    rw [← hsum.tsum_eq,tsum_fintype]
    refine sum_congr rfl fun c _ => ?_
    unfold pureRow g; simp_rw [mode,serves]
    unfold domain; split_ifs with hh
    · simp_rw [tsum_zero]
    exact (Complex.reCLM.map_tsum (hC c))

lemma combine (U : Config G n) {B a u δ} (hw : ∀ i,0 < w i) (ha : 0 ≤ a) (h : k.Worth w B a u δ) :
    Poly.bead R (Real.exp (k.bare U):ℂ)*Poly.pass (k.text U) = ∏ c : Column R n,(1+k.slip c U) := by
  classical
  have hF (c) : (k.markRow c U).part R.quiet = 0 := by
    unfold markRow; split
    next he => simp [Ne.symm he]
    rfl
  have he (s : Finset (Column R n)) : Poly.bead R (Real.exp (∑ c∈s,k.pureRow c U) : ℂ) * Poly.pass (∑ c∈s,k.markRow c U)=∏ c∈s,(1+k.slip c U) := by
    induction s using Finset.induction_on with
    | empty => simp only [sum_empty,prod_empty,pass_zero,Real.exp_zero,Complex.ofReal_one,map_one,mul_one]
    | insert c s hc IH =>
      rw [prod_insert hc, sum_insert hc, sum_insert hc, Real.exp_add, pass_add (hF c) (by simp [Poly.part_sum,hF]), Complex.ofReal_mul,map_mul, ← k.atom_factor c U, ← IH]
      ac_rfl
  rw [← (k.roster U hw ha h).1, ← (k.roster U hw ha h).2]; exact he univ
end Exp
end Feed
end YM.RG3.Forms
