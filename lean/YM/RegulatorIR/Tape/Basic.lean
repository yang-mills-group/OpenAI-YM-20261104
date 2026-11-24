import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
/-!
# Weighted tapes for connected cover diagrams

A tape is an array of coefficients retaining its addresses (words) explicitly. Use the ℓ¹
costs and support predicates when pushing tapes through *infinite* kernels. Elementary operators
(trace, fusion, substitutions, periodization) will be given on *one word*, and extended with this
toolkit. Bounds do not imply any identities of operators acting outside their absolute-summability
domain; no reliance on a convention for evaluating a divergent signed sum.
-/
noncomputable section
namespace YM.RegulatorIR
open scoped ENNReal NNReal BigOperators Classical

abbrev Weight (ι : Type*) := ι → ℝ≥0
abbrev Tape (ι : Type*) := ι → ℝ

namespace Tape

variable {ι κ α β γ : Type*}

def tally (w : Weight α) (f : Tape α) := ∑' i, ‖f i‖ₑ * w i
abbrev Carried (f : Tape α) (w : Weight α) : Prop := tally w f < ∞

def mass (f : Tape α) := ∑' i, ‖f i‖ₑ

@[simp] lemma tally_one (f : Tape α) : tally 1 f = mass f := by simp [tally,mass]

def Within (S : Set α) (f : Tape α) := ∀ i, f i ≠ 0 → i ∈ S

namespace Within
variable {S T : Set α} {f g : Tape α}
lemma weaken (h : Within S f) (hS : S ⊆ T) : Within T f := fun i hi => hS (h i hi)
lemma implies (h : Within S f) (hg : ∀ i, g i ≠ 0 → f i ≠ 0) : Within S g := fun i hi => h i (hg i hi)
@[simp] lemma full (f : Tape α) : Within Set.univ f := fun _ _ => trivial
lemma outside (h : Within S f) {i : α} (hi : i ∉ S) : f i = 0 := by_contra fun hf => hi (h i hf)
lemma of_outside (h : ∀ i ∉ S, f i = 0) : Within S f := fun i hi => by_contra fun hS => hi (h i hS)
@[simp] lemma zero (S : Set α) : Within S 0 := of_outside fun _ _ => rfl
lemma smul (h : Within S f) (x : ℝ) : Within S (x • f) := h.implies fun _ hi => right_ne_zero_of_mul hi
lemma add (hf : Within S f) (hg : Within S g) : Within S (f + g) := of_outside fun i hi => by simp only [Pi.add_apply,hf.outside hi,hg.outside hi,add_zero]
lemma sub (hf : Within S f) (hg : Within S g) : Within S (f - g) := of_outside fun i hi => by simp only [Pi.sub_apply,hf.outside hi,hg.outside hi,sub_zero]
lemma neg (hf : Within S f) : Within S (-f) := of_outside (fun i hi => by rw [Pi.neg_apply,hf.outside hi,neg_zero])
lemma sum {F : ι → Tape α} {s : Finset ι} (hf : ∀ i ∈ s, Within S (F i)) : Within S (∑ i∈s,F i) := of_outside (fun x hx => by simp only [Finset.sum_apply]; apply Finset.sum_eq_zero; exact fun i hi => (hf i hi).outside hx)
lemma tsum {F : ι → Tape α} (hf : ∀ i, Within S (F i)) : Within S (fun x => ∑' i, F i x) := of_outside (fun x hx => by simp only [(hf _).outside hx, tsum_zero])
end Within

lemma tally_mono_on {f : Tape α} {w w' : Weight α} (h : ∀ x, f x ≠ 0 → w x ≤ w' x) : tally w f ≤ tally w' f :=
  ENNReal.tsum_le_tsum fun i => by
    by_cases hi : f i = 0
    · simp [hi]
    exact mul_le_mul_right (ENNReal.coe_le_coe.mpr (h i hi)) _

lemma tally_mono {f : Tape α} {w w' : Weight α} (h : w ≤ w') : tally w f ≤ tally w' f := tally_mono_on (fun i _ => h i)
lemma point (w : Weight α) (f : Tape α) (i : α) : ‖f i‖ₑ * w i ≤ tally w f := ENNReal.le_tsum i
@[simp] lemma tally_zero (w : Weight α) : tally w (0 : Tape α) = 0 := by simp [tally]
@[simp] lemma tally_neg (w : Weight α) (f : Tape α) : tally w (-f)= tally w f := by simp [tally]
@[simp] lemma tally_smul (w : Weight α) (k : ℝ) (f : Tape α) : tally w (k • f) = ‖k‖ₑ * tally w f := by
  simp_rw [tally, Pi.smul_apply, smul_eq_mul, enorm_mul,mul_assoc, ENNReal.tsum_mul_left]
lemma tally_add (w : Weight α) (f g : Tape α) : tally w (f + g) ≤ tally w f + tally w g := by
  unfold tally; rw [← ENNReal.tsum_add]; apply ENNReal.tsum_le_tsum; intro a
  rw [Pi.add_apply, ← add_mul]; exact mul_le_mul_left (enorm_add_le ..) _
lemma tally_sub (w : Weight α) (f g : Tape α) : tally w (f - g) ≤ tally w f + tally w g := by
  simpa only [sub_eq_add_neg,tally_neg] using tally_add w f (-g)
lemma tally_sum (w : Weight α) (F : ι → Tape α) (s : Finset ι) : tally w (∑ i∈s,F i) ≤ ∑ i∈s,tally w (F i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi,Finset.sum_insert hi]; exact (tally_add ..).trans (add_le_add le_rfl ih)
lemma tally_tsum (w : Weight α) (F : ι → Tape α) : tally w (fun x => ∑' i, F i x) ≤ ∑' i, tally w (F i) := by
  unfold tally; rw [ENNReal.tsum_comm]
  refine ENNReal.tsum_le_tsum fun x => ?_
  rw [ENNReal.tsum_mul_right]
  exact mul_le_mul_left enorm_tsum_le_tsum_enorm _

lemma tally_product (w : Weight α) (v : Weight β) (f : α → ℝ) (g : β → ℝ) :
    tally (fun p : α × β => w p.1 * v p.2) (fun p => f p.1 * g p.2) = tally w f * tally v g := by
  unfold tally; simp_rw [enorm_mul,ENNReal.coe_mul]
  rw [show (∑' p : α × β, (‖f p.1‖ₑ * ‖g p.2‖ₑ) * ((w p.1:ℝ≥0∞) * v p.2)) =
      ∑' p : α × β, (‖f p.1‖ₑ * w p.1) * (‖g p.2‖ₑ * v p.2) from tsum_congr fun _ => mul_mul_mul_comm ..]
  rw [ENNReal.tsum_prod (f:=fun i j => (‖f i‖ₑ * w i) * (‖g j‖ₑ * v j))]; simp_rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]

def Lower (w : Weight α) := ∃ b : ℝ≥0, 0 < b ∧ ∀ i, b ≤ w i
@[simp] lemma lower_one : Lower (1 : Weight α) := ⟨1,zero_lt_one,fun _ => le_rfl⟩
lemma lower_mono {w w' : Weight α} (h : Lower w) (hh : w ≤ w') : Lower w' := by
  obtain ⟨b,hb,h⟩ := h; exact ⟨b,hb,fun i => (h i).trans (hh i)⟩
lemma Lower.product {w : Weight α} {v : Weight β} (h : Lower w) (hh : Lower v) :
    Lower (fun p : α × β => w p.1 * v p.2) := by
  obtain ⟨b,hb,h⟩:=h; obtain ⟨c,hc,hh⟩:=hh
  exact ⟨b*c,mul_pos hb hc,fun p => mul_le_mul' (h p.1) (hh p.2)⟩
lemma mass_lt_top {w : Weight α} {f : Tape α} (hw : Lower w) (hf : Carried f w) : mass f < ∞ := by
  obtain ⟨b,hb,he⟩ := hw
  have H : tally (fun _ => b) f < ∞ := (tally_mono (w:=fun _ => b) he).trans_lt hf
  rw [tally,ENNReal.tsum_mul_right] at H
  by_contra! hk; rw [top_le_iff] at hk
  change mass f * _ < _ at H; rw [hk, ENNReal.top_mul] at H
  · exact lt_irrefl _ H
  exact_mod_cast hb.ne'
lemma plain_summable {f : Tape α} (hf : mass f < ∞) : Summable f := (tsum_enorm_ne_top_iff_summable_norm.mp hf.ne).of_norm
lemma Carried.summable {w : Weight α} {f : Tape α} (hf : Carried f w) (hw : Lower w) : Summable f := plain_summable (mass_lt_top hw hf)
lemma Carried.add {f g : Tape α} {w : Weight α} (hf : Carried f w) (hg : Carried g w) : Carried (f+g) w :=
  (tally_add ..).trans_lt (ENNReal.add_lt_top.mpr ⟨hf,hg⟩)
lemma Carried.sub {f g : Tape α} {w : Weight α} (hf : Carried f w) (hg : Carried g w) : Carried (f-g) w :=
  (tally_sub ..).trans_lt (ENNReal.add_lt_top.mpr ⟨hf,hg⟩)
lemma Carried.neg {f : Tape α} {w : Weight α} (hf : Carried f w) : Carried (-f) w := by unfold Carried; rw [tally_neg]; exact hf
lemma Carried.smul {f : Tape α} {w : Weight α} (hf : Carried f w) (a : ℝ) : Carried (a • f) w := by
  unfold Carried; rw [tally_smul]; exact ENNReal.mul_lt_top (enorm_lt_top (x:=a)) hf
lemma Carried.sum {F : ι → Tape α} {s : Finset ι} {w : Weight α} (h : ∀ i∈s, Carried (F i) w) : Carried (∑ i∈s,F i) w :=
  (tally_sum ..).trans_lt <| ENNReal.sum_lt_top.mpr h

/-- Single address. -/
def atOne (x : α) : Tape α := fun y => if y=x then 1 else 0
lemma tally_at (w : Weight α) (x : α) : tally w (atOne x) = w x := by
  unfold tally atOne; rw [tsum_eq_single x]; simp; intro i hi; simp [hi]
lemma within_at {x : α} {S : Set α} (hx : x ∈ S) : Within S (atOne x) := fun y h => by
  by_cases he : y=x; exact he ▸ hx
  exact (h (if_neg he)).elim
lemma mass_single (x : α) : mass (atOne x)=1 := by rw [← tally_one,tally_at]; rfl
end Tape
end YM.RegulatorIR
