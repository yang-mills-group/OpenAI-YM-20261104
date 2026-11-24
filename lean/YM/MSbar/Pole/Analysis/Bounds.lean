import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Tactic

/-!
# Growth seminorms for hard amplitudes in dimensional continuation

All functions in this file are honest functions on real vector spaces. We allow independent
weights for polynomial growth and rapid decay (in momentum variables on a line being
integrated). Use ordinary (not `Within`) derivatives. Taken modulo the requirement that
all derivatives exist on an open domain larger than the sets in the norm; supplied at each
use, not encoded in bounds themselves. Lack of bounds on behavior at infinity in the
*dimension parameter* is intentional; use local compact sets there.
-/

noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole
open Function Set
open scoped Topology ContDiff NNReal BigOperators

universe u
variable {E A F G H : Type} [NormedAddCommGroup E]
  [NormedAddCommGroup A] [NormedAddCommGroup F] [NormedAddCommGroup G] [NormedAddCommGroup H]
  [NormedSpace ℝ E] [NormedSpace ℝ A] [NormedSpace ℝ F] [NormedSpace ℝ G] [NormedSpace ℝ H]

/-- Weights for norms. Always at least 1. -/
structure Price (E : Type u) where
  val : E → ℝ
  one' : ∀ x, 1 ≤ val x

namespace Price
instance : CoeFun (Price E) (fun _ => E → ℝ) := ⟨Price.val⟩
instance : One (Price E) := ⟨⟨fun _ => 1, fun _ => le_rfl⟩⟩
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[simp] lemma one_apply (x : E) : (1 : Price E) x = 1 := rfl
omit [NormedSpace ℝ E] [NormedAddCommGroup E] in
lemma large (p : Price E) (x) : 1 ≤ p x := p.one' x
omit [NormedSpace ℝ E] [NormedAddCommGroup E] in
lemma pos (p : Price E) (x) : 0 < p x := lt_of_lt_of_le zero_lt_one (p.large x)
omit [NormedSpace ℝ E] [NormedAddCommGroup E] in
lemma snap (p : Price E) (x) {i j : ℕ} (h : i ≤ j) : p x ^ i ≤ p x ^ j :=
  pow_le_pow_right₀ (p.large x) h
end Price
/-- `1+‖...‖`. -/
def ticket (f : E → F) : Price E := ⟨fun x => 1+‖f x‖, fun x => by simp⟩
omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] in
@[simp] lemma ticket_apply (f : E → F) (x) : ticket f x = 1+‖f x‖ := rfl

/-- Bounds with polynomial allowance in `grow`, all finite decay orders in `fast`. -/
def Bills (s : Set E) (grow fast : Price E) (f : E → F) :=
  ∀ k : ℕ, ∃ (C : ℝ) (e : ℕ), 0 ≤ C ∧ ∀ x∈s, ‖f x‖ * fast x^k ≤ C * grow x^e

variable {s t : Set E} {grow fast b : Price E} {f g : E → F}

namespace Bills
omit [NormedSpace ℝ E] [NormedAddCommGroup E] [NormedSpace ℝ F]
lemma mono (h : Bills s grow fast f) (hs : t ⊆ s) : Bills t grow fast f := by
  intro k; obtain ⟨C,e,hc,hx⟩ := h k; exact ⟨C,e,hc,fun _ hh => hx _ (hs hh)⟩
lemma congr (h : Bills s grow fast f) (hh : EqOn g f s) : Bills s grow fast g := by
  intro k; obtain ⟨C,e,hc,hx⟩ := h k; refine ⟨C,e,hc,fun x ha => ?_⟩; rw [hh ha]; exact hx x ha
lemma dominates {T : Type} [NormedAddCommGroup T] {g : E → T} (h : Bills s grow fast f)
    (hh : ∀ x∈s, ‖g x‖ ≤ ‖f x‖) : Bills s grow fast g := by
  intro k; obtain ⟨C,e,hc,hx⟩ := h k
  exact ⟨C,e,hc,fun x ha => (mul_le_mul_of_nonneg_right (hh x ha) (pow_nonneg (fast.pos x).le _)).trans (hx _ ha)⟩
lemma union (h : Bills s grow fast f) (j : Bills t grow fast f) : Bills (s ∪ t) grow fast f := by
  intro k; obtain ⟨C,e,hc,hx⟩ := h k; obtain ⟨D,r,hd,hy⟩ := j k
  refine ⟨C+D,max e r,add_nonneg hc hd,fun x hz => ?_⟩; rcases hz with hs|ht
  · refine (hx _ hs).trans (mul_le_mul ?_ (grow.snap _ (le_max_left ..)) (pow_nonneg (grow.pos _).le _) (add_nonneg hc hd)); linarith
  refine (hy _ ht).trans (mul_le_mul ?_ (grow.snap _ (le_max_right ..)) (pow_nonneg (grow.pos _).le _) (add_nonneg hc hd)); linarith
lemma const (c : F) : Bills s grow 1 (fun _ => c) := fun k => ⟨‖c‖,0,norm_nonneg _,by simp⟩
lemma zero : Bills s grow fast (fun _ => (0 : F)) := fun k => ⟨0,0,le_rfl,by simp⟩
lemma norm (h : Bills s grow fast f) : Bills s grow fast (fun x => ‖f x‖) :=
  h.dominates (by simp)
lemma weakening (h : Bills s grow fast f) (hh : Bills s fast 1 (fun x => b x)) : Bills s grow b f := by
  intro k; obtain ⟨C,e,hc,hx⟩ := hh 0
  obtain ⟨D,r,hd,hy⟩ := h (e*k)
  refine ⟨C^k*D,r,mul_nonneg (pow_nonneg hc _) hd,fun x hz => ?_⟩
  have hb : b x ^ k ≤ (C*fast x^e)^k := by
    apply pow_le_pow_left₀ ((b.pos _).le)
    simpa [Real.norm_of_nonneg (b.pos x).le] using hx x hz
  refine (mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans ?_
  rw [mul_pow,← pow_mul,mul_left_comm,mul_assoc (a:=C^k) (b:=D)]
  exact mul_le_mul_of_nonneg_left (hy x hz) (pow_nonneg hc _)
lemma growing (h : Bills s grow fast f) (hh : Bills s b 1 (fun x => grow x)) : Bills s b fast f := by
  obtain ⟨C,e,hc,hx⟩ := hh 0
  intro k; obtain ⟨D,r,hd,hy⟩ := h k
  refine ⟨D*C^r,e*r,mul_nonneg hd (pow_nonneg hc _),fun x hz => ?_⟩
  have hb : grow x ^ r ≤ (C*b x^e)^r := by
    apply pow_le_pow_left₀ ((grow.pos _).le)
    simpa [Real.norm_of_nonneg (grow.pos x).le] using hx x hz
  exact (hy x hz).trans ((mul_le_mul_of_nonneg_left hb hd).trans_eq (by rw [mul_pow,← pow_mul,mul_assoc]))
lemma add (hf : Bills s grow fast f) (hg : Bills s grow fast g) : Bills s grow fast (fun x => f x+g x) := by
  intro k; obtain ⟨C,e,hc,hx⟩ := hf k; obtain ⟨D,r,hd,hy⟩ := hg k
  refine ⟨C+D,max e r,add_nonneg hc hd,fun x hz => ?_⟩; rw [add_mul]
  refine (mul_le_mul_of_nonneg_right (norm_add_le _ _) (pow_nonneg (fast.pos _).le _)).trans ?_; rw [add_mul]
  exact add_le_add ((hx _ hz).trans (mul_le_mul_of_nonneg_left (grow.snap _ (le_max_left ..)) hc))
    ((hy _ hz).trans (mul_le_mul_of_nonneg_left (grow.snap _ (le_max_right ..)) hd))
lemma mul {f g : E → ℝ} (hf : Bills s grow fast f) (hg : Bills s grow 1 g) :
    Bills s grow fast (fun x => f x*g x) := by
  obtain ⟨D,r,hd,hy⟩ := hg 0; intro k; obtain ⟨C,e,hc,hx⟩ := hf k
  refine ⟨C*D,e+r,mul_nonneg hc hd,fun x hz => ?_⟩; rw [norm_mul,mul_right_comm,pow_add,mul_mul_mul_comm C]
  exact mul_le_mul (hx _ hz) (by simpa using hy _ hz) (norm_nonneg _) (mul_nonneg hc (pow_nonneg (grow.pos _).le _))
lemma sum {ι : Type*} (I : Finset ι) (v : ι → E → F) (H : ∀ i∈I, Bills s grow fast (v i)) :
    Bills s grow fast (fun x => ∑ i ∈ I, v i x) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using (Bills.zero (F:=F) (s:=s) (grow:=grow) (fast:=fast))
  | @insert i I h ih =>
    simpa only [Finset.sum_insert h] using (H i (Finset.mem_insert_self ..)).add (ih fun i hi => H i (Finset.mem_insert_of_mem hi))
end Bills

/-- Same seminorm at every jet order. -/
def Pays (s : Set E) (grow fast : Price E) (f : E → F) :=
    ∀ j, Bills s grow fast (iteratedFDeriv ℝ j f)

/-- Payload with its ambient differentiability on the closed measuring patch (or any set;
we will take unions of such patches). -/
structure Packet (s : Set E) (grow fast : Price E) (f : E → F) : Prop where
  smooth : ∀ x∈s, ContDiffAt ℝ ∞ f x
  budget : Pays s grow fast f

namespace Packet
lemma mono (h : Packet s grow fast f) (hs : t ⊆ s) : Packet t grow fast f :=
  ⟨fun _ hm => h.smooth _ (hs hm),fun j => (h.budget j).mono hs⟩
lemma union (h : Packet s grow fast f) (j : Packet t grow fast f) : Packet (s ∪ t) grow fast f :=
  ⟨fun x hh => Or.elim hh (h.smooth x) (j.smooth x),fun i => (h.budget i).union (j.budget i)⟩
lemma values (h : Packet s grow fast f) : Bills s grow fast f := by
  intro k; obtain ⟨C,e,hc,hb⟩ := h.budget 0 k; exact ⟨C,e,hc,by simpa using hb⟩
lemma weakening (h : Packet s grow fast f) (hh : Bills s fast 1 (fun x => b x)) : Packet s grow b f :=
  ⟨h.smooth, fun i => (h.budget i).weakening hh⟩
lemma growing (h : Packet s grow fast f) (hh : Bills s b 1 (fun x => grow x)) : Packet s b fast f :=
  ⟨h.smooth, fun i => (h.budget i).growing hh⟩
lemma zero : Packet s grow fast (fun _ : E => (0 : F)) := by
  refine ⟨fun _ _ => contDiffAt_const, fun j => ?_⟩
  intro k; exact ⟨0,0,le_rfl, by simp⟩
lemma congr (h : Packet s grow fast f) (hh : ∀ x∈s,g =ᶠ[nhds x] f) : Packet s grow fast g :=
  ⟨fun x hx => (h.smooth _ hx).congr_of_eventuallyEq (hh x hx), fun i => (h.budget i).congr (fun y hy => ((hh y hy).iteratedFDeriv ℝ i).eq_of_nhds)⟩
lemma add (hf : Packet s grow fast f) (hg : Packet s grow fast g) : Packet s grow fast (fun x => f x+g x) :=
  ⟨fun x hx => (hf.smooth x hx).add (hg.smooth x hx), fun i => ((hf.budget i).add (hg.budget i)).congr
    (fun x hx => iteratedFDeriv_add_apply ((hf.smooth x hx).of_le (by exact_mod_cast (show (↑i:ℕ∞) ≤ ⊤ from le_top))) ((hg.smooth x hx).of_le (by exact_mod_cast (show (↑i:ℕ∞) ≤ ⊤ from le_top))))⟩
lemma bilinear {g : E → G} (hf : Packet s grow fast f) (hg : Packet s grow 1 g) (L : F →L[ℝ] G →L[ℝ] H) :
    Packet s grow fast (fun x => L (f x) (g x)) := by
  refine ⟨fun x hx => L.isBoundedBilinearMap.contDiff.contDiffAt.comp x ((hf.smooth x hx).prodMk (hg.smooth x hx)),fun n => ?_⟩
  let w : ℕ → E → ℝ := fun i x => (n.choose i) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n-i) g x‖
  have hw (i : ℕ) : Bills s grow fast (w i) := by
    simp_rw [w,mul_comm (↑(n.choose _) : ℝ)]; exact (((hf.budget i).norm.mul (Bills.const _)).mul (hg.budget (n-i)).norm)
  have hz := (Bills.sum (Finset.range (n+1)) w fun i _ => hw i).mul (Bills.const ‖L‖)
  refine hz.dominates (fun x hx => ?_)
  have hf' : ContDiffAt ℝ n f x := (hf.smooth x hx).of_le (by exact_mod_cast (show (↑n:ℕ∞) ≤ ⊤ from le_top))
  have hg' : ContDiffAt ℝ n g x := (hg.smooth x hx).of_le (by exact_mod_cast (show (↑n:ℕ∞) ≤ ⊤ from le_top))
  obtain ⟨t,ht,ho,hy⟩ := mem_nhds_iff.mp ((hf'.eventually (by simp)).and (hg'.eventually (by simp)))
  have hh := L.norm_iteratedFDerivWithin_le_of_bilinear (s:=t) (ho.contDiffOn_iff.mpr fun _ hh => (ht hh).1)
    (ho.contDiffOn_iff.mpr fun _ hh => (ht hh).2) ho.uniqueDiffOn hy (n:=n) (by exact le_rfl)
  simp_rw [iteratedFDerivWithin_of_isOpen _ ho hy] at hh
  dsimp
  rw [mul_comm _ ‖L‖]
  exact hh.trans (le_abs_self _)
lemma fderiv (h : Packet s grow fast f) : Packet s grow fast (fderiv ℝ f) := by
  refine ⟨fun _ hx => (h.smooth _ hx).fderiv_right (m:=∞) ?_, fun i k => ?_⟩
  · simp
  obtain ⟨C,e,hc,hb⟩ := h.budget (i+1) k; refine ⟨C,e,hc,?_⟩
  simpa only [iteratedFDeriv_succ_eq_comp_right, comp_apply, LinearIsometryEquiv.norm_map] using hb
lemma apply {X : F →L[ℝ] H} (h : Packet s grow fast f) : Packet s grow fast (fun x => X (f x)) := by
  refine ⟨fun _ hx => X.contDiff.contDiffAt.comp _ (h.smooth _ hx), fun i => ?_⟩
  refine ((h.budget i).norm.mul (Bills.const ‖X‖)).dominates (fun x hx => ?_)
  have hh := X.norm_iteratedFDeriv_comp_left (h.smooth _ hx) (n:=i) (by exact_mod_cast (show (↑i:ℕ∞) ≤ ⊤ from le_top))
  rw [mul_comm]
  exact hh.trans (le_abs_self _)
end Packet
end YM.MSbar.Pole
