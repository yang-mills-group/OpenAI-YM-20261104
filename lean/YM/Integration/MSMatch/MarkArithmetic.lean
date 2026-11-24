import YM.Integration.MSMatch.Conditional

/-!
# Putting product insertions on the conditional log input

RG10 uses ordinary moments when giving separately labelled factors, while
local steps take log inputs. Relate the two in RG10's `Word`, using the
actual occurrence variables (no divided powers of source *names*).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.MSMatch
open Function
open Comparison.RG02 FormalOPE FormalOPE.RG10
open Marker
open scoped Topology BigOperators Classical

namespace MarkArithmetic
open Word

variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V}

omit [Fintype V] in
lemma vac_sing (i : V) (z : Series) : vac R (sing (R.fire i) z) = 0 := by
  have h : R.fire i ≠ R.quiet := fun h => by
    have hj := congrArg Subtype.val h
    simp [Census.fire,Census.quiet] at hj
  simp [Ne.symm h]

omit [Fintype V] in
lemma sq_sing (i : V) (z : Series) : (sing (R.fire i) z)^2 = 0 := by

  apply observe_ext
  intro s
  rw [sq, convolves, see_zero]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  split
  next h =>
    rw [see_sing,see_sing]; split
    next H =>
      split
      next H' =>
        subst a; subst b
        exfalso
        have hc := h.1
        simp [Census.fire] at hc
      simp
    simp
  next => rfl

lemma expMark_sing (i : V) (z : Series) : expMark (sing (R.fire i) z) = 1 + sing (R.fire i) z := by
  unfold expMark
  rw [← Finset.sum_subset (s₁:= Finset.range 2) (Finset.range_mono ?_) ?_]
  · simp [Finset.sum_range_succ]
  · have h : Nonempty V := ⟨i⟩
    have := Fintype.card_pos (α := V)
    omega
  intro b hb hm
  have he : 2 ≤ b := by simpa only [Finset.mem_range,not_lt] using hm
  rw [show b = 2+(b-2) by omega, pow_add, sq_sing, zero_mul, smul_zero]

omit [Fintype V] in
lemma vac_sum (T : Finset V) (f : V → Series) :
    vac R (∑ i ∈ T, sing (R.fire i) (f i)) = 0 := by
  rw [map_sum]
  exact Finset.sum_eq_zero fun i _ => vac_sing i (f i)

lemma emit_from_log_sum (R : Census V) (f : V → Series) :
    expMark (∑ i : V, sing (R.fire i) (f i)) = Word.emit R f := by
  unfold Word.emit
  generalize Finset.univ (α:=V) = B
  induction B using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.prod_empty, ← log_one (R:=R), exp_log (1 : Word R) (map_one _)]
  | @insert i s hi h =>
    rw [Finset.sum_insert hi,Finset.prod_insert hi, Word.exp_add _ _ (vac_sing i _) (vac_sum _ f),
      h, expMark_sing]

lemma singles_at_fire (R : Census V) (f : V → Series) (i : V) :
    see (R.fire i) (∑ i : V, sing (R.fire i) (f i)) = f i := by
  rw [see_sum, Finset.sum_eq_single i]
  · simp
  · intro b _ hb; rw [see_sing, if_neg (fun h => hb ((R.fire_inj ..).mp h.symm))]
  simp

lemma supported_on_fire (R : Census V) (f : V → Series) {s : R.Mode}
    (hs : ¬ ∃ i, R.fire i = s) :
    see s (∑ i : V, sing (R.fire i) (f i)) = 0 := by
  rw [see_sum]
  exact Finset.sum_eq_zero fun i _ => by rw [see_sing, if_neg (fun h => hs ⟨i,h.symm⟩)]

theorem exp_is_emit (R : Census V) (f : V → Series) (A : Word R)
    (hs : ∀ i, see (R.fire i) A = f i)
    (ho : ∀ s, (¬ ∃ i, R.fire i = s) → see s A = 0) :
    expMark A = Word.emit R f := by
  rw [← emit_from_log_sum]
  congr 1
  apply observe_ext
  intro s
  by_cases h : ∃ i, R.fire i = s
  · obtain ⟨i,rfl⟩ := h
    rw [hs i,singles_at_fire]
  rw [ho s h, supported_on_fire R f h]
end MarkArithmetic
end YM.Integration.MSMatch
