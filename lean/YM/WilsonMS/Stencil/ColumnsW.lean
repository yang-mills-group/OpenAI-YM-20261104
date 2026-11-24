import YM.WilsonMS.Stencil.PureA
/-!
# Instantiate the genuine B^a columns. Discharge strict slot lowering,
no engineering-horizon confusion from lower slots. Keep the compensation on
the very SAME `Survey` (through every order of the nonlinear expansion).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Corrected
open Function Filter Finset Set MeasureTheory XSpace
open Lattice RG Source Labels Maxwell Maxwell.Free Wilson Next.Rank.Normal
open MvPolynomial
open scoped Classical Topology ContDiff BigOperators Pointwise
variable {G : Gauge} {H : Source.Hol G} {d r k : ℕ} (A : Survey G H d)
section degree
variable {I : Type} {p q : poly I} {b : I →₀ ℕ}
open Finsupp

abbrev less (n : ℕ) : Submodule ℂ (poly I) :=
  restrictSupport ℂ (setOf fun x => Finsupp.weight (fun _ => 1) x < n)

lemma has_it (p : poly I) : p ∈ less k ↔ ∀ i ∈ p.support, Finsupp.weight (fun _ => 1) i < k :=
  mem_restrictSupport_iff ..

lemma rank_le (b : I →₀ ℕ) : Finsupp.weight (fun _ => 1) b = b.sum fun _ a => a := by
  simp only [weight_apply]
  simp [sum]

lemma lift_X (h : p ∈ less k) (i : I) : X (R := ℂ) i * p ∈ less (k + 1) := by
  apply (has_it _).mpr
  intro j hj
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp (support_mul _ _ hj)
  rw [support_X] at hx
  rw [map_add, Finset.mem_singleton.mp hx, Finsupp.weight_single, one_smul]
  obtain ht := (has_it _ |>.mp h) y hy
  omega

lemma slit_mild (L : I → ℂ) (p : poly I) (h : p ∈ less (k + 1)) : slit L p ∈ less k := by
  have hx : (slit L) p = ∑ i ∈ p.support, (slit L) (monomial i (MvPolynomial.coeff i p)) := by
    rw [← map_sum, ← as_sum p]
  rw [hx]
  apply Submodule.sum_mem
  intro i hi
  rw [slit, MvPolynomial.mkDerivation_monomial, Finsupp.sum]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro j hj
  rw [smul_eq_mul, mul_comm, MvPolynomial.C_mul']
  apply Submodule.smul_mem
  apply (has_it _).mpr
  intro j' hh
  rw [Finset.mem_singleton.mp (support_monomial_subset hh)]
  obtain hz := (has_it p |>.mp h) i hi
  have hv : single j 1 ≤ i := single_le_iff.mpr (by exact Nat.pos_of_ne_zero (mem_support_iff.mp hj))
  rw [← tsub_add_cancel_of_le hv] at hz
  rw [map_add, weight_single, one_smul] at hz
  omega

lemma detritus (Q : Next.Rank.Normal.Symmetric I) (h : IsWeightedHomogeneous (fun _ => (1 : ℕ)) p k) :
    milk Q p - p ∈ less k := by
  have he (x : I →₀ ℕ) (z : ℂ) :
    milk Q (monomial x z) - monomial x z ∈ less (weight (fun _ => 1) x) := by
    apply Extra.FD.per_factor x
    · change milk Q (C z) - _ ∈ _
      rw [fine]
      exact
        (by
          rw [show C z - monomial (0 : I →₀ ℕ) z = 0 from sub_self _]
          exact Submodule.zero_mem _)
    intro w i hh
    let n := weight (fun _ => (1 : ℕ)) w
    let P := MvPolynomial.monomial w z
    have hv : P ∈ less (n + 1) :=
      (has_it _).mpr
        (fun x hx => by
          rw [mem_singleton.mp (support_monomial_subset hx)]
          exact Nat.lt_succ_self n)
    have hl : milk Q P ∈ less (n + 1) := by
      rw [← sub_add_cancel (milk Q P) P]
      exact
        Submodule.add_mem _
          ((has_it _ |>.mpr fun i hi => ((has_it _ |>.mp hh) _ hi).trans (Nat.lt_succ_self n))) hv
    rw [monomial_add_single, pow_one, mul_comm (monomial w z), feeds]
    rw [show (weight (fun _ => 1) _) = n + 1 from ?_]
    swap
    · rw [map_add, weight_single]
      rfl
    rw [add_sub_right_comm, ← mul_sub]
    exact
      Submodule.add_mem _ (lift_X hh i)
        ((has_it _ |>.mpr fun j hj =>
          ((has_it _ |>.mp (slit_mild (Q.cov i) (milk Q P) hl)) _ hj).trans (Nat.lt_succ_self n)))
  rw [p.as_sum]
  rw [map_sum, ← Finset.sum_sub_distrib]
  exact Submodule.sum_mem _ fun i hi => (h (MvPolynomial.mem_support_iff.mp hi)) ▸ (he i _)

end degree

lemma count_down (p : Label G d) (h : p ∈ Labels.Grade (d, r)) :
    (A.insertW (-1) p).val - p.val ∈ less r :=
  detritus _
    (by
      intro i hi
      obtain hv := (pure_grade _ _) |>.mp h hi
      rw [weight_slot] at hv
      rw [rank_le]
      exact congr_arg Prod.snd hv)

def exactPart (p : Label G d) (i s : ℕ) : Label G d :=
  gradePart (i, s) (A.insertW (-1) p - p)

lemma piece_lit (p : Label G d) (hp : realBar p = p) (i s : ℕ) :
    (exactPart A p i s).val ∈ MS.Theater.Film0 G i s := by
  let X := exactPart A p i s
  apply (MS.Theater.cinema ..).mpr
  refine
    ⟨(pure_grade _ X).mp (gradePart_mem ..), X.property.2,
      congr_arg (fun x : Label G d => x.val) (show realBar X = X from ?_)⟩
  unfold X exactPart
  rw [← gradePart_bar, map_sub, ← A.wick_real, hp]

lemma piece_rank (p : Label G d) (h : p ∈ Labels.Grade (d, r)) (s : ℕ) (hs : r ≤ s) (i) :
    exactPart A p i s = 0 := by
  let v := A.insertW (-1) p - p
  let Q := p.val
  apply Subtype.ext
  change Labels.piece (i, s) v.val = 0
  apply MvPolynomial.ext
  intro j
  unfold Labels.piece
  rw [coeff_weightedHomogeneousComponent, MvPolynomial.coeff_zero]
  split
  swap
  · rfl
  rename_i hj
  rw [weight_slot] at hj
  by_contra hz
  obtain he := (has_it _ |>.mp (count_down A p h)) j (MvPolynomial.mem_support_iff.mpr hz)
  rw [rank_le] at he
  obtain hf := congr_arg Prod.snd hj
  simp only at hf
  omega

lemma labels_split (p : Label G d) (h : p ∈ Labels.Grade (d, r)) :
    A.insertW (-1) p = p + ∑ i ∈ Finset.range (d + 1), ∑ j ∈ Finset.range r, exactPart A p i j := by
  by_cases he : p = 0
  subst p
  simp [exactPart]
  have hp : p.val ≠ 0 := by
    intro hx
    apply he
    exact Subtype.ext hx
  obtain hh := MS.Theater.bipFire ((pure_grade _ p).mp h) hp
  rw [show
      (∑ i ∈ Finset.range (d + 1), ∑ j ∈ Finset.range r, exactPart A p i j) = A.insertW (-1) p - p
      from ?_,
    add_sub_cancel]
  rw [← Labels.decompose (A.insertW (-1) p - p)]
  exact
    Finset.sum_congr rfl fun i _ =>
      Finset.sum_subset (Finset.range_mono (by omega))
        (fun j _ hj =>
          piece_rank A p h j
            (by
              rw [Finset.mem_range] at hj
              omega)
            i)
end YM.WilsonMS.Corrected
