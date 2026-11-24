import YM.Integration.LocalComparisonPackets

/-! A finite family of literal marked tokens, with explicit zero padding.
The packet powers and ranks are supplied before all tests and fields.
The full countable read is exactly the finite sum; no tail or completion is
discarded and no prescribed-color or analytic estimate is assumed. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison.MarkedPackets
open Function Finset Lattice Wilson RG Marker
open Comparison.Density.RenderM
open scoped BigOperators Classical

variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V]
  {R : Census V} {D : V → ComparisonDensity.Address.Orbit} {count : ℕ}

private def rankAt (rank : Fin count → ℕ) (i : ℕ) : ℕ :=
  if h : i < count then rank ⟨i, h⟩ else 0

private def tokenAt (rank : Fin count → ℕ)
    (T : (k : Fin count) → Token G n (fun v => (D v).Mood) (rank k))
    (i : ℕ) : Option (Token G n (fun v => (D v).Mood) (rankAt rank i)) := by
  exact if hi : i < count then
    some (by simpa only [rankAt, dif_pos hi] using T ⟨i, hi⟩)
  else none

omit [DecidableEq V] in
private theorem read_cast {a b : ℕ} (h : a = b)
    (P : Token G n (fun v => (D v).Mood) a)
    (x : TestSpace D) (U : Config G n) :
    ((congrArg (fun q => Token G n (fun v => (D v).Mood) q) h.symm).mpr P).read x U =
      P.read x U := by
  cases h
  rfl

/-- Empty finite families are allowed. Padding is genuinely absent and
has the original quiet mode; every present token retains its own rank. -/
def ofFin (mode : Fin count → R.Mode) (rank : Fin count → ℕ)
    (power : Fin count → ℤ)
    (T : (k : Fin count) → Token G n (fun v => (D v).Mood) (rank k))
    (hm : ∀ k, mode k ≠ R.quiet)
    (hg : ∀ k, 0 ≤ power k + (rank k : ℤ)) : MarkedPackets D G n R where
  mode i := if h : i < count then mode ⟨i, h⟩ else R.quiet
  rank := rankAt rank
  power i := if h : i < count then power ⟨i, h⟩ else 0
  packet := tokenAt rank T
  marked i P hp := by
    by_cases hi : i < count
    · simpa only [dif_pos hi] using hm ⟨i, hi⟩
    · simp [tokenAt, hi] at hp
  rankCap := Finset.univ.sup rank
  powerCap := Finset.univ.sup (fun k => (power k).natAbs)
  rank_bounded i P hp := by
    by_cases hi : i < count
    · simpa only [rankAt, dif_pos hi] using
        (Finset.le_sup (f := rank) (Finset.mem_univ (⟨i, hi⟩ : Fin count)))
    · simp [tokenAt, hi] at hp
  power_bounded i P hp := by
    by_cases hi : i < count
    · simpa only [dif_pos hi] using
        (Finset.le_sup (f := fun k => (power k).natAbs)
          (Finset.mem_univ (⟨i, hi⟩ : Fin count)))
    · simp [tokenAt, hi] at hp
  nonnegative_grade i P hp := by
    by_cases hi : i < count
    · simpa only [rankAt, dif_pos hi] using hg ⟨i, hi⟩
    · simp [tokenAt, hi] at hp

variable (mode : Fin count → R.Mode) (rank : Fin count → ℕ)
  (power : Fin count → ℤ)
  (T : (k : Fin count) → Token G n (fun v => (D v).Mood) (rank k))
  (hm : ∀ k, mode k ≠ R.quiet)
  (hg : ∀ k, 0 ≤ power k + (rank k : ℤ))

theorem ofFin_absent (i : ℕ) (hi : count ≤ i) :
    (ofFin mode rank power T hm hg).packet i = none := by
  simp [ofFin, tokenAt, not_lt.mpr hi]

/-- All coupling powers, tests and nonlinear token values remain in the
literal finite sum. The statement also includes zero coupling. -/
theorem ofFin_read [Fintype V] (x : TestSpace D) (g : ℝ) (U : Config G n) :
    (ofFin mode rank power T hm hg).read x g U =
      ∑ k : Fin count, Poly.send (mode k) ((g : ℂ) ^ power k * (T k).read x U) := by
  unfold MarkedPackets.read
  rw [tsum_eq_sum (s := Finset.range count) (fun i hi => ?_)]
  · apply Finset.sum_bij (fun i hi => (⟨i, Finset.mem_range.mp hi⟩ : Fin count))
    · intro i hi
      exact Finset.mem_univ _
    · intro i hi j hj he
      exact congrArg Fin.val he
    · intro k hk
      exact ⟨k.val, Finset.mem_range.mpr k.isLt, rfl⟩
    · intro i hi
      have hit : i < count := Finset.mem_range.mp hi
      have hread := read_cast
        (a := rank ⟨i, hit⟩) (b := rankAt rank i)
        (by simp only [rankAt, dif_pos hit]) (T ⟨i, hit⟩) x U
      simpa only [MarkedPackets.term, ofFin, tokenAt, dif_pos hit] using
        congrArg (fun z => Poly.send (mode ⟨i, hit⟩)
          ((g : ℂ) ^ power ⟨i, hit⟩ * z)) hread
  · have hit : ¬ i < count := by simpa only [Finset.mem_range] using hi
    simp [MarkedPackets.term, ofFin, tokenAt, hit]

end YM.Integration.LocalComparison.MarkedPackets
