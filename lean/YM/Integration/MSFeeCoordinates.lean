import YM.FVA2.MixedRates

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

namespace YM.Integration.MSFeeCoordinates

open Finset Matrix
open MS MS.Land MS.Menus MS.Local.Physical
open scoped Classical Polynomial

variable {G : Gauge} {B : Deck G} {d h : ℕ}

abbrev R := PowerSeries (Polynomial ℝ)

def extend (l : h ≤ d) (v : Glyph B h) : Glyph B d :=
  ⟨⟨v.size, Nat.lt_succ_of_le ((Nat.le_of_lt_succ v.1.isLt).trans l)⟩, v.2⟩

def restrict (v : Glyph B d) (l : v.size ≤ h) : Glyph B h :=
  ⟨⟨v.size, Nat.lt_succ_of_le l⟩, v.2⟩

theorem remaining (v : Glyph B d) : v.size ≤ d := Nat.le_of_lt_succ v.1.isLt

theorem extend_restrict (l : h ≤ d) (v : Glyph B d) (a : v.size ≤ h) :
    extend l (restrict v a) = v := rfl

theorem restrict_extend (l : h ≤ d) (v : Glyph B h) :
    restrict (extend l v) (remaining v) = v := rfl

theorem extend_read (v : Glyph B d) :
    extend (remaining v) (Land.read v.2) = v := rfl

theorem restrict_eq_read (i j : Glyph B d) (a : j.size ≤ i.size) :
    restrict j a = Land.read i.2 ↔ j = i := by
  constructor
  · intro e
    exact (extend_restrict (remaining i) j a).symm.trans
      ((congrArg (extend (remaining i)) e).trans (extend_read i))
  · rintro rfl
    rfl

def register (F : Acts B d) (j : Glyph B d) : R :=
  PowerSeries.mk fun k => (F k).register j

def packet (_l : h ≤ d) (F : Acts B h) (j : Glyph B d) : R :=
  if a : j.size ≤ h then register F (restrict j a) else 0

theorem packet_extend (l : h ≤ d) (F : Acts B h) (v : Glyph B h) :
    packet l F (extend l v) = register F v := by
  have hv : (extend l v).size ≤ h := remaining v
  rw [packet, dif_pos hv]
  rfl

def matrix (P : Prescription B) (d : ℕ) : Matrix (Glyph B d) (Glyph B d) R :=
  fun i => packet (remaining i) (P.fees i.size i.2)

theorem head (P : Prescription B) (i j : Glyph B d) (s : i.grade ≤ j.grade) :
    PowerSeries.constantCoeff (matrix P d i j) = if j = i then 1 else 0 := by
  classical
  by_cases l : j.size ≤ i.size
  · rw [matrix, packet, dif_pos l, register, PowerSeries.constantCoeff_mk,
      (P.init i.size i.2).Single (restrict j l) s]
    simp only [restrict_eq_read i j l]
  · have e : j ≠ i := fun e => l (e ▸ le_rfl)
    rw [matrix, packet, dif_neg l, map_zero, if_neg e]

theorem rank_power {ι S : Type*} [Fintype ι] [DecidableEq ι] [Ring S]
    (D : Matrix ι ι S) (w : ι → ℕ) (low : ∀ i j, w i ≤ w j → D i j = 0)
    (m : ℕ) (i j : ι) (hi : w i < m) : (D ^ m) i j = 0 := by
  classical
  induction m generalizing i with
  | zero => omega
  | succ m ih =>
    rw [pow_succ', Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro a _
    by_cases h : w a < m
    · rw [ih a h, mul_zero]
    · rw [low i a (by omega), zero_mul]

theorem constant_unit (P : Prescription B) (d : ℕ) :
    IsUnit ((PowerSeries.constantCoeff (R := Polynomial ℝ)).mapMatrix (matrix P d)) := by
  classical
  let M := (PowerSeries.constantCoeff (R := Polynomial ℝ)).mapMatrix (matrix P d)
  let D := M - 1
  have lo (i j : Glyph B d) (hw : i.grade ≤ j.grade) : D i j = 0 := by
    change PowerSeries.constantCoeff (matrix P d i j) - (1 : Matrix _ _ _) i j = 0
    rw [head P i j hw, Matrix.one_apply]
    by_cases e : i = j <;> simp [e, eq_comm]
  have nil : D ^ (d + 1) = 0 := by
    apply Matrix.ext
    intro i j
    exact rank_power D Glyph.grade lo _ i j (Nat.lt_succ_of_le (Glyph.memory i))
  have hu := IsNilpotent.isUnit_one_add (show IsNilpotent D from ⟨d+1, nil⟩)
  change IsUnit M
  convert hu using 1
  dsimp [D]
  abel

theorem determinant (P : Prescription B) (d : ℕ) : IsUnit (matrix P d).det := by
  rw [PowerSeries.isUnit_iff_constantCoeff,
    (PowerSeries.constantCoeff (R := Polynomial ℝ)).map_det]
  exact ((PowerSeries.constantCoeff (R := Polynomial ℝ)).mapMatrix
    (matrix P d)).isUnit_iff_isUnit_det.mp (constant_unit P d)

theorem unit (P : Prescription B) (d : ℕ) : IsUnit (matrix P d) :=
  (matrix P d).isUnit_iff_isUnit_det.mpr (determinant P d)

def receiver (P : Prescription B) (F : Acts B d) : Glyph B d → R :=
  Matrix.vecMul (register F) (matrix P d)⁻¹

theorem recovering (P : Prescription B) (F : Acts B d) (j : Glyph B d) :
    ∑ i, receiver P F i * matrix P d i j = register F j := by
  change Matrix.vecMul (Matrix.vecMul (register F) (matrix P d)⁻¹) (matrix P d) j = _
  rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (determinant P d), Matrix.vecMul_one]

def evaluate (x : ℝ) : R →+* PowerSeries ℝ :=
  PowerSeries.map (Polynomial.evalRingHom x)

theorem evaluated (F : Acts B d) (j : Glyph B d) (x : ℝ) :
    evaluate x (register F j) = FVA2.Channel.credits j x F := by
  apply PowerSeries.ext
  intro k
  simp [evaluate, register, FVA2.Channel.credits, PowerSeries.coeff_map]

theorem original (P : Prescription B) (F : Acts B d) (j : Glyph B d) (x : ℝ) :
    ∑ i, evaluate x (receiver P F i) * evaluate x (matrix P d i j) =
      FVA2.Channel.credits j x F := by
  rw [← evaluated, ← recovering P F j, map_sum]
  simp only [map_mul]

end YM.Integration.MSFeeCoordinates
