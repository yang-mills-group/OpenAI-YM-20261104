import YM.WilsonMS.Scales.GradeW
/-!
# Engineering filtration and unit preservation

The `Ladder` condition is on compatible grade extensions for field matrices.
Actual parameter deformations keep `stand` and `Formal`, even in the presence
of singular growth before ending. Here only algebraic transformations.
`CloseP` asks additionally for near-free leading (= identity); latter not
assumed of arbitrary finite-regulator matrices.
-/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.GFlow
open Function Set Filter MeasureTheory Real Finset Metric
open XSpace XSpace.Normalize XSpace.Expense XSpace.Cirrus XSpace.TestBudget XSpace.Structure1
open Maxwell Maxwell.Free Maxwell.Wick VisitH
open MS MS.Menus MS.Theater MS.Land MS.Book MS.Book.Program MS.Book.Convolve
open PowerSeries (coeff mk X C constantCoeff invOfUnit)
open Fiscal BMenu Rider Reservoir VisitH Sea Fray FrameConj FrameConj.Gates Ice
open scoped BigOperators Topology Classical ContDiff
variable {G : Gauge} {d k n m j : ℕ}
local notation "BΨ" => Ensure.deck G

abbrev Ladder (F : Guard G (d + 1)) (T : Guard G d) : Prop :=
  ∀ n x, coeff n F (Normalize.step d x) = Normalize.step d (coeff n T x)
variable {P Q T : Guard G d} {U V : Guard G (d + 1)}
section algebra

@[simp]
lemma coefficients_mul (P Q : Guard G d) (j : ℕ) (v : Sec G d) :
    coeff j (P * Q) v = ∑ i ∈ Finset.antidiagonal j, coeff i.1 P (coeff i.2 Q v) := by
  rw [PowerSeries.coeff_mul]
  exact LinearMap.sum_apply ..

lemma Ladder.product (h : Ladder U P) (hp : Ladder V Q) : Ladder (U * V) (P * Q) := by
  intro n x
  rw [coefficients_mul, coefficients_mul, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [hp, h]

lemma Ladder.one : Ladder (1 : Guard G (d + 1)) 1 := by
  intro n v
  rw [PowerSeries.coeff_one, PowerSeries.coeff_one]
  split_ifs
  · rfl
  simp

lemma Ladder.C (v : FieldEnd G d) (T : FieldEnd G (d + 1)) (h : ∀ x, T (step d x) = step d (v x)) :
    Ladder (PowerSeries.C T) (PowerSeries.C v) := by
  intro i p
  rw [PowerSeries.coeff_C, PowerSeries.coeff_C]
  split_ifs
  exact h p
  simp

lemma Ladder.edit (h : Ladder U P) (c : Cn) : Ladder (coupon c U) (coupon c P) := by
  intro n x
  unfold coupon
  simp_rw [PowerSeries.coeff_mk, rules, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    h]

abbrev CloseP (P : Guard G d) :=
  Formal P ∧ constantCoeff P = 1
namespace CloseP

lemma right : CloseP (1 : Guard G d) :=
  ⟨Formal.one G d, map_one _⟩

lemma zeroC (h : CloseP P) : coeff 0 P = 1 :=
  (PowerSeries.coeff_zero_eq_constantCoeff_apply P).trans h.2

lemma times (h : CloseP P) (hv : CloseP Q) : CloseP (P * Q) :=
  ⟨h.1.product hv.1, (by rw [map_mul, h.2, hv.2, one_mul])⟩

lemma substitute (h : CloseP P) {c : Cn} (hx : Clean c) : CloseP (coupon c P) :=
  ⟨turn_seed h.1 hx, (turn0 c).trans h.2⟩
end CloseP

def vault (X : Guard G d) :=
  invOfUnit X 1

lemma antidote (h : CloseP P) : P * vault P = 1 ∧ vault P * P = 1 :=
  ⟨PowerSeries.mul_invOfUnit _ _ h.2, PowerSeries.invOfUnit_mul _ _ h.2⟩

lemma CloseP.invert (h : CloseP P) : CloseP (vault P) := by
  obtain ⟨W, hW, hX, hP⟩ := reversal_exists h.1
  rw [show vault P = W from (by rw [← one_mul (vault P), ← hX, mul_assoc, (antidote h).1, mul_one])]
  refine ⟨hW, ?_⟩
  obtain hh := congr_arg constantCoeff hX
  rw [map_mul, h.2, mul_one, map_one] at hh
  exact hh

lemma positiveC (h : CloseP P) (hi : j ≠ 0) : coeff j P ∈ Change G d := by
  obtain ⟨p, hp⟩ := h.1.actions
  rw [hp, pos_decked _ hi]
  exact (p j).property

lemma Ladder.turnback (h : Ladder U P) (hp : CloseP P) (hs : CloseP U) : Ladder (vault U) (vault P) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x
    by_cases ht : n = 0
    · subst n
      rw [hs.invert.zeroC, hp.invert.zeroC]
      rfl
    let S := Finset.antidiagonal n
    let A := S.erase (0, n)
    have he : (0, n) ∈ S := by simp [S]
    have hI {a : ℕ} (U : Guard G a) (h : CloseP U) (p : Sec G a) :
      coeff n (vault U) p = -∑ i ∈ A, coeff i.1 U (coeff i.2 (vault U) p) := by
      obtain H := (antidote h).1
      have hL : ∑ i ∈ S, coeff i.1 U (coeff i.2 (vault U) p) = 0 := by
        rw [← coefficients_mul, H, PowerSeries.coeff_one, if_neg ht, LinearMap.zero_apply]
      rw [← Finset.add_sum_erase _ _ he, h.zeroC, Module.End.one_apply] at hL
      exact eq_neg_of_add_eq_zero_left hL
    rw [hI U hs, hI P hp, map_neg, map_sum]
    congr 1
    exact
      Finset.sum_congr rfl fun i hi => by
        have H := Finset.mem_erase.mp hi
        obtain hx := Finset.mem_antidiagonal.mp H.2
        have hi : i.2 < n :=
          Nat.lt_of_le_of_ne (by omega) fun he =>
            H.1
              (Prod.ext
                (by
                  dsimp
                  omega)
                he)
        rw [ih _ hi, h]
end algebra

section grade

def printM (P : Guard G d) : Guard G d :=
  mk fun i => shadows (coeff i P)

abbrev Mass (P : Guard G d) :=
  printM P = P

abbrev PureDrop (P : Guard G d) :=
  printM P = 1

lemma printed (i : ℕ) : coeff i (printM P) = shadows (coeff i P) :=
  PowerSeries.coeff_mk ..

lemma Mass.exactly (h : Mass P) (i : ℕ) : Flat (coeff i P) :=
  (printed (P := P) _).symm.trans (congr_arg (coeff i) h)

lemma Mass.print : Mass (printM P) :=
  PowerSeries.ext fun i => by
    rw [printed, printed]
    exact Flat.freedom _

lemma filter_emb (hp : CloseP P) (i : ℕ) : Tier (coeff i P) := by
  by_cases he : i = 0
  · subst i
    rw [hp.zeroC]
    exact tierFlat (tile_one d)
  exact tier_change (⟨_, positiveC hp he⟩ : Change G d)

lemma print1 : Mass (1 : Guard G d) := by
  refine PowerSeries.ext fun n => ?_
  rw [printed, PowerSeries.coeff_one]
  split_ifs
  exact tile_one d
  exact tile_zero ..

lemma print_prod (hp : CloseP P) (hQ : CloseP Q) : printM (P * Q) = printM P * printM Q := by
  refine PowerSeries.ext fun i => ?_
  rw [printed, PowerSeries.coeff_mul, PowerSeries.coeff_mul, tile_total]
  exact
    Finset.sum_congr rfl fun v _ => by
      rw [mul_diag (filter_emb hp _) (filter_emb hQ _), printed, printed]

lemma printH (hp : CloseP P) : CloseP (printM P) := by
  have he : constantCoeff (printM P) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, printed, hp.zeroC, tile_one]
  refine ⟨makeDeck 0 (he.symm ▸ isUnit_one) (he.trans (stand0 d).symm) (fun i hi => ?_), he⟩
  rw [printed]
  exact tile_change (⟨_, positiveC hp hi⟩ : Change G d)

lemma tile_up (i : Pay d) (p : Sec G d) :
    tileK G (d + 1) i.castSucc (step d p) = step d (tileK G d i p) :=
  rfl

lemma ladder_tile (h : Ladder U P) : Ladder (printM U) (printM P) := by
  intro n x
  suffices he :
    ∀ i : Pay d,
      coeff n (printM U) (step d (tileK G d i x)) = step d (coeff n (printM P) (tileK G d i x))
    by
    rw [← whole x, map_sum, map_sum, map_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => he i
  intro i
  rw [printed, printed, tileskip, ← tile_up, tileskip, tile_up i, h]
  exact tile_up ..

lemma foldDrop (h : PureDrop P) (hv : PureDrop Q) (hp : CloseP P) (hq : CloseP Q) :
    PureDrop (P * Q) := by
  unfold PureDrop
  rw [print_prod hp hq, h, hv, one_mul]

lemma Strict (hp : CloseP P) : PureDrop (vault P * printM P) := by
  unfold PureDrop
  rw [print_prod hp.invert (printH hp), Mass.print, ← print_prod hp.invert hp, (antidote hp).2]
  exact print1

lemma dropV (hp : CloseP P) (h : PureDrop P) : PureDrop (vault P) := by
  have hx := print_prod hp hp.invert
  rw [h, one_mul, (antidote hp).1, print1] at hx
  exact hx.symm

lemma δ_charge (B : Guard G d) (h : Mass B) (v : Pay d) (p : Sec G d) (i : ℕ) :
    tileK G d v (coeff i B p) = coeff i B (tileK G d v p) := by
  nth_rw 1 2 [← h]
  rw [printed, tile_put, tileskip]
end grade
end YM.WilsonMS.GFlow
