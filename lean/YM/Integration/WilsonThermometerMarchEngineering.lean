import YM.Integration.WilsonThermometerMarchEnrollment

/-! The exact refund at physical scale r on the genuine occupied face.
The three engineering exponents total fourteen. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerMarchEngineering
open Finset Lattice Wilson RG Source Table Spec Marker
open RG05Readout Native Address RG17 Trace.Pilot Climb
open PhysicalNext.Repeat.Legato WilsonPositionThermometerCapStation
open WilsonPositionThermometerGradedReading WilsonPositionThermometerGradedSource
open WilsonThermometerMarchSource
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) (A : Group R.family 6) {m N p : ℕ}
local notation "d" => (fun i : Fin 3 => (grade i).val)

def degree (s : (Stock.census (Fin 3)).Mode) := ∑ i ∈ s.val,d i

theorem degree_le (s : (Stock.census (Fin 3)).Mode) : degree s ≤ 14 := by
  have h : degree s ≤ ∑ i:Fin 3,d i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s.val) (fun _ _ _ => Nat.zero_le _)
  have total : (∑ i:Fin 3,d i) = 14 := by decide
  rwa [total] at h

def bill (r : (i : Fin 3) → Emblems R.family (d i)) (hm : m ≤ N) (u : ℝ)
    (s : (Stock.census (Fin 3)).Mode) : ℝ :=
  ∏ i∈s.val,(u/R.family.S.a m)^(d i)*charge (coordinate R A (p:=p) r hm i)

theorem refund (r : (i : Fin 3) → Emblems R.family (d i)) (hm : m ≤ N) (u : ℝ)
    (s : (Stock.census (Fin 3)).Mode) :
    (bill R A (p:=p) r hm u s:ℂ) * (∏i∈s.val, weight R A (p:=p) r hm i) = (u:ℂ)^degree s := by
  have one (i : Fin 3) :
      ((u / R.family.S.a m)^(d i) * charge (coordinate R A (p:=p) r hm i) : ℝ) *
        weight R A (p:=p) r hm i = (u:ℂ)^(d i) := by
    have ha : (R.family.S.a m:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (R.family.S.a_pos m).ne'
    have hc : (charge (coordinate R A (p:=p) r hm i):ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (charged _).ne'
    push_cast
    unfold WilsonThermometerMarchSource.weight
    rw [div_pow]
    field_simp [ha,hc]
  unfold bill degree
  push_cast
  rw [←Finset.prod_mul_distrib,←Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro i _
  simpa only [Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_div] using one i

theorem price (r : (i : Fin 3) → Emblems R.family (d i)) (hm : m ≤ N) (u : ℝ) (hu : 0 ≤ u)
    (M : ℝ) (huge : 1 ≤ M) (ready : ∀ i : Fin 3, size (coordinate R A (p:=p) r hm i) ≤ M)
    (s : (Stock.census (Fin 3)).Mode) :
    bill R A (p:=p) r hm u s ≤ (max 1 (u/R.family.S.a m))^14*M^3 := by
  let v := max 1 (u/R.family.S.a m)
  have vpos : 1 ≤ v := le_max_left .. 
  have upos := div_nonneg hu (R.family.S.a_pos m).le
  have hq : ∏i∈s.val,(u/R.family.S.a m)^(d i) ≤ v^14 := by
    calc _ ≤ ∏i∈s.val,v^(d i) := Finset.prod_le_prod (fun _ _ => pow_nonneg upos _)
          (fun _ _=>pow_le_pow_left₀ upos (le_max_right ..) _)
      _ = v ^ degree s := Finset.prod_pow_eq_pow_sum ..
      _ ≤ _ := pow_le_pow_right₀ vpos (degree_le s)
  have hp : ∏i∈s.val,charge (coordinate R A (p:=p) r hm i) ≤ M^3 := by
    calc _ ≤ ∏ _i∈s.val,M := Finset.prod_le_prod (fun i _=>(charged _).le) (fun i _ => max_le huge (ready i))
      _ = M^s.val.card := by simp
      _ ≤ _ := pow_le_pow_right₀ huge (by simpa using Finset.card_le_univ s.val)
  unfold bill
  rw [Finset.prod_mul_distrib]
  exact mul_le_mul hq hp (Finset.prod_nonneg fun i _=>(charged _).le) (by positivity : 0 ≤ v^14)

end YM.Integration.WilsonThermometerMarchEngineering
