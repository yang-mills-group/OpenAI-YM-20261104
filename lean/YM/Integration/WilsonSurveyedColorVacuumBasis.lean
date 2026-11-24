import YM.Integration.WilsonSurveyedColorAppointed

/-! The constant named color chart on the full cumulative complex space of
fields. The real color coefficients pass through each input of a genuine
complex multilinear test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorVacuumBasis
open Function Finset PowerSeries Maxwell Maxwell.Free XSpace XSpace.Normalize
open FVA2 FVA2.Dframe FVA2.Scale FVA2.O FVA2.O.Score FVA2.O.Project FVA2.O.Read
open FVA2.Position.OpenAxis MS MS.Land MS.Menus MS.Theater MS.Book.Program
open WilsonSurveyedColorNormalizers WilsonSurveyedColorOpenIndex
open WilsonSurveyedColorNamedBasis WilsonSurveyedColorAppointed
open scoped Classical BigOperators Matrix
variable {G : Gauge} (U : G.Color ≃ₗᵢ[ℝ] G.Color) (N : Normalizes U)
variable {d n : ℕ}

def axis (d : ℕ) : FieldEnd G d :=
  (Daylight (Press.portDeck G) d).constr ℂ fun w =>
    ∑ j : Grade G w.size, (casting U N w.size (flash w).item j : ℂ) • cap (own j) (size_le w)

theorem label (i : Q G) (hi : heft i ≤ d) :
    axis U N d (cap i hi) =
      ∑ j : Grade G i.h, (casting U N i.h i.item j : ℂ) • cap (own j) hi := by
  rw [axis,cap,←theory_sig,Module.Basis.constr_basis]
  rfl

def weight (p : Scan G n) (v : LivesP p) : ℂ :=
  ∏ i, (casting U N (p i).h (p i).item (v i) : ℂ)

theorem bill (p : Scan G n) (v : LivesP p) :
    play (chart U N) p (decode p v) = PowerSeries.C (weight U N p v) := by
  simp only [play,decode,report,weight,map_prod]
  rfl

theorem coefficient (p : Scan G n) (F : Scan G n → Cn) (k : ℕ) :
    coeff k (concert (chart U N) p F) =
      ∑ v : LivesP p, weight U N p v * coeff k (F (decode p v)) := by
  simp only [concert,map_sum,bill,coeff_C_mul]

theorem expand (P : Structure1.Point G d n) (p : Scan G n) (h : Guarded p d) :
    P (fun i => axis U N d (tape p h i)) =
      ∑ v : LivesP p, weight U N p v * P (tape (decode p v) (readyP h v)) := by
  simp_rw [tape,label]
  rw [MultilinearMap.map_sum P (fun i (j : Grade G (p i).h) => _)]
  apply sum_congr rfl
  intro v _
  exact P.map_smul_univ (fun i => _) (tape (decode p v) (readyP h v))

end YM.Integration.WilsonSurveyedColorVacuumBasis
end
