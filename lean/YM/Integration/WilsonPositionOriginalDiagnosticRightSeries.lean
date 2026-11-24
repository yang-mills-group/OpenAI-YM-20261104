import YM.Integration.WilsonMatrixOriginalDeckPrescriptionReturn

/-! Truncate the filed two-clock field conversion at the same order as both
actual Q source programs. Its entire discrepancy has a fixed coefficient above that order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDiagnosticRightSeries
open Finset Matrix Polynomial MS MS.Land MS.Menus MS.Local.Physical
open WilsonMatrixOriginalDeckPrescription WilsonMatrixOriginalDeckPrescriptionSeries
open scoped Classical BigOperators Polynomial Matrix

def trunc (p:ℕ)(f:ℕ→ℂ) : ℂ[X] := ∑ n∈range (p+1),monomial n (f n)

theorem get {p n:ℕ}(h:n≤p)(f:ℕ→ℂ) : (trunc p f).coeff n=f n :=by
  simp [trunc,coeff_monomial,show n<p+1 by omega]

variable {G:Gauge} {D:Deck G} (Q:MS.Land.Prescription D) (h:ℕ)
local notation "I"=>Glyph D h

def sources (μ:ℝ)(p:ℕ) : Matrix I I ℂ[X] := fun i j=>trunc p fun k=>fees Q h μ k i j
def change (μ ν:ℝ)(p:ℕ) : Matrix I I ℂ[X] := fun i j=>trunc p fun k=>trial Q h μ ν k i j

def surplus (μ ν:ℝ)(p:ℕ) : Matrix I I ℂ[X] :=
  sources Q h μ p * change Q h μ ν p - sources Q h ν p

private theorem joined {p n:ℕ}(hn:n≤p)(f z:ℕ→ℂ) :
    ((trunc p f)*(trunc p z)).coeff n=∑ j:Fin (n+1),f (n-j.val)*z j.val:=by
  rw [mul_comm,coeff_mul,Nat.sum_antidiagonal_eq_sum_range_succ_mk,←Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro j _
  have jl:=j.isLt
  exact ((congrArg₂ (·*·) (get (show j.val≤p by omega) z) (get (show n-j.val≤p by omega) f))).trans (mul_comm _ _)

theorem flat (μ ν:ℝ)(p:ℕ)(i j:I):
    X^(p+1) ∣ surplus Q h μ ν p i j :=by
  rw [X_pow_dvd_iff]
  intro n hn
  have l:n≤p:=by omega
  have close:=congrFun (congrFun (WilsonMatrixOriginalDeckPrescriptionSeries.measured Q h μ ν n) i) j
  simp only [Matrix.sum_apply,Matrix.mul_apply] at close
  simp only [surplus,Matrix.sub_apply,Polynomial.coeff_sub,Matrix.mul_apply,
    finsetSum_coeff,sources,change,get l,joined l]
  rw [Finset.sum_comm,close,sub_self]

def tail (μ ν:ℝ)(p:ℕ)(i j:I):ℂ[X] := (flat Q h μ ν p i j).choose

theorem evaluated (μ ν:ℝ)(p:ℕ)(u:ℂ)(i j:I) :
    ∑ b:I,(sources Q h μ p i b).eval u*(change Q h μ ν p b j).eval u -
      (sources Q h ν p i j).eval u = u^(p+1)*(tail Q h μ ν p i j).eval u :=by
  have e:=congrArg (Polynomial.eval u) (flat Q h μ ν p i j).choose_spec
  simpa only [surplus,Matrix.sub_apply,Matrix.mul_apply,eval_sub,eval_finsetSum,
    eval_mul,eval_pow,eval_X,tail] using e

def mass (f:ℂ[X]):ℝ := ∑ k∈f.support,‖f.coeff k‖

theorem affordable (μ ν:ℝ)(p:ℕ){u:ℂ}(hu:‖u‖≤1)(i j:I) :
    ‖∑ b:I,(sources Q h μ p i b).eval u*(change Q h μ ν p b j).eval u -
      (sources Q h ν p i j).eval u‖ ≤ ‖u‖^(p+1)*mass (tail Q h μ ν p i j) :=by
  rw [evaluated,norm_mul,norm_pow]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  generalize tail Q h μ ν p i j=f
  rw [eval_eq_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun k _=>?_ )
  rw [norm_mul,norm_pow]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hu)

end YM.Integration.WilsonPositionOriginalDiagnosticRightSeries
