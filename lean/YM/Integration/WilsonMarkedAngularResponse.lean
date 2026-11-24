import YM.Integration.WilsonMarkedScalarResponse

/-! The complete signed change of each native marked homogeneous weight
from an arbitrary primitive kinetic discrepancy. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMarkedAngularResponse
open PowerSeries FormalBulk08 Wine Comparison.RG02 Adjacent
open WilsonMarkedKineticDefect WilsonMarkedKineticGerm
open WilsonMarkedScalarResponse WilsonMarkedScalarEquation
open scoped Classical

private theorem factored (A B : PowerSeries ℂ) (s : ℕ) :
    (A-B)*difference A B s = A^s-B^s := by
  induction s with
  | zero => simp [difference]
  | succ s ih =>
    rw [difference,pow_succ,pow_succ]
    calc
      _ = (A-B)*A^s+B*((A-B)*difference A B s) := by ring
      _ = _ := by rw [ih]; ring

/-- Exact response on arbitrary field rank without equality of the two
primitive measured vacuum inputs. The displayed right hand side contains
every original reciprocal field factor and the signed primitive discrepancy. -/
theorem weight (c : Caliber) (cap : ℕ) (H : Pence) (hH : Wine.Fresh H)
    {j e : ℕ} (hj : j ≤ e) (he : e ≤ cap) (r : ℕ) :
    let a := fun k => (c.measure k : ℂ)
    let b := fun k => ((coeff k H : ℝ) : ℂ)
    let A := rate (c.back cap)
    let U := reciprocal (c.back cap)
    let B := PowerSeries.map Complex.ofRealHom (Wine.bookH H)
    let V := PowerSeries.map Complex.ofRealHom (Wine.bookU H)
    physicalWeight c cap e j r - formalWeight H e j r =
       coeff (e-j) ((table cap (fun k => a k-b k) A * resolver cap b A B) *
       (difference A B j * U^r - B^j * (U*V) * difference U V r)) := by
  intro a b A U B V
  have au : A*U=1 := unit (c.back cap)
  have bv : B*V=1 := by dsimp [B,V]; rw [←map_mul,Wine.book_equal,map_one]
  have inv : U-V = -(A-B)*(U*V) := by
    calc
      _ = U*(B*V)-V*(A*U) := by rw [bv,au,mul_one,mul_one]
      _ = _ := by ring
  let m := difference A B j * U^r - B^j*(U*V)*difference U V r
  have form : A^j*U^r - B^j*V^r = (A-B)*m := by
    calc
      _ = (A^j-B^j)*U^r+B^j*(U^r-V^r) := by ring
      _ = (A-B)*difference A B j*U^r + B^j*((U-V)*difference U V r) := by rw [factored,factored]
      _ = _ := by rw [inv]; unfold m; ring
  have b₀ : formalWeight H e j r = coeff (e-j) (B^j*V^r) := by
    rw [formalWeight,if_pos hj]
    dsimp [B,V,Wine.bill]
    rw [←map_pow,←map_pow,←map_mul,coeff_map]
    rfl
  have h := (WilsonMarkedScalarResponse.signed c cap H hH).mul (Series.Through.exact_eq m cap)
  rw [analytic c cap e j r hj,b₀,←map_sub]
  change coeff (e-j) (A^j*U^r-B^j*V^r) = _
  rw [form]
  exact h (e-j) (by omega)

end YM.Integration.WilsonMarkedAngularResponse
