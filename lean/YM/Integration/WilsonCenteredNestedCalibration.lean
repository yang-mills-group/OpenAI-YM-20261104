import YM.Integration.WilsonCenteredNestedProgram
import YM.Integration.WilsonCenteredNestedRates

/-! On an arbitrarily deep but finite genuine deposited tree, evaluate every
local signed comparison before contracting. A child-to-parent scale ratio
appears to the actual nonnegative grade of that child. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedCalibration
open OPE OPE.Orbits OPE.Orbits.Reader OPE.Nesting OPE.Nesting.Tree OPE.Nesting.Composite OPE.Nesting.Atom
open Extraction Spec Table WilsonCenteredNestedProgram WilsonCenteredNestedProducts WilsonCenteredNestedRates
open scoped Classical BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

theorem original (A : Rule F Q) (g L E : ℝ → ℝ) (Ln : ∀ r,0 ≤ L r) (En : ∀ r,0 ≤ E r)
    (t : Tree) (s : t.Inner → ℝ) (z : t.Plot) (v : t.Leaf → S.Tag) (D : t.Inner → ℕ)
    (H : ℕ) (k : Stage F Q H t) (parent : ℝ) (pp : 0 < parent) (taper : t.Tapered parent 1 s)
    (row : calibrated F Q A g L E t s z v D H) :
    Priced (run F Q (measured F Q) g t s z v D H k) (run F Q A g t s z v D H k)
      ((premium F Q t D s L * parent^((token F Q t v k).1)) * leaves t s (degrees v) parent)
      (∑ i:t.Inner,E (s i)) := by
  induction t generalizing parent H with
  | bud =>
    change Priced 1 1 ((1 * parent^((v ()).1)) * (parent^((v ()).1))⁻¹) (∑ i:Empty,E (s i))
    rw [one_mul,mul_inv_cancel₀ (pow_ne_zero _ pp.ne'),Fintype.sum_empty]
    exact ⟨by simp,by simp,by simp⟩
  | fork n p ih =>
    let r := s (.inl ())
    have rp : 0 < r := taper.1
    let child (j : Branches F Q (f:=p) (rollCaps D)) (i : Fin n) :=
      (echoTags F Q v j i).1
    let sub (i : Fin n) := premium F Q (p i) (childAge i D) (childAge i s) L
    let leaf (i : Fin n) := leaves (p i) (childAge i s) (childWages i (degrees v)) r
    let δ (i : Fin n) := ∑ a:(p i).Inner,E (childAge i s a)
    let m := k.1.val
    let sel := Branches F Q (f:=p) (rollCaps D)
    let x (j : sel) (i : Fin n) := run F Q (measured F Q) g (p i) (childAge i s)
      (childPlace i z) (childWages i v) (childAge i D) (rollCaps D i) (j i)
    let y (j : sel) (i : Fin n) := run F Q A g (p i) (childAge i s)
      (childPlace i z) (childWages i v) (childAge i D) (rollCaps D i) (j i)
    let x₀ (j : sel) := express Q m k.2 (skyline z) (echoTags F Q v j) (anchor z)
    let y₀ (j : sel) := A n m k.2 r (g r) (skyline z) (echoTags F Q v j) (anchor z)
    have childPaid (j : sel) (i : Fin n) :
        Priced (x j i) (y j i) ((sub i*r^(child j i))*leaf i) (δ i) :=
      ih i _ _ _ _ _ _ r rp (by simpa only [mul_one] using taper.2.2 i) (row.2 i)
    have rootPaid (j : sel) :
        Priced (x₀ j) (y₀ j) (L r*(r^m/∏ i,r^(child j i))) (E r) :=
      row.1 j m (Nat.le_of_lt_succ k.1.isLt) k.2
    have term (j : sel) : Priced ((∏ i,x j i)*x₀ j) ((∏ i,y j i)*y₀ j)
        ((((∏ i,sub i)*L r)*r^m)*∏ i,leaf i) ((∑ i,δ i)+E r) := by
      have h := (Priced.product Finset.univ (x j) (y j) _ δ (fun i _=>childPaid j i)).mul (rootPaid j)
      rw [cancel r rp] at h
      exact h
    have sum := Priced.terms (fun j : sel=>(∏ i,x j i)*x₀ j) (fun j : sel=>(∏ i,y j i)*y₀ j) _ _ term
    have eqfee : ((Fintype.card sel:ℝ)*((((∏ i,sub i)*L r)*r^m)*∏ i,leaf i)) =
        ((premium F Q (fork n p) D s L*r^m)*∏ i,leaf i) := by
      change _ = (((Fintype.card sel:ℝ)*((∏ i,sub i)*L r))*r^m)*(∏ i,leaf i)
      ring
    rw [eqfee] at sum
    have eqchange : (∑ i,δ i)+E r = ∑ i:(fork n p).Inner,E (s i) := by
      rw [Tree.sum_inner,add_comm]
    rw [eqchange] at sum
    have inc : ((premium F Q (fork n p) D s L*r^m)*∏ i,leaf i) ≤
        ((premium F Q (fork n p) D s L*parent^m)*∏ i,leaf i) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ rp.le taper.2.1 m) (premium_nonnegative F Q _ _ _ L Ln))
        (leaves_nonnegative (fork n p) s (degrees v) pp taper)
    exact sum.expand inc (Finset.sum_nonneg (fun i _=>En _))

end YM.Integration.WilsonCenteredNestedCalibration
