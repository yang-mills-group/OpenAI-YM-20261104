import YM.Integration.WilsonRetainedReturnPrice
import YM.Integration.WholeCaptureTransport

/-! The actual whole-product budget controls the *difference of two
canonical projected labels*, with no price in the stock at the moving
capture scale. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedRetainedProjection
open Function Filter Real Lattice RG Wilson Labels Source PhysicalNext.Repeat.Legato
open Trace.Physical Trace.Physical.GermGraph Work.G08 RG16 RG16.Literal
open Extra.Histories Bid
open scoped Classical Topology BigOperators
variable {G : Gauge} (R : Run G) (d : ℕ)

theorem measured {N p t b i : ℕ} (ot : Opened R.family d t p) (tb : t ≤ b) (bN : b < N)
    (ti : t ≤ i) (ib : i ≤ b) (oi : Opened R.family d i p) (Y : Cut R.family N p) (B : R.family.label d) (a : ℝ)
    (purchase : WholeProductCapture.Retained R.family N b p d t R.makes ot tb bN Y B a) :
    gainChart R.family.path b i * mCost R.family d N p i
      (topReport R.family N p d R.makes i oi (ib.trans bN.le) Y - (R.family.factory d N p).terminal.symm B) ≤ a := by
  obtain ⟨P,g,_,_,path,_⟩ := purchase
  obtain ⟨paid,held,_,cash⟩ := path i ti ib
  let z := (R.family.factory d N p).terminal.symm B
  have germ := (WholeCaptureTransport.read_signed R.family N p d R.makes oi (ib.trans bN.le) z paid held).2.1
  have wrap := measured_diff d N p i R.makes oi.post (ib.trans bN.le) paid
  have small : invoice (C:=R.family) d i p ≤ 1 := (smaller d p oi).trans (by norm_num)
  have w := wrap.trans (mul_le_of_le_one_left (rem_nonneg paid.2) small)
  let q := P i
  let c := page (C:=R.family) d p i q
  have recompose : c = q.x+(c-q.x) := by abel
  have bank := Size.add (R.family.labels.level d) q.x (c-q.x)
  have joining : (R.family.labels.level d).coeffSize q.x + (R.family.labels.level d).coeffSize (c-q.x) ≤
      (R.family.labels.level d).coeffSize q.x + g i := add_le_add le_rfl w
  have cost : (R.family.labels.level d).coeffSize c ≤ g i+(R.family.labels.level d).coeffSize q.x :=
    (congrArg (R.family.labels.level d).coeffSize recompose).le.trans
      (bank.trans (joining.trans (add_comm _ _).le))
  have same : mCost R.family d N p i (topReport R.family N p d R.makes i oi (ib.trans bN.le) Y-z) =
      (R.family.labels.level d).coeffSize c := congrArg (R.family.labels.level d).coeffSize germ
  exact (mul_le_mul_of_nonneg_left (same.le.trans cost) (exp_pos _).le).trans cash

theorem returned (hG : G.Simple) :
    ∃ U : ℕ, ∃ M : ℝ, 1 ≤ M ∧ (∀ t ≥ U, ∀ p, Opened R.family d t p) ∧
      ∀ t ≥ U, ∀ N p b (ot : Opened R.family d t p) (tb : t ≤ b) (bN : b < N)
        (Y : Cut R.family N p) (B : R.family.label d) (a : ℝ),
      WholeProductCapture.Retained R.family N b p d t R.makes ot tb bN Y B a →
      ∀ i ≥ t, ∀ ib : i ≤ b, ∀ oi : Opened R.family d i p,
        gainChart R.family.path b i * mCost R.family d N p i
          (topReport R.family N p d R.makes i oi (ib.trans bN.le) Y -
           topReport R.family N p d R.makes t ot (tb.trans bN.le) Y) ≤
          (1+M*invoice (C:=R.family) d t p)*a := by
  obtain ⟨U,early,all⟩ := WilsonRetainedReturnPrice.prices R d hG
  obtain ⟨M,M1,raise⟩ := all (1/8) (by norm_num)
  refine ⟨U,M,M1,early,?_⟩
  intro t Ut N p b ot tb bN Y B a held i ti ib oi
  let α := topReport R.family N p d R.makes i oi (ib.trans bN.le) Y
  let β := topReport R.family N p d R.makes t ot (tb.trans bN.le) Y
  let z := (R.family.factory d N p).terminal.symm B
  let gain := gainChart R.family.path b i
  let bill := invoice (C:=R.family) d t p
  let mat : R.family.label d ≃ₗ[ℂ] R.family.label d := fitting (C:=R.family) d N p i R.makes oi (ib.trans bN.le)
  have tag : α-β = (α-z)-(β-z) := by abel
  have tri : mCost R.family d N p i (α-β) ≤ mCost R.family d N p i (α-z)+mCost R.family d N p i (β-z) :=
    (congrArg (R.family.labels.level d).coeffSize ((congrArg mat tag).trans (mat.map_sub _ _))).le.trans
      (count_sub (C:=R.family) (d:=d) (mat (α-z)) (mat (β-z)))
  have near := measured R d ot tb bN ti ib oi Y B a held
  have back := raise t Ut b N p ot tb bN Y B a held i ti (ib.trans bN.le)
  have inverse : exp ((1/8:ℝ)*(R.family.S.scale i-R.family.S.scale t) -
      (1/8:ℝ)*(R.family.S.scale b-R.family.S.scale t)) = gain⁻¹ := by
    change _ = (exp ((1/8:ℝ)*(R.family.S.scale b-R.family.S.scale i)))⁻¹
    rw [←Real.exp_neg]
    congr 1
    ring
  rw [inverse] at back
  have gpos : 0 < gain := exp_pos _
  have forced : gain*mCost R.family d N p i (β-z) ≤ M*(bill*a) := calc
    _ ≤ gain*(M*(bill*a)*gain⁻¹) := mul_le_mul_of_nonneg_left back gpos.le
    _ = _ := by rw [mul_left_comm,mul_inv_cancel₀ gpos.ne',mul_one]
  calc
    _ ≤ gain*(mCost R.family d N p i (α-z)+mCost R.family d N p i (β-z)) := mul_le_mul_of_nonneg_left tri gpos.le
    _ = gain*mCost R.family d N p i (α-z) + gain*mCost R.family d N p i (β-z) := mul_add _ _ _
    _ ≤ a+M*(bill*a) := add_le_add near forced
    _ = _ := by change a+M*(bill*a) = (1+M*bill)*a; ring

end YM.Integration.WilsonCapturedRetainedProjection
end
