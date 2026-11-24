import YM.Integration.WilsonOriginalAlternativePurse
import YM.Integration.WilsonPrecontactSeparatedLamps

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeLamps
open Function Finset Lattice Wilson RG Ac Marker QuadraticLocal Push.Corrected Push.AbsoluteSums MeasureTheory
open WilsonOriginalAlternativeNames WilsonOriginalAlternativePurse
open scoped Classical BigOperators Topology
variable {V:Type} [DecidableEq V] [Fintype V] {R:Census V}
variable {G:Gauge} {n:Side} {T I:Type} {o:V→Site n} {p:BudgetPoint}
variable (E:Lamps T I G p o R)

def roster : Set ((board R).Mode × I) := {v|base R v.1=E.mode v.2 ∧ ∀j∈v.1.val,j.2≠1}

def issued : Lamps T (roster E) G p (o ∘ Prod.fst) (board R) where
  mode j:=j.val.1
  live j h:=E.live j.val.2 (j.property.1.symm.trans (congrArg (base R) h))
  address j:=E.address j.val.2
  roots j v hv:=E.roots j.val.2 v.1 (j.property.1 ▸ Finset.mem_image_of_mem Prod.fst hv)
  nominal t j:=E.nominal t j.val.2
  legal t j:=E.legal t j.val.2
  clear j:=E.clear j.val.2
  pure t j:=E.pure t j.val.2

theorem paid {w:V→ℝ} (wp:∀i,0<w i) {B:ℕ} {a k:ℝ}
    (fund:E.Paid w B a k) : (issued E).Paid (wallet R w) B a k := by
  obtain ⟨f,nonneg,smooth,hits⟩:=fund.budget
  refine ⟨fun j=>f j.val.2,fun j=>nonneg _,fun j=>smooth _,?_⟩
  have cp:0<copiesBound R:=lt_of_lt_of_le zero_lt_one (bound_one R)
  have one:SumBudget (fun _:(board R).Mode=>(copiesBound R)⁻¹) 1:=by
    apply budget_finite (fun _=>inv_nonneg.mpr cp.le)
    simp only [sum_const,card_univ,nsmul_eq_mul]
    change copiesBound R*(copiesBound R)⁻¹≤1
    rw [mul_inv_cancel₀ cp.ne']
  intro x
  have full:=budget_prod one (hits x)
  rw [one_mul] at full
  apply budget_mono (WilsonPrecontactSeparatedLamps.subbill full (roster E))
  · intro j
    split
    · exact mul_nonneg (mul_nonneg (Poly.worth (positive R wp) _).le (nonneg _)) (Real.exp_nonneg _)
    · exact le_rfl
  intro j
  change (if x ∈ E.ground j.val.2 then Poly.toll (wallet R w) j.val.1*f j.val.2*
    Real.exp (a*coverNumber B (E.ground j.val.2)) else 0) ≤
    (copiesBound R)⁻¹*(if x∈E.ground j.val.2 then Poly.toll w (E.mode j.val.2)*f j.val.2*
    Real.exp (a*coverNumber B (E.ground j.val.2)) else 0)
  split
  · have small:=row R wp j.val.1 (fun eq=>E.live j.val.2 (j.property.1.symm.trans eq))
    rw [j.property.1] at small
    rw [show (copiesBound R)⁻¹*(Poly.toll w (E.mode j.val.2)*f j.val.2*
        Real.exp (a*coverNumber B (E.ground j.val.2)))=
        (Poly.toll w (E.mode j.val.2)/copiesBound R)*f j.val.2*
        Real.exp (a*coverNumber B (E.ground j.val.2)) by ring]
    gcongr
    exact nonneg _
  · simp

theorem signal (j:roster E) (t:T) (U:Config G n) (s:(board R).Mode):
    ((issued E).frame j t U).part s=if s=j.val.1 then E.light t j.val.2 U else 0 :=
  Poly.part_send ..

end YM.Integration.WilsonOriginalAlternativeLamps
