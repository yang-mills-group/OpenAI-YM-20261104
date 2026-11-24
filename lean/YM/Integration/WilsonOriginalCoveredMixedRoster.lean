import YM.Integration.WilsonOriginalSuspendedTensor

/-! One authentic centerwise income for every original relative owner and ordered thermal/angular slot. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCoveredMixedRoster
open Function Finset Lattice RG Wilson Marker Push Push.AbsoluteSums QuadraticLocal QuadraticLocal.Earn Stationary
open Further.PhysicalPeriodLimitF933 Macrame FVA1Physical FVA1Physical.TwoReset
open WilsonOriginalPaidWalkCover WilsonOriginalPointCompactRoster WilsonOriginalCenteredSeamSalary
open WilsonOriginalSuspendedTensor
open scoped Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {n N:Side} {V X ι:Type} [DecidableEq V] {o:Passport n V} {J:Census V}
  (h:n.val∣N.val) (M:ι→Row o J G X) {w:V→ℝ} {grades:V→ℕ} {σ C:ℝ} {order seats shelf:ℕ}

abbrev Item (ι:Type) (n N:Side) (G:Gauge) (r:ℕ):=Σ (_:Σ _:ι,Fin (Pages n N)),Positions G N r

def wage (w:V→ℝ) (x:Site N) (s:Finset V) (t:X) (j r:ℕ) (σ:ℝ) (i:Item ι n N G r):ℝ :=
  let A:=row h (M i.1.1) i.1.2
  if A.center=x ∧ s⊆A.mode.val then Poly.toll w A.mode*paid A s t j r i.2 (σ/2) else 0

theorem original (stock:Scene.Armada M w grades σ C order seats shelf) (hs:0<σ)
    (x:Site N) (s:Finset V) (t:X) (j r:ℕ) :
    SumBudget (wage h M w x s t j r σ) (fee G σ r*C) := by
  let k:=fee G σ r
  have k0:0≤k:=nonnegative G hs r
  let cost (z:ι):=Poly.toll w (M z).mode*(M z).height σ
  have toll (z:ι):0≤Poly.toll w (M z).mode:=Finset.prod_nonneg fun v _=>(stock.positive v).le
  have pos (z:ι):0≤cost z:=mul_nonneg (toll z) (mul_nonneg (M z).sound.le (Real.exp_pos _).le)
  let P:Type:=Σ _:ι,Fin (Pages n N)
  let note (u:P):=if (row h (M u.1) u.2).center=x then k*cost u.1 else 0
  have outer:SumBudget note (k*C):=by
    have each (z:ι):SumBudget (fun p:Fin (Pages n N)=>note ⟨z,p⟩)
        (k*(if (M z).center=splitter h x then cost z else 0)):=by
      apply budget_finite
      · intro p;unfold note;split
        · exact mul_nonneg k0 (pos z)
        · exact le_rfl
      · unfold note
        simp only [centered,anchor]
        rw [WilsonOriginalCoherentCoverSalary.fiber]
        split <;> simp
    exact Push.Local.sumBudget_sigma each (budget_scale k0 (stock.suggests (splitter h x)))
  apply Push.Local.sumBudget_sigma (a:=note) _ outer
  rintro ⟨z,p⟩
  let A:=row h (M z) p
  have mode: A.mode=(M z).mode:=rfl
  by_cases hit:A.center=x ∧ s⊆A.mode.val
  · have draw:=WilsonOriginalSuspendedTensor.original A s hit.2 t hs
      (stock.honor z) (stock.purchases.spend z) j r
    have height:A.height σ≤(M z).height σ:=by
      unfold Row.height
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (WilsonOriginalPaidWalkCover.length h (M z) p)) hs.le)) (M z).sound.le
    apply budget_finite
    · intro a
      change 0≤ if A.center=x ∧ s⊆A.mode.val then Poly.toll w A.mode*paid A s t j r a (σ/2) else 0
      simp only [if_pos hit]
      exact mul_nonneg (toll z) (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
    · change (∑ a:Positions G N r,if A.center=x ∧ s⊆A.mode.val then Poly.toll w A.mode*paid A s t j r a (σ/2) else 0)≤
        if A.center=x then k*cost z else 0
      simp only [if_pos hit,if_pos hit.1,←Finset.mul_sum]
      exact (mul_le_mul_of_nonneg_left (draw.trans (mul_le_mul_of_nonneg_left height k0)) (toll z)).trans_eq (by unfold cost k;ring)
  · apply budget_finite
    · intro a;change 0≤ if A.center=x ∧ s⊆A.mode.val then _ else 0;rw [if_neg hit]
    · change (∑ a:Positions G N r,if A.center=x ∧ s⊆A.mode.val then _ else 0)≤ if A.center=x then k*cost z else 0
      simp only [if_neg hit,sum_const_zero]
      split
      · exact mul_nonneg k0 (pos z)
      · exact le_rfl

theorem named (stock:Scene.Armada M w grades σ C order seats shelf) (hs:0<σ)
    (x:Site N) (s:Finset V) (t:X) (j r:ℕ) :
    SumBudget (fun z:Σ (_:Item ι n N G r),(s→Fin (Pages n N))=>
      if WilsonOriginalNamedRelativeRows.assigned h M s z.1.1.1 z.1.1.2=z.2 then
        wage h M w x s t j r σ z.1 else 0) (fee G σ r*C):=by
  have all:=original h M stock hs x s t j r
  apply Push.Local.sumBudget_sigma (a:=wage h M w x s t j r σ) _ all
  intro z
  apply budget_finite
  · intro u;split
    · exact all.1 z
    · exact le_rfl
  · simp

end YM.Integration.WilsonOriginalCoveredMixedRoster
