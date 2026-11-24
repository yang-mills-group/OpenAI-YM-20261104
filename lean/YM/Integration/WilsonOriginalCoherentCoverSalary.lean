import YM.Integration.WilsonOriginalPaidWalkCover
import YM.Integration.WilsonOriginalCenteredSeamSalary

/-! A single original centered salary pays all coherent lifts at a fixed covered root. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCoherentCoverSalary
open Function Finset Lattice RG Wilson Marker Push Push.AbsoluteSums QuadraticLocal QuadraticLocal.Earn
open Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical TwoReset
open WilsonOriginalPaidWalkCover WilsonOriginalCenteredSeamSalary
open scoped BigOperators Classical
variable {G:Gauge} {n N:Side} {V ι α:Type} [DecidableEq V]
  {o:Passport n V} {J:Census V} (h:n.val∣N.val)

theorem fiber (center:Site n) (x:Site N) (a:ℝ) :
    (∑p:Fin (Pages n N),if (page h center p).val=x then a else 0)=
      if center=splitter h x then a else 0 := by
  calc
    _=∑y∈parcel (splitter h) center,if y=x then a else 0 :=
      TwoReset.pages h center (fun y=>if y=x then a else 0)
    _=_:=by simp [parcel,eq_comm]

variable (M:ι→Row o J G α) {w:V→ℝ} {grades:V→ℕ} {σ C:ℝ} {order seats shelf:ℕ}

def amount (w:V→ℝ) (σ:ℝ) (x:Site N) (t:α) (s:Finset V) (angular:Finset (Site N))
    (z:ι) (p:Fin (Pages n N)) : ℝ :=
  let A:=row h (M z) p
  if A.center=x ∧ s⊆A.mode.val ∧ angular⊆A.atom.footprint A.center then
    Poly.toll w A.mode * ‖A.paint t‖ * Real.exp (σ * radius x (targets (passport h (M z) p) s angular)) else 0

theorem original (stock:Scene.Armada M w grades σ C order seats shelf) (σ0:0≤σ)
    (x:Site N) (t:α) (s:Finset V) (angular:Finset (Site N)) :
    SumBudget (fun z:Σ _:ι,Fin (Pages n N)=>amount h M w σ x t s angular z.1 z.2) C := by
  let cost (z:ι):=Poly.toll w (M z).mode*(M z).height σ
  have toll (z:ι):0≤Poly.toll w (M z).mode:=Finset.prod_nonneg fun v _=>(stock.positive v).le
  have pos (z:ι):0≤cost z:=mul_nonneg (toll z) (mul_nonneg (M z).sound.le (Real.exp_pos _).le)
  have each (z:ι):SumBudget (amount h M w σ x t s angular z)
      (if (M z).center=splitter h x then cost z else 0):=by
    apply budget_finite
    · intro p
      unfold amount
      dsimp only
      split
      · exact mul_nonneg (mul_nonneg (toll z) (norm_nonneg _)) (Real.exp_pos _).le
      · exact le_rfl
    · rw [←fiber h (M z).center x (cost z)]
      apply Finset.sum_le_sum
      intro p _
      unfold amount
      dsimp only
      split_ifs with hit atRoot atRoot
      · have far:=geometry (row h (M z) p) s angular hit.2.1 hit.2.2
        rw [hit.1] at far
        have dist:=far.trans (WilsonOriginalPaidWalkCover.length h (M z) p)
        unfold cost Row.height
        rw [←mul_assoc]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (stock.honor z t) (toll z))
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr dist) σ0))
          (Real.exp_pos _).le (mul_nonneg (toll z) (M z).sound.le)
      · exact (atRoot ((centered h (M z) p).symm.trans hit.1)).elim
      · exact pos z
      · exact le_rfl
  exact Push.Local.sumBudget_sigma each (stock.suggests (splitter h x))

end YM.Integration.WilsonOriginalCoherentCoverSalary
