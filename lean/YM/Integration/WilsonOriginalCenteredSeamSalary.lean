import YM.Integration.WilsonOriginalPointCompactSalary

/-! Rooted income of an actually funded marked row on its original passport. -/
set_option autoImplicit false
set_option warningAsError true

noncomputable section
namespace YM.Integration.WilsonOriginalCenteredSeamSalary
open Function Finset Lattice Laurent RG Wilson Marker Gauge
open Push Push.AbsoluteSums Paths Animals QuadraticLocal QuadraticLocal.Poetry QuadraticLocal.Earn
open scoped BigOperators Classical

variable {G:Gauge} {n:Side} {V ι α:Type} [DecidableEq V] {J:Census V}
  {o:Passport n V} {w:V→ℝ} {grades:V→ℕ} {σ C:ℝ} {order seats shelf:ℕ}

def targets (o:Passport n V) (s:Finset V) (angular:Finset (Site n)) : Finset (Site n) :=
  angular ∪ s.biUnion o.support

def radius (root:Site n) (points:Finset (Site n)) := points.sup (separation root)

theorem geometry (A:Row o J G α) (s:Finset V) (angular:Finset (Site n))
    (named:s⊆A.mode.val) (placed:angular ⊆ A.atom.footprint A.center) :
    radius A.center (targets o s angular) ≤ A.length := by
  apply Finset.sup_le
  intro u occurs
  apply A.binder.spread A.atom
  rcases Finset.mem_union.mp occurs with h|h
  · exact A.binder.footprint A.atom (placed h)
  · obtain ⟨v,hv,located⟩:=Finset.mem_biUnion.mp h
    exact A.binder.covers A.atom v (named hv) located

theorem income (M:ι→Row o J G α) (stock:Scene.Armada M w grades σ C order seats shelf)
    (σ0:0≤σ) (root:Site n) (t:α) (s:Finset V) (angular:Finset (Site n)) :
    SumBudget (fun z=>if (M z).center=root ∧ s⊆(M z).mode.val ∧ angular⊆(M z).atom.footprint (M z).center then
      Poly.toll w (M z).mode * ‖(M z).paint t‖ * Real.exp (σ * radius root (targets o s angular)) else 0) C := by
  apply Push.Local.sumBudget_mono (stock.suggests root)
  · intro z
    have pay:0≤Poly.toll w (M z).mode:=Finset.prod_nonneg fun v _=>(stock.positive v).le
    split_ifs <;> positivity
  · intro z
    have pay:0≤Poly.toll w (M z).mode:=Finset.prod_nonneg fun v _=>(stock.positive v).le
    dsimp only
    by_cases center:(M z).center=root
    · rw [if_pos center]
      split_ifs with h
      · have far:radius root (targets o s angular) ≤ (M z).length:=
          center ▸ geometry (M z) s angular h.2.1 h.2.2
        rw [Row.height,←mul_assoc]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (stock.honor z t) pay)
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr far) σ0))
          (Real.exp_pos _).le (mul_nonneg pay (M z).sound.le)
      · exact mul_nonneg pay (mul_nonneg (M z).sound.le (Real.exp_pos _).le)
    · simp [center]
  · exact le_rfl

end YM.Integration.WilsonOriginalCenteredSeamSalary
