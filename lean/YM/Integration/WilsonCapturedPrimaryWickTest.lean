import YM.Integration.WilsonCapturedPrimaryWickFiled

/-! The full ordinary finite forecast on each of the intrinsic field
detector's clipped Wilson rays. Its degree is fixed by the original mark
grades and the two requested horizons. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWickTest
open Finset Labels Lattice Wilson RG Tree Marker Precision Exterior
open Source Push.Local Next.Foundations Planned.AtomRegular ConnectedActivityE6.SliceRows
open Stationary Comparison.RG02 Comparison.RG02.Order
open WilsonCapturedPrimaryAngles WilsonCapturedPrimaryPotential
open scoped Classical BigOperators
variable {G : Gauge} {V : Type} [Fintype V] [DecidableEq V] {I : Census V}
  {c f : Side} {P : Clip} {X : PathData G} {O : ChartRatio G} {S : StepData c f}
  (K : Bulk.Kernel S P X O) (F : Forest S.ratio) (tag : S.Choices) (W : Bulk.Colors I G f)

def fieldDegree (r : ℕ) (grades : V → ℕ) := r+2+∑ v, grades v

def directions (A : Hol G) (b : BudgetPoint) (o : Site c) (l : ℕ) {d : ℕ} (p : Probe G d)
    (g : ℝ) (j : Fin (d+1)) :=
  Stationary.arm G c 1 (potential g (limitAmp (WilsonCapturedPrimaryRough.quadratic b) o
    (active o l) (coeff A b o l p j.val)))

theorem angle (A : Hol G) (b : BudgetPoint) (o : Site c) (l : ℕ) {d : ℕ} (p : Probe G d) (g t : ℝ) :
    ∑ j : Fin (d+1), t^j.val • directions A b o l p g j = Stationary.arm G c 1 (lifted A b o l p g t) := by
  rw [WilsonCapturedPrimaryPotential.polynomial,map_sum]
  simp only [map_smul, directions]
  exact Fin.sum_univ_eq_sum_range (fun j : ℕ => t^j • Stationary.arm G c 1
    (potential g (limitAmp (WilsonCapturedPrimaryRough.quadratic b) o (active o l) (coeff A b o l p j)))) (d+1)

theorem original (A : Hol G) (b : BudgetPoint) (o : Site c) (l : ℕ) {d : ℕ} (p : Probe G d)
    (g : ℝ) (r : ℕ) (grades : V → ℕ)
    (hpow : ∀ a, W.power a ≤ (∑ j∈a.sites, grades j)+1)
    (a b' c' : V) (s : I.Mode) (diff : a≠b') (ab : s.val={a,b'}) :
    let D := fieldDegree r grades
    let y := WilsonCapturedPrimaryWickFiled.signed K F tag W r D d (directions A b o l p g) (g:ℂ) a b' c' s
    y.natDegree ≤ 2*(D*d) ∧ ∀ t : ℝ,
      let W' := Bulk.Fk K F tag W (Stationary.arm G c 1 (lifted A b o l p g t)) r
      let Z := Order.value (g:ℂ) (Order.ratio W')
      y.eval (t:ℂ) = Z.part s-Z.part (I.fire c') := by
  intro D y
  refine ⟨WilsonCapturedPrimaryWickFiled.degree ..,?_⟩
  intro t
  let price := fun j => (grades j:ℤ)
  have ticket (x : I.Mode) : Valence.Toile W.power x price := by
    intro a _
    have b' := hpow a
    change (W.power a:ℤ) ≤ 2+∑ j∈a.sites, (grades j:ℤ)
    exact_mod_cast (show W.power a ≤ 2+∑ j∈a.sites,grades j from by omega)
  have room (x : I.Mode) : (r:ℤ)+2+∑ j∈x.val,price j ≤ D := by
    have sub : ∑ j∈x.val, grades j ≤ ∑ j,grades j := sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intros;omega)
    change (r:ℤ)+2+∑ j∈x.val,(grades j:ℤ) ≤ (fieldDegree r grades:ℤ)
    unfold fieldDegree
    exact_mod_cast (show r+2+∑ j∈x.val,grades j ≤ r+2+∑ j,grades j from by omega)
  apply Eq.trans (WilsonCapturedPrimaryWickFiled.evaluated K F tag W r D d (directions A b o l p g)
    price (g:ℂ) a b' c' s diff ab (fun x _ => ticket x) (fun x _ => room x) t)
  rw [angle]

end YM.Integration.WilsonCapturedPrimaryWickTest
