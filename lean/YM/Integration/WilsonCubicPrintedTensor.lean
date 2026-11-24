import YM.Integration.WilsonHeldCubicOriginalRun
import YM.WilsonCoeffUV.Reclosure.Paths.RetainBase

/-! Recover the full unmasked original cubic Wilson source from its own
independently published Laurent rows on the same finite torus. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonCubicPrintedTensor
open WilsonCoeffUV
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Blue FreeResolvent Work.F08 Precision
open Gauge WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic Power Near Stationary PowerSeries
open Work.G05
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge} {c : Side} {s a : ℝ}

def source (A : ℕ → Atom G 3) : PrismA G := ⟨1,1,le_rfl,A⟩

/-- At angular rank k the cubic row is read at the actual coupling lag k−2.
The missing ranks zero through two vanish in the true cubic action. -/
theorem rank (A : ℕ → Atom G 3) (hs : 0<s) (money : SumBudget (fun i => (A i).budget s) a) (k : ℕ) :
    surf (source A) c (k-2) k = rye (turnSeries A (m:=c)) k := by
  by_cases small : k<3
  · have low : ¬1≤k-2 := by omega
    have smooth : Green (turnSeries A (m:=c)) := (turns_analytic A hs money).contDiffAt
    have vanish := (rays_jet smooth.analyticAt 3).1 (turns_low A hs money) k small
    funext x
    simp [Mosaic.surf,source,low,rye,vanish]
  · have inside : 1≤k-2 := by omega
    have total : 1+2+(k-2-1)=k := by omega
    simp only [Mosaic.surf,source,inside,if_pos,sprig]
    have same (l : ℕ) (e : l=k) :
        Blue.shine (rye (turnSeries A (m:=c)) l) k = rye (turnSeries A (m:=c)) k := by
      subst l
      exact Blue.shine_lit _
    exact same _ total

def polynomial (A : ℕ → Atom G 3) (d : ℕ) (x : Link G c) : ℝ :=
  ∑ k ∈ Finset.range (d+1), MvPolynomial.eval x (paint k (surf (source A) c (k-2) k))

theorem printed (A : ℕ → Atom G 3) (hs : 0<s) (money : SumBudget (fun i => (A i).budget s) a)
    (d : ℕ) : polynomial A d = blockTaylor d (turnSeries A (m:=c)) := by
  funext x
  unfold polynomial blockTaylor
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [rank A hs money,← jet_apply]
  exact rayon _ _ _

theorem enrolled (R : PathData G) : source R.cubic ∈ pool R := by
  simp [source,pool]

end YM.Integration.WilsonCubicPrintedTensor
