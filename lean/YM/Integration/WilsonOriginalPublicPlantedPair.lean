import YM.Integration.WilsonOriginalPublicPlantedFaces
import YM.Integration.WilsonOriginalPublicPivotCross

/-! Coercivity on the finite reflected board for the actual planted source.
The two single residuals and their joint residual contain every change of the
original section and every scalar feed before the reflected norm is taken. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonOriginalPublicPlantedPair
open Finset Function PowerSeries Lattice Wilson RG Labels Source PhysicalNext.Repeat.Legato
open XSpace XSpace.Cirrus XSpace.Normalize XSpace.Structure1 Maxwell Maxwell.Wick
open MS MS.Menus MS.Land MS.Theater Local.Physical
open WilsonOriginalPublicPivotCross (Film detector)
open WilsonOriginalPublicPivotReflected (sampled)
open WilsonOriginalPublicPivotFaces (tests)
open WilsonOriginalPublicPlantedFaces (occupied)
open WilsonPositionProgramPublicWickGram (nodes reading)
open WilsonPositionProgramPublicContrast (assay)
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (W:Initialize G) {I L:Type} [Fintype I] [Fintype L]
    (d:Fin 2→ℕ)(v:(i:Fin 2)→(R.family.labels.level (d i)).Coeff)
    (X:L→Sample 2)(μ:L→ℂ)(q:ℕ)(g:ℝ)(a:I→ℂ)(A B:I→Film W)

def pivots (x:Sample 2) (i:Fin 2) : Bare.Series (W.tree x.F.p) G :=
  ![(∑j,star (a j) • A j) x,(∑j,a j • B j) x] i

def residual (S:Finset (Fin 2)) : ℂ :=
  tests X μ q g (fun x=>occupied R W d v (pivots W a A B) x univ S)

theorem empty :
    tests X μ q g (fun x=>WilsonOriginalPublicPivotFaces.part R W d v (pivots W a A B) x univ ∅) =
      assay a a (fun j k=>detector W X μ q g (A j*B k)) := by
  let H:=detector W X μ q g
  have source :
      tests X μ q g (fun x=>WilsonOriginalPublicPivotFaces.part R W d v (pivots W a A B) x univ ∅) =
        H ((∑j,star (a j) • A j)*(∑k,a k • B k)) := by
    simp [H,detector,tests,WilsonOriginalPublicPivotReflected.evaluated,WilsonOriginalPublicPivotFaces.part,
      pivots,Fin.prod_univ_two]
  rw [source,Finset.sum_mul,map_sum,assay]
  apply sum_congr rfl
  intro j _
  rw [Finset.mul_sum,map_sum]
  apply sum_congr rfl
  intro k _
  simp only [smul_mul_assoc,mul_smul_comm,map_smul,smul_eq_mul]
  ring

local notation "D" T:max => residual R W d v X μ q g a A B T

theorem full :
    sampled R W d v X μ univ q g - assay a a (fun j k=>detector W X μ q g (A j*B k)) =
      D {0} + D {1} + D univ := by
  have entire:=WilsonOriginalPublicPlantedFaces.tested R W d v (pivots W a A B) X μ q g univ
  rw [empty R W d v X μ q g a A B] at entire
  have subsets : (univ : Finset (Fin 2)).powerset.erase ∅ = {{0},{1},univ} := by decide
  change _ = ∑S∈(univ:Finset (Fin 2)).powerset.erase ∅,residual R W d v X μ q g a A B S at entire
  rw [subsets,sum_insert (by decide),sum_insert (by decide),sum_singleton] at entire
  simpa only [add_assoc] using entire

theorem original {h:ℕ}{B₀:Local.Physical.Deck G} (axis:Axis) (basis:I→Glyph B₀ h)
    (independent:Injective basis) :
    ∃k τ:ℝ,0<k ∧ 0<τ ∧ ∀ (coarse:ℂ) (c z u e t:ℝ),
      0≤c → 1≤z → 0≤u → e*u≤1 → e*u^2≤1 → t≤1 →
      ‖(fun i j=>detector W X μ q g (A i*B j))-reading axis (nodes axis) basis‖≤τ →
      ‖coarse‖≤c*z^2 → ‖sampled R W d v X μ univ q g-coarse‖≤1 →
      ‖D {0}‖≤e*u*‖a‖ → ‖D {1}‖≤e*u*‖a‖ → ‖D univ‖≤e*u^2+t →
      ‖a‖≤ max 1 ((c+5)/k)*z := by
  obtain ⟨k,τ,hk,hτ,price⟩:=WilsonOriginalPublicPivotReflected.original R W axis basis independent
  refine ⟨k,τ,hk,hτ,?_⟩
  intro coarse c z u e t hc hz hu first both last near gross paid left right double
  apply price d v X μ q g coarse _ a c z u e t hc hz hu first both last near gross paid
  rw [norm_sub_rev,full]
  calc
    _ ≤ (‖D {0}‖+‖D {1}‖)+‖D univ‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (e*u*‖a‖+e*u*‖a‖)+(e*u^2+t) := add_le_add (add_le_add left right) double
    _ = _ := by ring

end YM.Integration.WilsonOriginalPublicPlantedPair
