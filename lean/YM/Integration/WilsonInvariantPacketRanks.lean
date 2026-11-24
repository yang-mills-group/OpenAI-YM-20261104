import YM.Integration.LocalComparisonPackets
import YM.UVNext.FREE_STRESS_CERTIFICATE.Color

/-! The lowest ranks of a genuinely paid curvature packet on the original simple gauge group. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Integration.WilsonInvariantPacketRanks
open Function Finset Lattice Wilson RG Marker LocalComparison
open Comparison.Density.RenderM
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V] {R : Census V}
    {D : V → ComparisonDensity.Address.Orbit} {P : MarkedPackets D G n R}

omit [DecidableEq V] in
set_option linter.unusedSimpArgs false in
private def colorFunctional (T : Token G n (fun v => (D v).Mood) 1) (x : TestSpace D) : G.Color →ₗ[ℝ] ℂ where
  toFun v := T.touch x (fun _ => v)
  map_add' a b := by
    simp [Token.touch,Fin.prod_univ_one,PiLp.add_apply,add_mul,Finset.sum_add_distrib]
  map_smul' a b := by
    simp [Token.touch,Fin.prod_univ_one,PiLp.smul_apply,Complex.real_smul,smul_eq_mul,
      Finset.mul_sum,mul_assoc]

omit [DecidableEq V] in
/-- Rank zero is independent of all links, including the transport walks. -/
theorem constant {r : ℕ} (T : Token G n (fun v => (D v).Mood) r) (hr : r=0) (x : TestSpace D) (U W : Config G n) :
    T.read x U = T.read x W := by
  subst r
  apply congrArg (T.touch x)
  funext j
  exact Fin.elim0 j

omit [DecidableEq V] in
/-- In rank one the physically required simultaneous adjoint invariance kills the full complex coefficient. -/
theorem linear_zero {r : ℕ} (hG : G.Simple) (T : Token G n (fun v => (D v).Mood) r) (hr : r=1) (x : TestSpace D)
    (hi : ∀ a k, T.touch x (fun i => G.adjoint k (a i)) = T.touch x a) (U : Config G n) :
    T.read x U = 0 := by
  subst r
  let f := colorFunctional T x
  have inv (k : G.El) (v : G.Color) : f (G.adjoint k v) = f v := hi (fun _ => v) k
  have hf : f=0 := UVNext.FreeStress.no_linear hG f inv
  calc T.read x U = f ((T.path 0).atSite U T.root) := by
         apply congrArg (T.touch x)
         funext j
         exact congrArg (fun i => (T.path i).atSite U T.root) (Subsingleton.elim j 0)
       _ = 0 := by rw [hf]; rfl

/-- The complete native packet term at its original coupling is constant on fields in rank zero. -/
theorem zero {i : ℕ} (hr : P.rank i=0) (x : TestSpace D) (g : ℝ) (U W : Config G n) :
    P.term x g U i = P.term x g W i := by
  cases hT : P.packet i with
  | none => simp [MarkedPackets.term,hT]
  | some T => simp only [MarkedPackets.term,hT]; rw [constant T hr x U W]

/-- Every original purchased rank-one term vanishes at every test and field for every coupling. -/
theorem one {p : BudgetPoint} {address : V → Support n}
    {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n} {w : V → ℝ} {gp width budget : ℝ} {co cs : ℕ}
    (hG : G.Simple) (paid : P.Paid p address region w gp width budget co cs)
    {i : ℕ} (hr : P.rank i=1) (x : TestSpace D) (g : ℝ) (U : Config G n) : P.term x g U i = 0 := by
  cases hT : P.packet i with
  | none => simp [MarkedPackets.term,hT]
  | some T => simp only [MarkedPackets.term,hT]; rw [linear_zero hG T hr x (paid.symmetry i T hT x) U,mul_zero]

end YM.Integration.WilsonInvariantPacketRanks
