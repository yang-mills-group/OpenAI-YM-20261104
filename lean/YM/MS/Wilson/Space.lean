import YM.MS.Properties

set_option autoImplicit false
noncomputable section
namespace YM.MS.Native
open Function Filter Finset Set Koszul Plane Landau
open scoped Topology ContDiff
variable (G:Gauge)
abbrev Conn := G.ColorIndex
variable (P:Type)
abbrev Eyes := P ×Conn G
variable {G P}
variable (G)
abbrev Lot (A:Type*) := A→ G.Color
variable {G}
variable {Q:Type*} [DecidableEq Q]
abbrev baseC := EuclideanSpace.basisFun G.ColorIndex ℝ
def priv (k:Q × Conn G): Lot G Q:= Pi.single k.1 (baseC k.2)
section
variable [Fintype Q]
def projector (i:Q ×Conn G): Lot G Q→L[ℝ] ℝ := ((baseC.toBasis).coord i.2).toContinuousLinearMap ∘L ContinuousLinearMap.proj i.1
omit [DecidableEq Q][Fintype Q] in
lemma projector_k (i:Q×Conn G)(x:Lot G Q): projector i x=x i.1 i.2:= by simp [projector,baseC]
lemma frame (f:Lot G Q):∑ i, projector i f • priv i=f := by
    funext x; rw [Finset.sum_apply,Fintype.sum_prod_type]; simp_rw [projector_k,Pi.smul_apply,priv, Pi.single_apply, smul_ite, smul_zero]; rw [Finset.sum_eq_single x]; swap; · intro i hi hx; simp [Ne.symm hx]
    swap; · simp
    simpa using Landau.color_sum (f x)
end
end YM.MS.Native
