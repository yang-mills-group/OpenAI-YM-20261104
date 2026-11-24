import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

namespace YM.MS.Bare.Focus

structure Metric (K:Type*) [Fintype K](τ:K→K→K→ℝ): Prop where
    skew i j k: τ i j k= -τ j i k
    acts i j k l: (∑ w:K,(τ i j w*τ w k l+τ j k w*τ w i l+τ k i w*τ w j l))=0
    trace i: (∑ j:K,τ j i j)=0
end YM.MS.Bare.Focus
