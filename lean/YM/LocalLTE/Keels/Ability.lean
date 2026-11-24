import YM.LocalLTE.Drift.Story
/-!
# Inverting a predicted frame transport

At each step of the actual-history stencil: predict the pivot also (do
not use real *next* basis reindexing to issue this calibrated preview). We
also expose the norm after re-expression in those normalized coordinates
and to the actual lead at the destination. This doesn't say one can roll
only the last outputs of this step onward; the running column algorithm
`FileBank` uses an angular order ladder, accumulates aligned stencils and
uses true previously selected basis policies. It prices calls at that
incoming level's actual axes. Need different theorem if composing in a
formally predetermined global-frame scheme.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Keels
open Function Filter Lattice Wilson RG Source Labels Extra.Histories Bid
open LocalLTE.Vinca LocalLTE.Drift LocalLTE.FrameBox AnalyticBridge VerifiedReset Collection Price PhysicalNext.Repeat Blush
open Push Local Planned.GuardedAtom LocalLTE.River YM.MergeProof
open Finset MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{H:History G}{N m p:ℕ}{d:ℕ}(F:Labels.Frame G d)
open Work.G08
variable {a b e α:ℝ}
local notation "Ψ"=> F.Coeff
local notation "K"=> F.coeffSize
variable (V:F.Coeff ≃ₗ[ℂ] F.Coeff) (T:F.Coeff →ₗ[ℂ] F.Coeff)
lemma upward (h:e ≤ (1/2:ℝ))(hp:∀ x:Ψ, K (V x - T x) ≤ e*K (V x)) (x:Ψ): K (V x) ≤ 2*K (T x)∧ K (T x)≤2*K (V x):=by
    have hx:=size_triangle F (V x) (T x)
    have ht:=size_triangle F (T x) (V x); rw [size_sub_rev] at ht
    constructor<;> linarith [hp x,mul_le_mul_of_nonneg_right h (size_nonneg F (V x)), size_nonneg F (V x)] -- he not explicitly needed remove
lemma supplies (he:0 ≤ e)(h:e ≤ (1/2:ℝ))(hp:∀ x:Ψ, K (V x - T x) ≤ e*K (V x)) : ∃ L: Ψ≃ₗ[ℂ] Ψ, L.toLinearMap=T ∧ ∀ y:Ψ, K (V (L.symm y))≤ 2*K y∧ K (V (L.symm y)- y)≤ e* (2*K y):=by
    have hi:Injective T:=by intro u v hz; have hb:=upward F V T h hp (u-v); rw [map_sub T,hz,sub_self] at hb; refine sub_eq_zero.mp (map_eq_zero_iff V V.injective|>.1 (size_separates F _ (hb.1.trans ?_))); simp [Frame.coeffSize]
    have ht:Surjective T:= (LinearMap.injective_iff_surjective).1 hi
    let Q: Ψ≃ₗ[ℂ]Ψ:= LinearEquiv.ofBijective T ⟨hi,ht⟩
    refine ⟨Q, rfl,fun i=>?_⟩; have hi:T (Q.symm i)=i:= Q.apply_symm_apply i; have hZ : K (V (Q.symm i))≤ 2*K i := by have hz:=(upward F V T h hp (Q.symm i)).1; rwa [hi] at hz
    exact ⟨hZ,(show K (V (Q.symm i)-i)≤ e*K (V (Q.symm i)) from (by have ht:=hp (Q.symm i); rwa [hi] at ht)).trans (mul_le_mul_of_nonneg_left hZ he)⟩
end YM.LocalLTE.Keels
