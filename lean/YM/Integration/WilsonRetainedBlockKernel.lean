import YM.Integration.WilsonRetainedBlockPrimitive
import YM.Integration.MSFixedRatioPrimitiveAction

/-! Completion of the finite path action and its original blocking kernel. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000

noncomputable section
namespace YM.Integration.WilsonRetainedBlockKernel
open Function Finset Filter Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open LocalTaylorR2 LocalTaylorR2.Canvas LocalTaylorR2.Port Work.G05 Analysis
open Series FormalBulk08 WilsonRetainedBlockPrimitive
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {n c f : Side} {S : StepData c f}

/-- Reuniting the direct curvature square with its Wilson remainder leaves
the original nonlinear plaquette price and the truncated transported path. -/
theorem rows (P : PathData G) (A : Clip) (j d : ℕ) (U : Config G n) :
    kinetic A.direct U (plotted P A j d U) =
      ∑ i : Cell n, (A.direct*G.price (faceValue U i)+‖shorten P j d U i‖^2/2) := by
  rw [kinetic,show (∑ i : Twin n, ‖plotted P A j d U i‖^2/2) =
      ∑ i : Cell n, ∑ h : Bool, ‖plotted P A j d U (i,h)‖^2/2 from Fintype.sum_prod_type _,
      ←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fintype.sum_bool,plotted,if_true,Bool.false_eq_true,if_false,shoot,flaw,norm_smul,
    Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,
    Real.sq_sqrt A.quadratic_pos.le,G.chord_price]
  ring

/-- The genuine long-pair series supplies precisely the missing transported
quadratic on a quiet field. Its pair labels retain their lifted path lengths. -/
theorem complete {P : PathData G} {A : Clip} {σ C Λ : ℝ} (hp : P.Bounds A σ C Λ)
    (j d : ℕ) (t : ℝ) (U : Config G n) (hq : ∀ i : Cell n, PathData.kept A t i.1 U) :
    kinetic A.direct U (plotted P A j d U) + (∑ i : Cell n,∑' v,pairTail P A j d t i U v) =
      Precision.quadratic A P U := by
  rw [rows,Precision.quadratic,←Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(pair_sum hp j d t i U).tsum_eq,tails,if_pos (hq i)]
  ring

/-- Summing the authentic fine and coarse path tails on the same branch
closes the complete quadratic action. -/
theorem quiet (T : Tube G S) (s t₁ t₀ : ℝ) (U : Config G f) (V : Config G c)
    (k : S.Choices) {σ₁ C₁ Λ₁ σ₀ C₀ Λ₀ : ℝ}
    (h₁ : T.up.Bounds T.high σ₁ C₁ Λ₁) (h₀ : T.down.Bounds T.low σ₀ C₀ Λ₀)
    (fine : ∀ i : Cell f, PathData.kept T.high t₁ i.1 U)
    (coarse : ∀ i : Cell c, PathData.kept T.low t₀ i.1 V) :
    (∑ i,loft T s U k V true i) + (∑ i : Cell f,∑' v,pairTail T.up T.high (till s) 1 t₁ i U v) -
       (∑ i : Cell c,∑' v,pairTail T.down T.low (till s) S.patch.L.val t₀ i V v) =
        Precision.quadratic T.high T.up U + noiseTaylor S V U k - Precision.quadratic T.low T.down V := by
  rw [WilsonRetainedBlockPrimitive.action,noiseTaylor,←Finset.mul_sum]
  have hF := complete h₁ (till s) 1 t₁ U fine
  have hC := complete h₀ (till s) S.patch.L.val t₀ V coarse
  unfold Xf Xn
  linarith only [hF,hC]

/-- The physical blocking penalty in the chart is exactly the independent
finite-period branch kernel, at the full nonlinear finite field. -/
theorem original (T : Tube G S) (s : ℝ) (F : Forest S.ratio) (k : S.Choices)
    (a : Jets.Rays (Reef.Pine G S F ⊕ Reef.wire G c)) :
    let u:=MSFixedRatioPrimitiveAction.fields (G:=G) S F a
    let U:=represent u.2
    let V:=represent u.1
    (∑ i,loft T s U k V true i) = kinetic T.high.direct U (T.Xf (till s) U) +
      Reef.clack (G:=G) S k (Reef.graft (G:=G) (S:=S) F a) -
        kinetic T.low.direct V (T.Xn (till s) V) := by
  dsimp only
  rw [WilsonRetainedBlockPrimitive.action]
  unfold Reef.clack noiseTaylor
  rw [Finset.mul_sum]
  rfl

end YM.Integration.WilsonRetainedBlockKernel
end
