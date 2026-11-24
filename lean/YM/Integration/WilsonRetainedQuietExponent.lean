import YM.Integration.WilsonRetainedBlockKernel
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Pane.Null

/-! The full pre-reset incoming exponent on the finite quiet chart. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000

noncomputable section
namespace YM.Integration.WilsonRetainedQuietExponent
open Function Finset Filter Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Presented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open LocalTaylorR2 LocalTaylorR2.Canvas LocalTaylorR2.Port Work.G05 Analysis
open PhysicalNext.Repeat WilsonRetainedBlockPrimitive WilsonRetainedBlockKernel
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {n c f : Side} {S : StepData c f} {T : Tube G S} {P : Teller G}
variable {s : ℝ} {R : Rep G f}

private theorem retained {U : Config G n} {t : ℝ} (A : Clip) {x : Site n}
    (ht : 0 ≤ t) (h : ∀ p : Cell n, G.chord (faceValue U p) ≤ t) : PathData.kept A t x U :=
  fun p => (h p).trans (le_mul_of_one_le_right ht (Real.one_le_exp (div_nonneg
    (Nat.cast_nonneg _) A.radius_pos.le)))

private theorem capped (A : Clip) (W : PathData G) (j d : ℕ) (t : ℝ) (U : Config G n)
    (ht : 0 ≤ t) (h : ∀ p : Cell n, G.chord (faceValue U p) ≤ t) :
    (∑ p, crown W A j d t U p) = kinetic A.direct U (plotted W A j d U) := by
  rw [rows]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [crown,Pressure.trunk,if_pos (retained A ht h),PathData.clipped,if_pos (h p),G.chord_price]
  ring

private theorem completed (A : Clip) (W : PathData G) (j d : ℕ) (t : ℝ) (U : Config G n)
    (ht : 0 ≤ t) (h : ∀ p : Cell n, G.chord (faceValue U p) ≤ t) :
    (∑ p,tails W A j d t p U) =
      Precision.quadratic A W U - kinetic A.direct U (plotted W A j d U) := by
  rw [rows,Precision.quadratic,←Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [tails,if_pos (retained A ht h)]
  ring

/-- Every old letter, including its actual additive activity, is retained.
This additive identity has no exceptional-sector denominator. -/
theorem old (H : Intake P T s R) (U : Config G f) (V : Config G c) :
    (∑' i, Raw.expo T s R U V i) = R.exponent U - R.v * Fintype.card (Site f) +
      R.beta*(cutR R (till s) U + Raw.outTail T s V) := by
  let A (h : Signed) := ∑ i, crown R.path R.clip (till s) 1 R.p.threshold (pull h 0 U) i
  have hp (h : Signed) : R.path.principal R.clip R.p R.beta (pull h 0 U) =
      reduced R (till s) (pull h 0 U) + R.beta*A h := by
    simp only [PathData.principal,A,reduced,cuff,Finset.sum_sub_distrib,mul_sub,mul_add]
    abel
  have he : R.path.inChannels R.clip R.p R.beta U =
      averaged (fun h=>reduced R (till s) (pull h 0 U)) + R.beta*cutR R (till s) U := by
    simp only [PathData.inChannels,averaged,hp,Finset.sum_add_distrib,←Finset.mul_sum,cutR,A]
    ring
  rw [(Raw.income H U V).tsum_eq,Rep.exponent,he]
  ring

private theorem fee (h : P.Funds S T) (U : Config G f) (V : Config G c)
    (k : S.Choices) (a : Signed) :
    noiseTaylor S (pull a 0 V) (pull a 0 U) (Oriented.choice a k) = noiseTaylor S V U k := by
  have eq (Q Z : Config G c) : S.kernel.penalty*(∑ i,G.price (Z i*(Q i)⁻¹)) =
      ∑ i,monetary S Q Z i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [monetary,wire,G.chord_price]
    ring
  unfold noiseTaylor
  rw [eq,eq, (Oriented.carry a (SectorMeasure.funds_branch h) k U).2]
  simp_rw [monetary,wire_pulled]
  exact Equiv.sum_comp (StepData.sendBonds a 0) (monetary S (S.prediction U k) V)

/-- The actual signed sum, on the common quiet chart, is the original
incoming represented exponent and the full branch penalty with the
prescribed outgoing kinetic base. -/
theorem original (H : Intake P T s R) (U : Config G f) (V : Config G c) (k : S.Choices)
    (fine : ∀ a : Signed, ∀ i : Cell f,G.chord (faceValue (pull a 0 U) i) ≤ R.p.threshold)
    (coarse : ∀ a : Signed, ∀ i : Cell c,G.chord (faceValue (pull a 0 V) i) ≤ Pressure.temp s) :
    (∑' i,Raw.expo T s R U V i) -
      R.beta*(averaged fun a=>∑ i,loft T s (pull a 0 U) (Oriented.choice a k) (pull a 0 V) true i) =
      R.exponent U - R.v*Fintype.card (Site f) +
        R.beta*(Precision.secondTerm T.low T.down V - noiseTaylor S V U k) := by
  let A (a : Signed) := kinetic T.high.direct (pull a 0 U) (T.Xf (till s) (pull a 0 U))
  let B (a : Signed) := kinetic T.low.direct (pull a 0 V) (T.Xn (till s) (pull a 0 V))
  have ht : 0 ≤ Pressure.temp s := by unfold Pressure.temp; positivity
  have hf : cutR R (till s) U = averaged A := by
    apply congrArg averaged
    funext a
    exact (capped R.clip R.path (till s) 1 R.p.threshold (pull a 0 U) R.p.threshold_pos.le (fine a)).trans
      (by rw [H.received.clip,H.received.path]; rfl)
  have hc : Raw.outTail T s V = Precision.secondTerm T.low T.down V - averaged B := by
    unfold Raw.outTail
    have h (a : Signed) := completed T.low T.down (till s) S.patch.L.val (Pressure.temp s)
      (pull a 0 V) ht (coarse a)
    simp_rw [h]
    exact av_sub _ _
  have h (a : Signed) : (∑ i,loft T s (pull a 0 U) (Oriented.choice a k) (pull a 0 V) true i) =
      A a + noiseTaylor S V U k - B a := by
    rw [WilsonRetainedBlockPrimitive.action,← Finset.mul_sum,
      ←fee H.ready U V k a]
    rfl
  rw [old H U V,hf,hc]
  simp_rw [h]
  rw [av_sub,av_add,av_const]
  ring

end YM.Integration.WilsonRetainedQuietExponent
end
