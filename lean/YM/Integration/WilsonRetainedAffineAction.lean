import YM.Integration.WilsonRetainedQuietExponent
import YM.Integration.PhysicalForestAction

/-! The original incoming catalogue in the affine forest action.
The stored regular activity stays in the same fine configuration as the
kinetic energy, area and block penalty. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000

noncomputable section
namespace YM.Integration.WilsonRetainedAffineAction
open Function Finset Filter Matrix Lattice Wilson RG Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open LocalTaylorR2 LocalTaylorR2.Canvas LocalTaylorR2.Port Work.G05 Analysis PhysicalNext.Repeat
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open FreeResolvent Comparison.RG02 Stationary Marker Multi
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner

variable {G : Gauge} {n c f : Side} {S : StepData c f} {T : Tube G S}
variable {P : Teller G} {R : Rep G f} {s : ℝ}
variable {V : Type} [DecidableEq V] {C : Census V}

def before (T : Tube G S) (s : ℝ) (R : Rep G f) (k : S.Choices) (U : Config G f) (B : Config G c) :=
  (∑' i,Raw.expo T s R U B i) - R.beta*(averaged fun b=>
    ∑ i,loft T s (pull b 0 U) (Oriented.choice b k) (pull b 0 B) true i)

def incoming (R : Rep G f) (W : Bulk.Colors C G f) : Bulk.Colors C G f :=
  {W with vac := fun g U => g^2 * R.activities.additive R.p U}

private theorem clear {A : Type*} [TopologicalSpace A] {a : A} (U : A → Config G n)
    (hU : ContinuousAt U a) (h : U a=1) {t : ℝ} (ht : 0<t) :
    ∀ᶠ x in 𝓝 a, flags t (U x)=∅ := by
  have hi (p : Cell n) : ∀ᶠ x in 𝓝 a, G.chord (faceValue (U x) p) ≤ t := by
    have hc : Continuous (fun u : Config G n => G.chord (faceValue u p)) := by
      unfold faceValue
      fun_prop
    have hz : ((fun u : Config G n => G.chord (faceValue u p)) ∘ U) a < t := by
      change G.chord (faceValue (U a) p) < t
      rwa [h,faceValue,SliceRows.trivial,G.chord_one]
    exact ((hc.continuousAt.comp hU).tendsto.eventually (gt_mem_nhds hz)).mono fun x hx=>le_of_lt hx
  filter_upwards [eventually_all.mpr hi] with x hx
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨p,_,hp⟩ := (flags_spec ..).mp hv
  exact hp.not_ge (hx p)

private theorem oriented {U : Config G n} {t : ℝ} (h : flags t U=∅)
    (b : Signed) (i : Cell n) : G.chord (faceValue (pull b 0 U) i) ≤ t := by
  by_contra! hh
  have hi : i.1 ∈ flags t (pull b 0 U) := (flags_spec ..).mpr ⟨i,WilsonStartup.anchor_visit _,hh⟩
  rw [Pane.tranquility U h b 0] at hi
  exact Finset.notMem_empty _ hi

variable (F : Forest S.ratio) (M : Matrix (Woods G f) (Woods G c) ℝ)
variable (O : ChartRatio G)

def logRead (T : Tube G S) (s : ℝ) (R : Rep G f) (w : Sloc S F G) :=
  let U := PhysicalForestAction.field S F M w
  let B := mantle (rightArm w)
  R.beta*Precision.secondTerm T.low T.down B - before T s R (tac S) U B -
    unhaar O (camSlice G S F M *ᵥ w)

/-- The normalized physical pre-reset exponent, at the actual measured
temperature, is the complete affine action including the old activity. -/
theorem absolute (H : Intake P T s R) (hs : 0<s) (W : Bulk.Colors C G f) :
    ∀ᶠ w in 𝓝 (0 : Sloc S F G), ∀ g : ℝ, R.beta*g^2=1 →
      PhysicalForestAction.absoluteAction S F M (p:=R.clip) (P:=R.path) (O:=O)
        (incoming R W) g w = g^2*logRead F M O T s R w := by
  have hu : ContinuousAt (PhysicalForestAction.field S F M) 0 :=
    mantle_cont.continuousAt.comp (camSlice G S F M).mulVecLin.toContinuousLinearMap.continuous.continuousAt
  have hz : PhysicalForestAction.field S F M 0=1 := by
    rw [PhysicalForestAction.field,Matrix.mulVec_zero,mantle_zero]
  have hb : ContinuousAt (fun w : Sloc S F G => mantle (rightArm w)) 0 :=
    mantle_cont.continuousAt.comp rightGreen.continuousAt
  have ht : 0<Pressure.temp s := by unfold Pressure.temp; positivity
  filter_upwards [clear _ hu hz R.p.threshold_pos,clear _ hb (by rw [rightZero,mantle_zero]) ht] with w hf hc
  intro g hg
  let U:=PhysicalForestAction.field S F M w
  let B:=mantle (rightArm w)
  have hpre := WilsonRetainedQuietExponent.original H U B (tac S) (oriented hf) (oriented hc)
  have hlog : before T s R (tac S) U B =
      -(R.beta*mainTerm R.clip R.path U + Precision.loop R.path U) - R.activities.additive R.p U +
        R.beta*(Precision.secondTerm T.low T.down B - noiseTaylor S B U (tac S)) := by
    change _ = _ at hpre
    rw [Rep.exponent,Pane.crystalline R.path R.clip R.p R.beta U hf] at hpre
    unfold before
    rw [hpre]
    ring
  have hpen : jointPen G S (panSlice G S F M *ᵥ w)=noiseTaylor S B U (tac S) := by
    rw [jointPen,arm_pan]
    rfl
  unfold PhysicalForestAction.absoluteAction logRead
  dsimp only [incoming]
  rw [hpen,hlog]
  change _ = g^2 * _
  linear_combination (mainTerm R.clip R.path U + noiseTaylor S B U (tac S)) * (-hg)

end YM.Integration.WilsonRetainedAffineAction
