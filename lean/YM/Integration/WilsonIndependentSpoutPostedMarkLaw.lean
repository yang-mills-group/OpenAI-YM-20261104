import YM.Integration.WilsonIndependentSpoutAmbientMark
import YM.Integration.WilsonIndependentSpoutFiniteExitRows

/-! The authentic old mark on the same finite free axis, and its cancellation against the actual vacuum. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutPostedMarkLaw
open Function PowerSeries Matrix Lattice RG WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open WilsonCoeffUV.Power WilsonCoeffUV.Soil WilsonCoeffUV.Mer RegulatorIR RegulatorIR.Geometry
open PertExtension Tree FreeResolvent Metric Precision Exterior
open WilsonIndependentConditionalRawSpout (finite)
open scoped BigOperators Classical Matrix
variable {X I J:Type}[Fintype X][Fintype I][Fintype J]

theorem expense (C:Matrix X X ℝ){V W:Pal ℝ X}{k:ℕ}(scope:shellK 2 V)(bare:V 0=0)
    (span:shellK k W)(smooth:∀i,Pure (W i)):
    (∀ e,FiniteGen (finite C V W k e)) ∧ ∀ e,Pure (finite C V W k e):=by
  refine ⟨fun e=>finite_sum fun j _=>finite_stops (stops_bul C (span_abr C scope bare) k span) j e,?_⟩
  intro e r
  change Smooth ((∑i∈Finset.range (k+3*e+1),bul C (abr C V) W i e) r)
  rw [Finset.sum_apply]
  exact Smooth.sum fun i _=>pure_bul C (abr C V) smooth i e r

theorem cancel {R:Type}[CommRing R]{a b H:PowerSeries R}{p:ℕ}(paid:IsUnit H)
    (h:Equal p (H*a) (H*b)):Equal p a b:=by
  obtain ⟨u,rfl⟩:=paid
  simpa only [←mul_assoc,Units.inv_mul,one_mul] using (Equal.refl ((u⁻¹:Units (PowerSeries R)):PowerSeries R) p).mul h

variable {G:Gauge}{f c:Side}
theorem inlet (S:StepData c f)(F:Forest S.ratio)(Q:Matrix (Woods G f) (Woods G c) ℝ)
    {W:PChart G f}{k:ℕ}(span:shellK k W)(α:Cost)(unit:constantCoeff α=1):
    loom (panSlice G S F Q) (flash (srCold (mix α W) (0:Matrix (Woods G f) (Woods G c) ℝ)))=
      redo α (loom (camSlice G S F Q) (Blue.flash W)):=by
  rw [WilsonIndependentSpoutSchurFrame.linear α unit,redo_stern α span]
  unfold srCold
  rw [←loom_fade _ _ (finite_shell (mix_length (A:=α) span))]
  refine (RingHom.congr_fun (loom_loom (camber G (0:Matrix (Woods G f) (Woods G c) ℝ))
    (panSlice G S F Q)) (Blue.flash (mix α W))).trans ?_
  apply congrArg (fun M=>loom M (Blue.flash (mix α W)))
  rw [show camber G (0:Matrix (Woods G f) (Woods G c) ℝ)=leftFlag _ _ by simp [camber],
    panSlice,camSlice,←Matrix.mul_assoc,(arm_ground G Q).1]

end YM.Integration.WilsonIndependentSpoutPostedMarkLaw
