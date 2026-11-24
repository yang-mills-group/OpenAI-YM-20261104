import YM.Integration.WilsonIndependentConditionalHeardMean
import YM.RegulatorIR.Diagram.Spokes

/-! Post-heat crop and draft on the actual torus with its reported
covariance, spring and all held angular ranks. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalPulledBoard
open Lattice RG Wilson Tree WilsonCoeffUV Blue WilsonCoeffUV.Convention FreeResolvent Exterior
open Metric Precision RegulatorIR RegulatorIR.Budget RegulatorIR.Diagram WilsonIndependentConditionalHeldGaussian
open Matrix PowerSeries Function
open scoped Classical BigOperators
variable {G:Gauge}{c f:Side}(S:StepData c f)(F:Forest S.ratio)(H:FaceRow)
    (Q:Matrix (Body 1 f) (Body 1 c) ℝ)

theorem move (M:Matrix (Woods G f) (Woods G c) ℝ)(b:Woods G c→ℝ):
    announce (groundM G M).transpose
        (Diagram.dilute (Embedding.inr:Woods G c↪Joint G f c) b)=Sum.elim (M*ᵥb) b:=by
  have seed:Diagram.dilute (Embedding.inr:Woods G c↪Joint G f c) b=held b:=by
    funext j
    cases j with
    | inl j=>exact dilute_miss _ _ _ (by simp)
    | inr j=>exact dilute_here _ _ _
  rw [seed]
  exact WilsonIndependentConditionalPostedMean.shifted M b

def output (Ñ:ChartRatio G)(P w:PChart G f)(k:ℕ):Orders (Woods G c):=
  let M:=extractV G S F Q
  let K:=fillSlots (Woods G c) (covariance G S F H)
  collectO (Embedding.inr:Woods G c↪Joint G f c) (groundM G M).transpose
    (endHeat k K (logHeat K (casePW S Ñ 0 P) false) (srCold w 0))

theorem original {Ñ:ChartRatio G}{P w:PChart G f}{k:ℕ}(hp:shellK 2 P)(ratio:LocalRatio Ñ)
    (wp:shellK (k+1) w)(branch:S.patch.Branches S.kernel G)(sym:(H.acts f).transpose=H.acts f)
    (pure:∀ i,Pure (P i))(wpure:∀ i,Pure (w i))(hf:(treeMatrix G S F H).PosDef):
    rated (fun e=>e+(k+1)) (output S F H Q Ñ P w (k+1))=flash (reed S F H Q Ñ P (k+1) w):=by
  ext1 e;apply MvPolynomial.funext;intro b
  let M:=extractV G S F Q
  have h:PowerSeries.map (emphasis b).toRingHom (rated (fun j=>j+(k+1)) (output S F H Q Ñ P w (k+1)))=
      PowerSeries.map (emphasis b).toRingHom (flash (reed S F H Q Ñ P (k+1) w)):=by
    unfold output;rw [collect_formula,move]
    exact WilsonIndependentConditionalHeardMean.original S F H Q hp ratio wp branch sym pure wpure hf b
  have t:=congrArg (coeff e) h
  simp only [coeff_map] at t
  rw [←MvPolynomial.aeval_eq_eval]
  exact t

end YM.Integration.WilsonIndependentConditionalPulledBoard
