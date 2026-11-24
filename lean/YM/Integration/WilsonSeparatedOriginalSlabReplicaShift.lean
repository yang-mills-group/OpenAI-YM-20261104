import YM.Integration.WilsonSeparatedOriginalReplicaMeasure

/-! A common preserving spatial translation on a clamped Wilson probability
acts simultaneously on all five honest experiments in its third cumulant. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabReplicaShift
open Function MeasureTheory Lattice Wilson
open scoped BigOperators Classical Topology
variable {G:Gauge} {n:Side}
local notation "A"=>Config G n

theorem embedding (d:Site n):MeasurableEmbedding (pull 1 d:A→A):=by
  apply Topology.IsClosedEmbedding.measurableEmbedding
  apply Continuous.isClosedEmbedding (continuous_pull ..)
  intro a b equal
  have back:=congrArg (pull 1 (-d)) equal
  simpa [pull_pull,affine] using back

private theorem both {B:Type*}[MeasurableSpace B](μ:Measure B)(t:B→B)
    (sale:∀F:B→ℂ,(∫a,F (t a) ∂μ)=∫a,F a ∂μ)(F:B→B→ℂ):
    (∫a,∫b,F (t a) (t b) ∂μ ∂μ)=∫a,∫b,F a b ∂μ ∂μ:=by
  simp_rw [sale (F (t _))]
  exact sale (fun a=>∫b,F a b ∂μ)

private theorem three {B:Type*}[MeasurableSpace B](μ:Measure B)(t:B→B)
    (sale:∀F:B→ℂ,(∫a,F (t a) ∂μ)=∫a,F a ∂μ)(F:B→B→B→ℂ):
    (∫a,∫b,∫c,F (t a) (t b) (t c) ∂μ ∂μ ∂μ)=∫a,∫b,∫c,F a b c ∂μ ∂μ ∂μ:=by
  simp_rw [both μ t sale (F (t _))]
  exact sale (fun a=>∫b,∫c,F a b c ∂μ ∂μ)

theorem original (μ:Measure A)(d:Site n)(sale:MeasurePreserving (pull 1 d:A→A) μ μ)
    (H:(Fin 3→A)→ℂ):WilsonSeparatedOriginalReplicaMeasure.read μ (fun W=>H (fun i=>pull 1 d (W i)))=
      WilsonSeparatedOriginalReplicaMeasure.read μ H:=by
  let t:A→A:=pull 1 d
  have bought (F:A→ℂ):(∫a,F (t a) ∂μ)=∫a,F a ∂μ:=sale.integral_comp (embedding d) F
  have panel (a b c:A):(fun i=>t (![a,b,c] i))=![t a,t b,t c]:=by funext i;fin_cases i <;> rfl
  change WilsonSeparatedOriginalReplicaMeasure.read μ (fun W=>H (fun i=>t (W i)))=_
  simp only [WilsonSeparatedOriginalReplicaMeasure.read,panel]
  rw [bought (fun a=>H ![a,a,a]),both μ t bought (fun a b=>H ![a,a,b]),
    both μ t bought (fun a b=>H ![a,b,a]),both μ t bought (fun a b=>H ![b,a,a]),
    three μ t bought (fun a b c=>H ![a,b,c])]

end YM.Integration.WilsonSeparatedOriginalSlabReplicaShift
