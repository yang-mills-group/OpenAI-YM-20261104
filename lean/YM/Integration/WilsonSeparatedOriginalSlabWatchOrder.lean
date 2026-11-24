import YM.Integration.WilsonSeparatedOriginalSlabWatchTest
import YM.Integration.WilsonSeparatedOriginalSlabWatchDensity

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabWatchOrder
open Set Function MeasureTheory Spec OPE OPE.Orbits RG05Readout RG05Readout.Native RG05Readout.Pulse
open WilsonSeparatedOriginalSlabWatchDensity WilsonSeparatedOriginalSlabWatchMean
open scoped Topology Classical
variable {n:ℕ}{E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]

def coordinates (n:ℕ):Points n ≃L[ℝ] (Fin n→E4):=PiLp.continuousLinearEquiv 2 ℝ _

def permutation (n:ℕ):Points (Fintype.card (Fin n)) ≃L[ℝ] Points n:=
  ((coordinates _).trans (ContinuousLinearEquiv.piCongrLeft ℝ (fun _:Fin n=>E4) (runNames (Fin n)))).trans (coordinates n).symm

theorem slots (x:Points (Fintype.card (Fin n))):(permutation n x).ofLp=native x:=by
  funext i;obtain ⟨j,rfl⟩:∃j,(runNames (Fin n)) j=i:=(runNames (Fin n)).surjective i
  change ContinuousLinearEquiv.piCongrLeft ℝ (fun _:Fin n=>E4) (runNames (Fin n)) x.ofLp (runNames (Fin n) j)=x ((runNames (Fin n)).symm (runNames (Fin n) j))
  rw [Equiv.symm_apply_apply];exact Equiv.piCongrLeft_apply_apply (fun _:Fin n=>E4) (runNames (Fin n)) x.ofLp j

theorem volume_paid (n:ℕ):MeasurePreserving (permutation n) volume volume:=by
  have start:MeasurePreserving (coordinates (Fintype.card (Fin n))) volume volume:=Points.volume_product _
  have middle:MeasurePreserving (ContinuousLinearEquiv.piCongrLeft ℝ (fun _:Fin n=>E4) (runNames (Fin n))) volume volume:=volume_measurePreserving_piCongrLeft (fun _:Fin n=>E4) (runNames (Fin n))
  have finish:MeasurePreserving ((coordinates n).toHomeomorph.toMeasurableEquiv) volume volume:=Points.volume_product _
  exact finish.symm.comp (middle.comp start)

theorem read (f:Cloud (Fin n)→E):
    (∫x:Points (Fintype.card (Fin n)),f (native x))=∫x:Points n,f x.ofLp:=by
  simpa only [slots] using (volume_paid n).integral_comp (permutation n).toHomeomorph.measurableEmbedding (fun x=>f x.ofLp)

theorem source {θ:ℝ}(ht:θ∈Icc (0:ℝ) 1)(A:Set (Cloud (Fin n)))(bound:IsCompact A)
    (Ψ:Wave (Fin n))(filed:tsupport Ψ.val⊆A)(g:Body){η M:ℝ}(pos:0<η)
    (apart:∀x∈A,∀i j:Fin n,i≠j→η≤‖x i-x j‖)(size:∀x∈A,∀i,‖x i‖≤M)(K:Cloud (Fin n)→ℂ):
    (∫x:Points (Fintype.card (Fin n)),(wave θ Ψ g).val (native x)*K (native x))=
      (WilsonSeparatedOriginalSlabWatchTest.physical ht A bound Ψ filed g pos apart size).applyTo (fun y=>K y.ofLp):=
  read (fun y=>(wave θ Ψ g).val y*K y)

end YM.Integration.WilsonSeparatedOriginalSlabWatchOrder
