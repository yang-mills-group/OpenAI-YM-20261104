import YM.OPE.Compatible.Arch.Ilex
/-!
# Equating all replicas only within local connected patch
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra
open Function Filter Set Lattice Laurent Tree Woody Weir Cascade MeasureTheory LinearMap
open scoped Topology BigOperators ComplexConjugate Classical ContDiff ENNReal Matrix.Norms.Frobenius
open PertExtension Series GaussianScore Asymptotics Precision
variable {I J:Type}{G:Gauge}[Fintype I][Fintype J]
open Radial Zone ScriptJ Metric
local notation "W" => Chart.tangent G I
local notation "Lf" => Tested.germ
structure Dimes (G:Gauge)(I J:Type)[Fintype I][Fintype J] where
    q:Tile G I ≃ₜ Tile G J
    acts : MeasurePreserving q (Gem G I) (Gem G J)
    clan : q 1=1
    lifted : ContDiffAt ℝ ∞ (fun x: Keys G I=>unput (q (put x))) 0
namespace Dimes
variable (A:Dimes G I J)
nonrec def gradient (x:Keys G I):Keys G J := intake G J (A.q (put x))
lemma meas_grad:Measurable A.gradient:= introM.comp (A.q.measurable.comp putC.measurable)
lemma lead_grad : A.gradient =ᶠ[𝓝 0] fun x=> unput (A.q (put x)) :=by
      have hh:Tendsto (fun x=> A.q (put x)) (𝓝 0) (𝓝 1):=by simpa [A.clan] using (show Continuous (fun x=> A.q (put x)) from A.q.continuous.comp putC).tendsto 0
      exact introG.comp_tendsto hh
lemma gradC : ContDiffAt ℝ ∞ A.gradient 0:= A.lifted.congr_of_eventuallyEq A.lead_grad
@[simp] lemma grad0 : A.gradient 0=0:=by rw [A.lead_grad.eq_of_nhds]; simp [A.clan]
-- pull relations
lemma covered {u v:ℝ→Tile G J→ℝ} {p₁ q₁ p₂ q₂:JetS ℝ}(hu:∀ i,Measurable (u i))(hv: ∀ i,Measurable (v i))(a:Snap (fun t x=>u t (A.q x)) p₁)(b:Snap (fun t x=>v t (A.q x)) q₁) (c:Snap u p₂)(d:Snap v q₂)(h:q₁.s≠0)(ht:q₂.s≠0): p₁/q₁=p₂/q₂:=by
    obtain ⟨s,hs,hS⟩:= meetQuota a b h; obtain ⟨y,hy,hY⟩:= meetQuota c d ht
    let e := A.q; obtain ⟨z,hz,ho,hz1⟩:= _root_.mem_nhds_iff.mp (inter_mem hy (show e.symm ⁻¹' s∈𝓝 (1:Tile G J) from e.symm.continuous.continuousAt.preimage_mem_nhds (by rw [show _= _ from e.symm_apply_eq.mpr A.clan.symm];exact hs)))
    have hZ:=ho.mem_nhds hz1; let t:=e ⁻¹' z; have hP:t⊆s:= fun i hi=> by have hh : e.symm (e i) ∈ s := (hz (show e i∈z from hi)).2; simpa using hh
    have he:t∈𝓝 1:=e.continuous.continuousAt.preimage_mem_nhds (by rw [show e (1:Tile G I)=1 from A.clan];exact hZ)
    apply Reads.equality (f:=riddle u v z) _ (hY z (hz.trans inter_subset_left) hZ ho.measurableSet)
    apply (hS t hP he (ho.measurableSet.preimage e.measurable)).cong
    have h(q:Tile G J→ℝ)(hq:Measurable q) : (∫ x in t,q (e x) ∂Gem G I) = ∫ x in z,q x ∂Gem G J:=by
          rw [← A.acts.map_eq,Measure.restrict_map A.q.measurable ho.measurableSet, integral_map A.q.measurable.aemeasurable hq.aestronglyMeasurable]
    exact Eventually.of_forall fun i=> (congr_arg₂ HDiv.hDiv (h (u i) (hu i)).symm (h (v i) (hv i)).symm : (_:ℝ)/_= (_:ℝ)/_)
end Dimes
end YM.OPE.Libra
