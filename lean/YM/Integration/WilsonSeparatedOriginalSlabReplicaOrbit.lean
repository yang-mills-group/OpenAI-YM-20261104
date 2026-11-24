import YM.Integration.WilsonSeparatedOriginalSlabReplicaTransport
import YM.Integration.WilsonSeparatedOriginalReplicaRegularity

/-! The full translated ultraviolet constellation at an arbitrary earlier
physical cell. The same displacement acts on every original insertion. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabReplicaOrbit
open Function Set MeasureTheory Finset Lattice Wilson RG Source
open RG05Readout Address Native Pulse Flatten MergeProof Accent Extra.Histories
open scoped Classical Topology BigOperators
variable {G:Gauge} (C:Family G) {N p k:ℕ}

local notation "I"=>Fin 3
open private shift from YM.Integration.WilsonSeparatedOriginalSlabReplicaTransport
open private coefficient entry tested stamp from YM.Integration.WilsonSeparatedOriginalReplicaRegularity

def surface (s:I→ℕ)(v:(i:I)→Palette C (s i))(r:ℝ)(Ψ:Wave I)(top:k≤N)(m:ℕ)(g:Body)(U:I → Config G (C.side N p)):ℂ:=
  premiums C s m k r*∑y:I→Site (C.side k p),WilsonSeparatedOriginalReplicaRegularity.meeting s v y top Ψ r g U
theorem regular (s:I→ℕ)(v:(i:I)→Palette C (s i))(r:ℝ)(Ψ:Wave I)(top:k≤N)(m:ℕ)(g:Body):
    Continuous (surface C (p:=p) s v r Ψ top m g):=continuous_const.mul (continuous_finsetSum _ (fun y _=>WilsonSeparatedOriginalReplicaRegularity.regular s v y top Ψ r g))

private theorem lives (s:I→ℕ)(v:(i:I)→Palette C (s i))(o:I→Site (C.side k p))(h:k≤N)(Ψ:Wave I)(r:ℝ)(g:Body)(U:I → Config G (C.side N p)):
    IntegrableOn (fun z:E4=>g.val z*WilsonSeparatedOriginalReplicaWave.scalp s v o h (cropX Ψ o r z) U) Native.box:=by
  have cash (z:E4):WilsonSeparatedOriginalReplicaWave.scalp (C:=C) s v o h (cropX (C:=C) Ψ o r z) U=
      ∑t:I→Site (C.S.toDepth h p).count,∑a:(i:I) → Mark C (s i),coefficient s o h Ψ r t z a*entry s v o h t a U:=by
    unfold WilsonSeparatedOriginalReplicaWave.scalp
    simp only [LinearMap.sum_apply,LinearMap.smul_apply,Finset.sum_apply,Pi.smul_apply,LinearMap.comp_apply,smul_eq_mul]
    apply Finset.sum_congr rfl;intro t _
    change _*(∑a:(i:I) → Mark C (s i),stamp s o h Ψ r t z a*entry s v o h t a U)=_
    rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro a _;exact (mul_assoc ..).symm
  have lives (t:I→Site (C.S.toDepth h p).count)(a:(i:I) → Mark C (s i)):Integrable
      (fun z:E4=>g.val z*(coefficient s o h Ψ r t z a*entry s v o h t a U)) (volume.restrict Native.box):=by
    simpa only [mul_assoc] using (tested s o h Ψ r t a g).mul_const (entry s v o h t a U)
  simp_rw [cash,Finset.mul_sum]
  exact integrable_finsetSum _ (fun t _=>integrable_finsetSum _ (fun a _=>lives t a))

theorem original (D:I→ℕ) (v:(i:I)→Palette C (D i)) (r:ℝ) (Ψ:Wave I) (top:k≤N) {cap B:ℝ}
    (rp:0<r) (enclosed:∀x∈tsupport Ψ.val,∀i,‖x i‖≤cap) (room:r*cap+2*C.S.a k<C.S.radius p)
    (far:B+r*cap<C.S.radius p) (m:ℕ) (o:Site (C.side k p)) (inside:∀z∈Native.box,‖voyager C p k o z‖≤B)
    (g:Body) (U:I → Config G (C.side N p)):
    surface C D v r Ψ top m g (fun i=>Lattice.pull 1 ((C.S.toDepth top p).embed o) (U i))=
      ∫z in Native.box,g.val z*((∏_i:I,(r:ℂ)⁻¹^4)*WilsonSeparatedOriginalSlabReplicaTransport.multi C m N p D v (rel r Ψ (voyager C p k o z)) U):=by
  let V:=fun i:I=>Lattice.pull 1 ((C.S.toDepth top p).embed o) (U i)
  let h (y:I→Site (C.side k p)) (z:E4):=g.val z*WilsonSeparatedOriginalReplicaWave.scalp D v y top (cropX Ψ y r z) V
  have row (y:I→Site (C.side k p)): IntegrableOn (h y) Native.box:=lives C D v y top Ψ r g V
  have point (z:E4) (hz:z∈Native.box):g.val z*((∏_i:I,(r:ℂ)⁻¹^4)*WilsonSeparatedOriginalSlabReplicaTransport.multi C m N p D v (rel r Ψ (voyager C p k o z)) U)=
      premiums C D m k r *∑y:I→Site (C.side k p),h y z:=by
    rw [WilsonSeparatedOriginalSlabReplicaTransport.original (C:=C) D v r Ψ top rp enclosed room far m o z hz (inside z hz)]
    simp only [Pi.smul_apply,smul_eq_mul,Finset.sum_apply,shift,premiums,Finset.prod_mul_distrib]
    dsimp only [h,V];rw [←Finset.mul_sum];ring
  rw [setIntegral_congr_fun Pert.Cellular.cells_compact.measurableSet point,integral_const_mul,
    integral_finsetSum _ (fun y _=>row y)]
  rfl

end YM.Integration.WilsonSeparatedOriginalSlabReplicaOrbit
