import YM.Integration.WilsonSeparatedOriginalSlabReplicaOrbit
import YM.Integration.WilsonSeparatedOriginalReplicaScanner

/-! Exact integration of the common affine subcell test before any three-copy
measurement. Its complete stencil is finite, for every recorded derivative
and every native offset, even when the submitted action is not bounded. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabReplicaFilm
open Function MeasureTheory Set Finset Lattice Wilson RG Source
open RG05Readout Address Native Pulse Flatten
open scoped Classical Topology BigOperators
open private filed from YM.Integration.WilsonSeparatedOriginalReplicaScanner
open private coefficient entry entry_regular stamp tested finite_meet from YM.Integration.WilsonSeparatedOriginalReplicaRegularity
open WilsonSeparatedOriginalReplicaRegularity
variable {G:Gauge}{C:Family G}{n N per:ℕ}(s:Fin 3→ℕ)(v:(i:Fin 3)→Palette C (s i))
    (o:Fin 3→Site (C.side n per))(h:n≤N)
local notation "I"=>Fin 3
local notation "A"=>C.S.toDepth h per
local notation "Letters"=>(i:I)→Mark C (s i)
local notation "Space"=>I → Config G (C.side N per)

def cell (t:I→Site (A).count)(a:Letters):C(Space,ℂ):=⟨entry s v o h t a,entry_regular s v o h t a⟩
def film (Ψ:Wave I)(r:ℝ)(g:Body):C(Space,ℂ):=⟨meeting s v o h Ψ r g,regular s v o h Ψ r g⟩

private theorem point (Ψ:Wave I)(r:ℝ)(z:E4):filed s v o h (cropX (C:=C) Ψ o r z)=
    ∑t:I→Site (A).count,∑a:Letters,coefficient s o h Ψ r t z a • cell s v o h t a:=by
  ext U
  simp only [ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul]
  change WilsonSeparatedOriginalReplicaWave.scalp (C:=C) s v o h (cropX (C:=C) Ψ o r z) U=
    ∑t:I→Site (A).count,∑a:Letters,coefficient s o h Ψ r t z a*entry s v o h t a U
  unfold WilsonSeparatedOriginalReplicaWave.scalp
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,Finset.sum_apply,Pi.smul_apply,LinearMap.comp_apply,smul_eq_mul]
  apply Finset.sum_congr rfl;intro t _
  change _*(∑a:Letters,stamp s o h Ψ r t z a*entry s v o h t a U)=_
  rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro a _;exact (mul_assoc ..).symm

theorem original (Ψ:Wave I)(r:ℝ)(g:Body)(meter:C(Space,ℂ)→ₗ[ℂ]ℂ):
    meter (film s v o h Ψ r g)=∫z in Native.box,g.val z*meter (filed s v o h (cropX (C:=C) Ψ o r z)):=by
  have earn:film s v o h Ψ r g=∑t:I→Site (A).count,∑a:Letters,(∫z in Native.box,g.val z*coefficient s o h Ψ r t z a) • cell s v o h t a:=by
    ext U
    simp only [ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul]
    exact finite_meet s v o h Ψ r g U
  have cash (t:I→Site (A).count)(a:Letters):Integrable (fun z:E4=>g.val z*(coefficient s o h Ψ r t z a*meter (cell s v o h t a))) (volume.restrict Native.box):=by
    simpa only [mul_assoc] using (tested s o h Ψ r t a g).mul_const (meter (cell s v o h t a))
  rw [earn];simp only [point,map_sum,map_smul,smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun t _=>integrable_finsetSum _ (fun a _=>cash t a))]
  apply Finset.sum_congr rfl;intro t _
  rw [integral_finsetSum _ (fun a _=>cash t a)]
  apply Finset.sum_congr rfl;intro a _;simp only [←mul_assoc,integral_mul_const]

end YM.Integration.WilsonSeparatedOriginalSlabReplicaFilm
