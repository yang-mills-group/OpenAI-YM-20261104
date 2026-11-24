import YM.Integration.WilsonSeparatedOriginalReplicaWave
import YM.RG05Readout.Pulse.Excursion

/-! The full smooth-source observable is continuous in each independently supplied gauge copy. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalReplicaRegularity
open Function Finset Set MeasureTheory RG Lattice Wilson Source RG05Readout RG05Readout.Native
open RG05Readout.Flatten RG05Readout.Pulse RG05Readout.Address
open scoped Classical BigOperators Topology ContDiff
variable {G:Gauge}{C:Family G}{I:Type}[Fintype I][DecidableEq I](s:I→ℕ)
variable {b N per:ℕ}(v:(i:I)→Palette C (s i))(o:I→Site (C.side b per))(h:b≤N)
set_option quotPrecheck false
local notation "A" => C.S.toDepth h per
local notation "Letters" => (i:I)→Mark C (s i)

private def location (r:ℝ)(t:I→Site (A).count)(z:E4):Cloud I:=
  (fun i=>r⁻¹ • (C.S.place (o i)-C.S.a b • z))+
    (r⁻¹*C.S.a b) • (fun i=>placeR A (t i))

private def stamp (Ψ:Wave I)(r:ℝ)(t:I→Site (A).count)(z:E4)(a:Letters):ℂ:=
  (Pulse.perform s (fun i=>(a i).1) (fork (((A).count.val:ℝ)⁻¹) (fun i=>placeR A (t i))
    (cropX (C:=C) Ψ o r z))).val 0

private theorem exposed (Ψ:Wave I)(r:ℝ)(t:I→Site (A).count)(z:E4)(a:Letters):
    stamp s o h Ψ r t z a=
      (((r⁻¹*C.S.a b)*(↑(A).count.val:ℝ)⁻¹:ℝ):ℂ)^(pegs s (fun i=>(a i).1) (Finset.univ.toList))*
      (Pulse.perform s (fun i=>(a i).1) Ψ).val (location o h r t z):=by
  unfold stamp cropX
  rw [fly_fork]
  unfold Pulse.perform;rw [machine_roll]
  simp only [SetLike.val_smul,Pi.smul_apply,smul_eq_mul]
  change _*(machine _ _ _ _).val (location o h r t z+_ • (0:Cloud I))=_
  rw [smul_zero,add_zero]

omit [DecidableEq I] [Fintype I] in
private theorem located (r:ℝ)(t:I→Site (A).count):Continuous (location o h r t):=by
  unfold location;apply Continuous.add _ continuous_const
  exact continuous_pi fun _=>continuous_const_smul .. |>.comp (continuous_const.sub (continuous_const_smul ..))

private def coefficient (Ψ:Wave I)(r:ℝ)(t:I→Site (A).count)(z:E4)(a:Letters):ℂ:=
  (∏i,ratioX A (s i))*stamp s o h Ψ r t z a

private def entry (t:I→Site (A).count)(a:Letters)(U:I → Config G (C.side N per)):ℂ:=
  ∏i,Pulse.key C N per (s i) (v i) (a i) ((A).assemble (o i,t i)) (U i)

private theorem tested (Ψ:Wave I)(r:ℝ)(t:I→Site (A).count)(a:Letters)(g:Body):
    IntegrableOn (fun z:E4=>g.val z*coefficient s o h Ψ r t z a) Native.box:=by
  apply ContinuousOn.integrableOn_compact Pert.Cellular.cells_compact
  have f:ContDiff ℝ ∞ g.val:=g.2
  have projection:ContDiff ℝ ∞ (Pulse.perform s (fun i=>(a i).1) Ψ).val:=(Pulse.perform s (fun i=>(a i).1) Ψ).2
  simp_rw [coefficient,exposed]
  exact (f.continuous.mul (continuous_const.mul (continuous_const.mul
    (projection.continuous.comp (located o h r t))))).continuousOn

omit [Fintype I] [DecidableEq I] in
private theorem key_regular {d:ℕ}(x:Palette C d)(a:Mark C d)(y:Site (C.side N per)):
    Continuous (Pulse.key C N per d x a y):=by
  unfold Pulse.key
  apply Continuous.const_smul
  exact ((C.localSection _).continuous_places _ _).comp (continuous_pull ..)

omit [DecidableEq I] in
private theorem entry_regular (t:I→Site (A).count)(a:Letters):Continuous (entry s v o h t a):=
  continuous_finsetProd _ fun i _=>(key_regular (v i) (a i) _).comp (continuous_apply i)

def meeting (Ψ:Wave I)(r:ℝ)(g:Body)(U:I → Config G (C.side N per)):ℂ:=
  ∫z in Native.box,g.val z*WilsonSeparatedOriginalReplicaWave.scalp (C:=C) s v o h (cropX (C:=C) Ψ o r z) U

private theorem finite_meet (Ψ:Wave I)(r:ℝ)(g:Body)(U:I → Config G (C.side N per)):
    meeting s v o h Ψ r g U=∑t:I→Site (A).count,∑a:Letters,
      (∫z in Native.box,g.val z*coefficient s o h Ψ r t z a)*entry s v o h t a U:=by
  have cash (z:E4):WilsonSeparatedOriginalReplicaWave.scalp (C:=C) s v o h (cropX (C:=C) Ψ o r z) U=
      ∑t:I→Site (A).count,∑a:Letters,coefficient s o h Ψ r t z a*entry s v o h t a U:=by
    unfold WilsonSeparatedOriginalReplicaWave.scalp
    simp only [LinearMap.sum_apply,LinearMap.smul_apply,Finset.sum_apply,Pi.smul_apply,LinearMap.comp_apply,smul_eq_mul]
    apply Finset.sum_congr rfl;intro t _
    change _*(∑a:Letters,stamp s o h Ψ r t z a*entry s v o h t a U)=_
    rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro a _;exact (mul_assoc ..).symm
  have lives (t:I→Site (A).count)(a:Letters):Integrable
      (fun z:E4=>g.val z*(coefficient s o h Ψ r t z a*entry s v o h t a U)) (volume.restrict Native.box):=by
    simpa only [mul_assoc] using (tested s o h Ψ r t a g).mul_const (entry s v o h t a U)
  unfold meeting;simp_rw [cash,Finset.mul_sum]
  rw [integral_finsetSum _ (fun t _=>integrable_finsetSum _ (fun a _=>lives t a))]
  apply Finset.sum_congr rfl;intro t _
  rw [integral_finsetSum _ (fun a _=>lives t a)]
  apply Finset.sum_congr rfl;intro a _;simp only [←mul_assoc,integral_mul_const]

theorem regular (Ψ:Wave I)(r:ℝ)(g:Body):Continuous (meeting s v o h Ψ r g):=by
  rw [funext (finite_meet s v o h Ψ r g)]
  exact continuous_finsetSum _ fun t _=>continuous_finsetSum _ fun a _=>
    continuous_const.mul (entry_regular s v o h t a)

theorem diagonal (Ψ:Wave I)(U:Config G (C.side N per)):
    WilsonSeparatedOriginalReplicaWave.scalp (C:=C) s v o h Ψ (fun _=>U)=Pulse.scalp (C:=C) s v o h Ψ U:=by
  unfold WilsonSeparatedOriginalReplicaWave.scalp Pulse.scalp
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,Finset.sum_apply,Pi.smul_apply,LinearMap.comp_apply]
  rfl

theorem physical (Ψ:Wave I)(r:ℝ)(m:ℕ)(g:Body):Continuous (constellation (C:=C) (p:=per) s v r Ψ h m g):=by
  change Continuous (fun U:Config G (C.side N per)=>constellation (C:=C) s v r Ψ h m g U)
  simp only [constellation,Pi.smul_apply,smul_eq_mul,Finset.sum_apply]
  apply continuous_const.mul
  apply continuous_finsetSum;intro y _
  have eq : (fun U:Config G (C.side N per)=>meeting s v y h Ψ r g (fun _=>U))=Pulse.meet s v r Ψ h y g:=by
    funext U;unfold meeting Pulse.meet;simp_rw [diagonal]
  rw [←eq];exact (regular s v y h Ψ r g).comp (continuous_pi fun _=>continuous_id)

end YM.Integration.WilsonSeparatedOriginalReplicaRegularity
