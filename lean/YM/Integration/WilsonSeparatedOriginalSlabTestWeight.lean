import YM.Integration.WilsonSeparatedOriginalSlabTestDirections
import YM.Integration.WilsonSeparatedOriginalSlabReplicaStencil
import YM.Integration.WilsonSeparatedOriginalSlabUniformRun

/-! The authentic common-cell weights of the independent and measured experiments use a fixed external derivative budget. -/
noncomputable section
set_option maxHeartbeats 200000
set_option autoImplicit false
set_option quotPrecheck false
namespace YM.Integration.WilsonSeparatedOriginalSlabTestWeight
open Function MeasureTheory Finset Lattice RG05Readout Address Native Nuclear Pulse Flatten
open WilsonSeparatedOriginalSlabTestDirections WilsonSeparatedOriginalSlabReplicaStencil
open private location coefficient exposed tested from YM.Integration.WilsonSeparatedOriginalReplicaRegularity
open scoped Classical BigOperators Topology ContDiff
local notation "I"=>Fin 3
variable (s:I→ℕ)

def tariff:ℝ:=∑k:(i:I)→Letter (s i),Classical.choose (WilsonSeparatedOriginalSlabTestDirections.original s k)

theorem paid (k:(i:I)→Letter (s i))(f:Wave I)(x:Cloud I):
    ‖(perform s k f).val x‖ ≤ tariff s*‖iteratedFDeriv ℝ (order s k) f.val x‖:=by
  let c:=fun a:(i:I)→Letter (s i)=>Classical.choose (WilsonSeparatedOriginalSlabTestDirections.original s a)
  have pos:∀a,0≤c a:=fun a=>(Classical.choose_spec (WilsonSeparatedOriginalSlabTestDirections.original s a)).1
  exact ((Classical.choose_spec (WilsonSeparatedOriginalSlabTestDirections.original s k)).2 f x).trans
    (mul_le_mul_of_nonneg_right (single_le_sum (fun a _=>pos a) (mem_univ k)) (norm_nonneg _))

theorem nonneg:0≤tariff s:=sum_nonneg fun a _=>(Classical.choose_spec (WilsonSeparatedOriginalSlabTestDirections.original s a)).1

variable {G:Gauge}{C:Family G}{b N per:ℕ}
local notation "Letters"=>(i:I)→Mark C (s i)

def factor (h:b≤N)(r:ℝ)(a:Letters):ℂ:=
  (∏i:I,ratioX (C.S.toDepth h per) (s i))*
    (((r⁻¹*C.S.a b)*(((C.S.toDepth h per).count.val:ℝ)⁻¹):ℝ):ℂ)^(order s (fun i=>(a i).1))

def expense (h:b≤N)(r:ℝ)(a:Letters)(g:Body):ℝ:=
  (∫z in Native.box,‖g.val z‖)*‖factor (per:=per) s h r a‖*tariff s

theorem original (o:I→Site (C.side b per))(h:b≤N)(r:ℝ)(t:I→Site (C.S.toDepth h per).count)(a:Letters)(g:Body)
    (f:Wave I){M:ℕ}{X:ℝ}(degree:order s (fun i=>(a i).1)≤M)(fit:Tall f M 1 X):
    ‖weight s o h r t a g f‖ ≤ expense (per:=per) s h r a g*X:=by
  let A:=‖factor (per:=per) s h r a‖
  have point (z:E4):‖g.val z*atSite s o h r t z a f‖ ≤ ‖g.val z‖*(A*(tariff s*X)):=by
    have formed:atSite s o h r t z a f=factor (per:=per) s h r a*(perform s (fun i=>(a i).1) f).val (location o h r t z):=by
      change coefficient s o h f r t z a=_
      rw [coefficient,exposed];unfold factor order;ring
    rw [formed,norm_mul,norm_mul]
    have bill:‖(perform s (fun i=>(a i).1) f).val (location o h r t z)‖ ≤ tariff s*X:=
      (paid s _ f _).trans (mul_le_mul_of_nonneg_left
        (by simpa only [one_pow,one_mul] using fit _ degree (location o h r t z)) (nonneg s))
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left bill (norm_nonneg _)) (norm_nonneg _)
  have ig:IntegrableOn (fun z:E4=>‖g.val z‖) Native.box:=
    ContinuousOn.integrableOn_compact Pert.Cellular.cells_compact (show ContDiff ℝ ∞ g.val from g.2).continuous.norm.continuousOn
  calc
    ‖weight s o h r t a g f‖ ≤ ∫z in Native.box,‖g.val z*atSite s o h r t z a f‖:=norm_integral_le_integral_norm _
    _ ≤ ∫z in Native.box,‖g.val z‖*(A*(tariff s*X)):=integral_mono
      (tested s o h f r t a g).norm (ig.mul_const _) point
    _ = expense (per:=per) s h r a g*X:=by rw [integral_mul_const];unfold expense A;ring

local notation "M"=>WilsonSeparatedOriginalSlabUniformRun.testRank s+1
theorem tested_ball (o:I→Site (C.side b per))(h:b≤N)(r:ℝ)(t:I→Site (C.S.toDepth h per).count)(a:Letters)(g:Body)
    {K:Set (Points 3)}{X:ℝ}(xp:0≤X)(φ:YM.Test 3)(fit:WilsonSeparatedOriginalSlabTestNorm.Tested K M X φ):
    ‖weight s o h r t a g (WilsonSeparatedOriginalProfileTest.wave φ)‖ ≤
      expense (per:=per) s h r a g*(WilsonSeparatedOriginalSlabTestNorm.scale M*X):=by
  apply original s o h r t a g («M»:=M)
  · apply (grades s _).trans
    unfold WilsonSeparatedOriginalSlabUniformRun.testRank
    have hsum:(∑i:I,s i) ≤ ∑i:I,(s i+2):=sum_le_sum fun i _=>Nat.le_add_right _ _
    omega
  · exact WilsonSeparatedOriginalSlabTestNorm.jets xp φ fit

end YM.Integration.WilsonSeparatedOriginalSlabTestWeight
