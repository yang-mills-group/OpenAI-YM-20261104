import YM.Integration.WilsonSeparatedOriginalSlabTestWeight
import YM.Integration.WilsonSeparatedOriginalReplicaSupport

/-! Every original offset and every independently retained mark has zero external weight outside a fixed pre-period region. -/
noncomputable section
set_option maxHeartbeats 200000
set_option quotPrecheck false
set_option autoImplicit false
namespace YM.Integration.WilsonSeparatedOriginalSlabActiveWeights
open Function Finset Lattice RG05Readout Address Native Nuclear Pulse Flatten MeasureTheory
open WilsonSeparatedOriginalSlabTestWeight WilsonSeparatedOriginalSlabReplicaStencil WilsonSeparatedOriginalSlabTestDirections
open private location coefficient exposed from YM.Integration.WilsonSeparatedOriginalReplicaRegularity
open scoped Classical BigOperators Topology
local notation "I"=>Fin 3
variable {G:Gauge}{C:Family G}{b N per:ℕ}

def range (C:Family G)(b:ℕ)(r cap:ℝ):ℕ:=⌈(r*cap+2*C.S.a b)/C.S.a b⌉₊

theorem contains (C:Family G)(b:ℕ)(r cap:ℝ):
    r*cap+2*C.S.a b≤C.S.a b*(range C b r cap:ℝ):=by
  rw [mul_comm (C.S.a b)]
  exact (div_le_iff₀ (C.S.a_pos b)).mp (Nat.le_ceil _)

theorem original (s:I→ℕ)(o:I→Site (C.side b per))(h:b≤N){r cap:ℝ}(rp:0<r)
    (f:Wave I)(shape:∀x∈tsupport f.val,∀i,‖x i‖≤cap)
    (outside:o∉Pulse.area (C:=C) (p:=per) (b:=b) (range C b r cap))
    (t:I→Site (C.S.toDepth h per).count)(a:(i:I)→Mark C (s i))(g:Body):
    weight s o h r t a g f=0:=by
  change (∫z in Native.box,g.val z*atSite s o h r t z a f)=0
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro z hz
  have absent:location o h r t z∉tsupport f.val:=by
    intro live
    apply outside
    simp only [Pulse.area,Finset.mem_filter,Finset.mem_univ,true_and]
    intro i
    exact_mod_cast le_of_mul_le_mul_left ((Pulse.understood h r f rp shape t z hz o live i).trans (contains C b r cap)) (C.S.a_pos b)
  have vanished:iteratedFDeriv ℝ (order s (fun i=>(a i).1)) f.val (location o h r t z)=0:=
    notMem_support.mp (fun mark=>absent (support_iteratedFDeriv_subset _ mark))
  have zero: (perform s (fun i=>(a i).1) f).val (location o h r t z)=0:=by
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa only [vanished,norm_zero,mul_zero] using paid s (fun i=>(a i).1) f (location o h r t z)) (norm_nonneg _)
  change g.val z*coefficient s o h f r t z a=0
  simp only [coefficient,exposed,zero,mul_zero]

end YM.Integration.WilsonSeparatedOriginalSlabActiveWeights
