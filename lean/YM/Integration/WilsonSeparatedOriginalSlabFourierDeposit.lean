import YM.Integration.WilsonSeparatedOriginalSlabPlaneTest
import YM.Integration.WilsonSeparatedOriginalSlabReplicaStencil

/-! The phase and its exact Jacobian on a genuine differentiated three-slot Wilson stencil. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabFourierDeposit
open Function Finset Set MeasureTheory RG Lattice Wilson Source RG05Readout RG05Readout.Native RG05Readout.Pulse
open RG05Readout.Address RG05Readout.Flatten WilsonSeparatedOriginalSlabReplicaStencil WilsonSeparatedOriginalSlabCenterPhase
open WilsonSeparatedOriginalSlabPlaneTest WilsonSeparatedOriginalSlabCenterBill
open private coefficient exposed location from YM.Integration.WilsonSeparatedOriginalReplicaRegularity
open scoped BigOperators Classical Topology ContDiff
local notation "I"=>Fin 3
variable {G:Gauge}{C:Family G}{b N per:ℕ}(s:I→ℕ)(o:I→Site (C.side b per))(h:b≤N)
local notation "A"=>C.S.toDepth h per
local notation "Letters"=>(i:I)→Mark C (s i)

private def chartTest (g:Body):C(Axis→ℝ,ℂ):=
  ⟨fun z=>g.val (WithLp.toLp 2 z), (body_smooth g 1).continuous.comp (PiLp.continuous_toLp 2 _)⟩

def price (v:I→Axis→ℝ)(t:I→Site (A).count)(a:Letters):ℂ:=
  (∏i,ratioX A (s i))*((↑(A).count.val:ℂ)⁻¹)^pegs s (fun i=>(a i).1) Finset.univ.toList*
    (perform s (fun i=>(a i).1) (packet v 1)).val 0 *
      (∏i,mode (v i) ((C.S.a b)⁻¹ • C.S.place (o i)))*(∏i,mode (v i) (placeR A (t i)))

theorem actual (v:I→Axis→ℝ)(r:ℝ)(hr:0<r)(t:I→Site (A).count)(a:Letters)(z:E4):
    atSite s o h r t z a (packet v (r/C.S.a b))=price s o h v t a*center v z:=by
  have char:(packet v (r/C.S.a b)).val (location o h r t z)=
      (∏i,mode (v i) ((C.S.a b)⁻¹ • C.S.place (o i)))*(∏i,mode (v i) (placeR A (t i)))*center v z:=
    WilsonSeparatedOriginalSlabCenterPhase.original o h v r hr t z
  change coefficient s o h _ r t z a=_
  rw [coefficient,exposed]
  let deg:=pegs s (fun i=>(a i).1) Finset.univ.toList
  let jac:ℂ:=((r⁻¹*C.S.a b)*(↑(A).count.val:ℝ)⁻¹:ℝ)
  refine (congrArg (fun z:ℂ=>(∏i,ratioX A (s i))*(jac^deg*z))
    (WilsonSeparatedOriginalSlabPlaneTest.derivative s (fun i=>(a i).1) v (r/C.S.a b) (location o h r t z))).trans ?_
  dsimp only [jac,deg]
  rw [char]
  have qty:(((r⁻¹*C.S.a b)*(↑(A).count.val:ℝ)⁻¹:ℝ):ℂ)*((r/C.S.a b:ℝ):ℂ)=(↑(A).count.val:ℂ)⁻¹:=by
    push_cast; field_simp [hr.ne', (C.S.a_pos b).ne']
  let d:=pegs s (fun i=>(a i).1) Finset.univ.toList
  have powered:=congrArg (fun x:ℂ=>x^d) qty
  change (_*_)^d=_ at powered
  rw [mul_pow] at powered
  unfold price
  rw [←powered]
  ring

theorem original (v:I→Axis→ℝ)(r:ℝ)(hr:0<r)(t:I→Site (A).count)(a:Letters)(g:Body):
    weight s o h r t a g (packet v (r/C.S.a b))=price s o h v t a * invoice v (chartTest g):=by
  change (∫z in Native.box,g.val z*atSite s o h r t z a (packet v (r/C.S.a b)))=_
  simp_rw [actual s o h v r hr t a,mul_left_comm (g.val _) (price s o h v t a)]
  exact integral_const_mul ..

end YM.Integration.WilsonSeparatedOriginalSlabFourierDeposit
