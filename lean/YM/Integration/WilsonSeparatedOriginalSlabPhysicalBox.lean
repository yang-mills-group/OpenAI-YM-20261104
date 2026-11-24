import YM.Integration.WilsonSeparatedOriginalSlabPhysicalStencil
import YM.Integration.WilsonPositionSeparatedProfileCenteredSource

/-! The full original centered test has a single common box integral and one finite physical expectation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabPhysicalBox
open Function Set Filter MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Pulse RG05Readout.Records RG05Readout.Flatten MergeProof Accent
open WilsonReportingTerminalPrimaryStencil WilsonSeparatedOriginalSlabPhysicalStencil
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {C:Family G} {I:Type}[Fintype I][DecidableEq I] {N per k:ℕ}

def sheet (C:Family G)(k:ℕ)(r:ℝ)(Ψ:Wave I)(g:Body)(x:Cloud I)(z:E4):ℂ:=g.val z * (rel r Ψ (C.S.a k • z)).val x

def row (C:Family G)(k:ℕ)(r:ℝ)(Ψ:Wave I)(g:Body)(x:Cloud I):ℂ:=∫z in Native.box, sheet C k r Ψ g x z

def weight (s:I→ℕ)(m N:ℕ)(r:ℝ):ℂ:=(∏_i:I,(r:ℂ)⁻¹^4)*mesh (C:=C) s m N

omit [DecidableEq I] in
theorem smooth (Ψ:Wave I)(g:Body)(x:Cloud I)(r:ℝ):Continuous (sheet C k r Ψ g x):=by
  refine (body_smooth g 1).continuous.mul ((lit Ψ 1).continuous.comp ?_)
  apply continuous_pi;intro i
  change Continuous (fun z:E4=>r⁻¹ • (-(C.S.a k • z)) + r⁻¹ • x i)
  fun_prop

theorem returned (made:C.Makes)(s:I→ℕ)(v:(i:I)→C.label (s i)) (r:ℝ)(Ψ:Wave I)(top:k≤N){cap:ℝ}
    (rp:0<r)(enclosed:∀x∈tsupport Ψ.val,∀i,‖x i‖≤cap)(room:r*cap+2*C.S.a k<C.S.radius per)
    (m:ℕ)(g:Body)(U:Config G (C.side N per)):
    constellation s (fun i=>upper (N:=N) (per:=per) (v i)) r Ψ top m g U =
      ∑ x:I→Site (C.side N per), (weight (C:=C) s m N r * row C k r Ψ g (C.S.place ∘ x)) * ∏i,C.O N per (v i) (x i) U:=by
  have far:C.S.a k+r*cap<C.S.radius per:=by linarith only [room,C.S.a_pos k]
  have zero:C.S.place (0:Site (C.side k per))=0:=MergeProof.Ribbons.latzero C k
  have vzero (z:E4):voyager C per k 0 z=C.S.a k • z:=by unfold voyager;rw [zero,zero_add]
  have entry (z:E4) (hz:z∈Native.box):‖voyager C per k 0 z‖≤C.S.a k:=by rw [vzero];exact room_B (C:=C) z hz
  have root:(C.S.toDepth top per).embed 0=0:=(C.S.toDepth _ per).root.map_zero
  have original:=WilsonPositionSeparatedProfileCenteredOrbit.original C s (fun i=>upper (N:=N) (per:=per) (v i)) r Ψ top rp enclosed room far m 0 entry g U
  simp only [root,Lattice.pull_id,vzero] at original
  rw [original];clear original
  let Q(x:I→Site (C.side N per)):=∏i,C.O N per (v i) (x i) U
  let term (x:I→Site (C.side N per))(z:E4):=weight (C:=C) s m N r * sheet C k r Ψ g (C.S.place ∘ x) z * Q x
  have equal (z:E4):g.val z*((∏_i:I,(r:ℂ)⁻¹^4)*multi C m N per s (fun i=>upper (N:=N) (per:=per) (v i)) (rel r Ψ (C.S.a k • z)) U)=∑x,term x z:=by
    rw [WilsonSeparatedOriginalSlabPhysicalStencil.joint made];unfold WilsonSeparatedOriginalSlabPhysicalStencil.sample
    simp only [Finset.mul_sum];apply Finset.sum_congr rfl;intro x _;unfold term weight sheet Q;ring
  simp_rw [equal];rw [integral_finsetSum];swap
  · intro x _;exact ((continuous_const.mul (smooth Ψ g _ r)).mul continuous_const).continuousOn.integrableOn_compact Pert.Cellular.cells_compact
  apply Finset.sum_congr rfl;intro x _;unfold term row Q;rw [integral_mul_const,integral_const_mul]

end YM.Integration.WilsonSeparatedOriginalSlabPhysicalBox
