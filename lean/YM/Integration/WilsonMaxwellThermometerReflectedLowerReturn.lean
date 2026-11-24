import YM.Integration.WilsonMaxwellThermometerReflectedOlder
import YM.Integration.WilsonMaxwellThermometerReflectedTangent

/-! At the common independent inversions the actual occupied lower
field in a signed reflected fit has vanishing finite Rose ground payment.
The signed original first-incidence remainder is shown explicitly. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerReflectedLowerReturn
open Filter Function Finset MeasureTheory Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Maxwell
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Shard WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open Source Source.Drops Labels XSpace XSpace.Normalize XSpace.Cirrus XSpace.Rose XSpace.Structure1
open XSpace.Photo XSpace.Tornado XSpace.Retirement Table.Pairing
open WilsonMaxwellThermometerLowerPointGram (occupied)
open WilsonMaxwellThermometerLowerGramPrice (token reassemble)
open WilsonMaxwellThermometerIndependentReflection (panel)
open WilsonMaxwellThermometerReflectedOlder (connected)
open WilsonMaxwellThermometerReflectedFirstPrice (filed)
open WilsonMaxwellThermometerReflectedIncidence (Gram Pair mass site)
open WilsonMaxwellThermometerFiniteTangent (credit)
open WilsonMaxwellThermometerCommonTangent (Equivariant)
open WilsonMaxwellThermometerOriginal (lower)
open WilsonMaxwellThermometerReflectedTangent (raised)
open scoped Classical BigOperators Topology
variable {G:Gauge}{D k u e l d:ℕ}(R:Run G)(h4:4<l)(h6:6<d)
theorem original (U:XSpace.Run){stage:ℕ}(B:WilsonPositionProgramReporterBand.Band R U stage)
    (a:Axis)(x:E4)(hx:0<x a)(W:Initialize G){V:Normalize.Store G}(K:Pick V)(b:Sec G 6)
    (P Q:Module.End ℂ (Sec G 4))(hP:Equivariant P)(hQ:Equivariant Q)
    (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (big:0<D)(rails:Rails 0 k u e)(he:1 ≤ e)(cap:capP (panel (G:=G) h4 h6) ≤ k):
    let π₀:=panel (G:=G) h4 h6
    ∃β:Bulb (site x) a,∃φ:Wilt π₀,∃floor:ℕ,
      WilsonPositionProgramReflectedRead.reading π₀ a φ=mass a x β ∧
      (∫w:Pair,WilsonPositionProgramReflectedRead.reading π₀ a φ w)=1 ∧
      ∀q:ℕ,∀A δ:ℝ,0≤A → 0<δ → ∀ᶠ t:ℕ in atTop,let m:=B.reporter+t;let M:=U.step (B.index t)
      ∀v₀:ℕ,floor ≤ v₀ → B.lower t ≤ v₀ → v₀ ≤ m → ∀N:ℕ,m ≤ N → ∀c∈M.Box,
      let y:=connected R h4 h6 a b big φ m v₀ N k-filed a x W V β b M c
      let F:=reassemble a x (Gram a x W V β M c)
      let ground:=fun z:occupied G a x=>credit W K M (raised a x z) (P (lower G)) (Q (lower G))
      (∀z:occupied G a x,‖y-F z‖ ≤ A*(1+(B.index t:ℝ))^q → ‖ground z‖<δ) ∧
      ∃z:occupied G a x,(∀z',‖y-F z‖ ≤ ‖y-F z'‖) ∧ ‖ground z‖<δ:=by
  intro π₀
  obtain ⟨β,C,J,hC,hJ,first⟩:=WilsonMaxwellThermometerReflectedFirstPrice.original a x W V hx b
  obtain ⟨E,hE,wfile⟩:=WilsonMaxwellThermometerReflectedFirstPrice.bounded a x W V β b
  obtain ⟨φ,w,shape,read,int⟩:=WilsonPositionProgramReflectedRead.original π₀ a x β 1
  obtain ⟨floor,H,hH,p,fee⟩:=WilsonMaxwellThermometerReflectedOlder.original R h4 h6 a b U B simple
    v funded big rails he cap φ w shape
  obtain ⟨L,hL,ground⟩:=WilsonMaxwellThermometerReflectedTangent.ground a x W K simple P Q hP hQ
  refine ⟨β,φ,floor,read,int,?_⟩
  intro q A δ non pos
  let r:=p+q
  let T:=L*C*(H+J+(A+H+E))
  have data:Tendsto (fun t:ℕ=>T*((U.step (B.index t)).spacing*(1+(B.index t:ℝ))^r)) atTop (𝓝 0):=by
    simpa only [Function.comp_apply,mul_zero] using ((WilsonMaxwellThermometerReflectedTangent.decay U r).comp B.cofinal).const_mul T
  have steps:Tendsto (fun t=>U.step (B.index t)) atTop Front:=
    (goesFront (Expense.Stretched.runs U)).comp B.cofinal
  filter_upwards [data.eventually (gt_mem_nhds pos),fee,steps.eventually wfile,steps.eventually first,
    steps.eventually ground] with t small paid pub obs out
  intro m M v₀ base start vm N upper c hc y F net
  let h:=1+(B.index t:ℝ)
  have h₁:1≤h:=by dsimp [h];linarith [Nat.cast_nonneg (α:=ℝ) (B.index t)]
  have hpow:1≤h^r:=one_le_pow₀ h₁
  have pprice:h^p≤h^r:=pow_le_pow_right₀ h₁ (Nat.le_add_right ..)
  have qprice:h^q≤h^r:=pow_le_pow_right₀ h₁ (Nat.le_add_left ..)
  have ph:0≤H*h^p:=mul_nonneg hH (pow_nonneg (zero_le_one.trans h₁) _)
  have cost:‖connected R h4 h6 a b big φ m v₀ N k‖≤H*h^p:=
    (pi_norm_le_iff_of_nonneg ph).2 (paid v₀ base start vm N upper)
  have charges (z:occupied G a x)(hw:‖y-F z‖≤(A+H+E)*h^r):‖net z‖<δ:=by
    have d:=obs c hc z (connected R h4 h6 a b big φ m v₀ N k) ‖y-F z‖ le_rfl
    have inv:‖token a x z‖≤C*((H+J+(A+H+E))*h^r):=by
      apply d.trans
      apply mul_le_mul_of_nonneg_left _ hC.le
      rw [add_mul,add_mul]
      apply add_le_add _ hw
      exact add_le_add (cost.trans (mul_le_mul_of_nonneg_left pprice hH))
        (le_mul_of_one_le_right hJ hpow)
    have slip:=out z
    change ‖net z‖≤L*M.spacing*‖token a x z‖ at slip
    apply lt_of_le_of_lt (slip.trans (mul_le_mul_of_nonneg_left inv (mul_nonneg hL M.positive.le)))
    calc
      _ = T*(M.spacing*h^r):=by dsimp [T];ring
      _ < δ:=small
  constructor
  · intro z err
    apply charges z (err.trans _)
    exact mul_le_mul (by linarith only [hH,hE]) qprice
      (pow_nonneg (zero_le_one.trans h₁) _) (by linarith only [non,hH,hE])
  · obtain ⟨z,solves⟩:=WilsonMaxwellThermometerReflectedCalibration.solved a x (Gram a x W V β M c) y
    refine ⟨z,solves,charges z ?_⟩
    have h:=solves 0
    change ‖y-F z‖≤‖y-(WilsonMaxwellThermometerReflectedCalibration.detector a x (Gram a x W V β M c)) 0‖ at h
    rw [map_zero,sub_zero] at h
    apply h.trans (((norm_sub_le ..).trans (add_le_add cost (pub c hc))).trans _)
    rw [add_mul,add_mul]
    linarith only [mul_le_mul_of_nonneg_left pprice hH,
      le_mul_of_one_le_right hE hpow,mul_nonneg non (zero_le_one.trans hpow)]
end YM.Integration.WilsonMaxwellThermometerReflectedLowerReturn
