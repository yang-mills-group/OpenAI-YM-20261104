import YM.Integration.WilsonPositionScaleLawGrade
import YM.Integration.WilsonPositionScaleLawClock
import YM.Integration.WilsonPositionScaleLawIteration

/-! Dyadic products of the actual projected physical steps and their inverses.
The one-step engineering-stripped map agrees on the full chosen grade with the
physical Maxwell projection, and is extended by identity on its complement. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawDyadic
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open PhysicalNext.Repeat.Legato RG17 Maxwell XSpace XSpace.Normalize MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionScaleLawHome (sweep)
open WilsonPositionScaleLawNative (exactOp)
open WilsonPositionScaleLawGrade (cut grade half)
open WilsonPositionScaleLawClock (radius)
open WilsonPositionScaleLawKinetic (kinetic)
open WilsonPositionScaleLawQinter (measured)
open WilsonPositionScaleLawIteration (walk)
open scoped Topology Classical Asymptotics
variable {G:Gauge}(Z:WilsonPrescription G){hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
    {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)
set_option quotPrecheck false
local notation "E"=>(Bel R.family.book).Field

def step {d:ℕ}(i:Fin (d+1))(r:ℝ)(n:ℕ):E d→L[ℂ]E d:=
  ContinuousLinearMap.id ℂ (E d)+cut R.family i (exactOp F J Z.store d (radius r n,half)-ContinuousLinearMap.id ℂ (E d))

theorem read {d:ℕ}(i:Fin (d+1))(r:ℝ)(n:ℕ)(v:E d)(pure:grade R.family i v=v):
    step Z F J i r n v=grade R.family i (exactOp F J Z.store d (radius r n,half) v):=by
  change v+grade R.family i ((exactOp F J Z.store d (radius r n,half)) (grade R.family i v)-grade R.family i v)=_
  rw [pure,map_sub,pure];abel

variable (lead:Leading F J){Y:(Bel R.family.book).Hierarchy}(paid:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)
variable {d:ℕ}(i:Fin (d+1))(raw:WilsonPositionScaleLawBranch.Raw J d)
    (observed:(measured Z M ν F J d 2)=o[sweep] (fun z=>kinetic Z F J z.1^2))
    (funded:Coupling G (kinetic Z F J))(r:ℝ)(hr:0<r)

include H lead paid raw observed funded hr in
theorem cost :∃K:ℝ,0≤K ∧ ∀ᶠn:ℕ in atTop,
    ‖step Z F J i r n-ContinuousLinearMap.id ℂ (E d)‖≤K/((n:ℝ)+1):=by
  obtain ⟨A,hA,fee⟩:=WilsonPositionScaleLawGrade.quadratic Z M H ν F J lead paid i half raw observed
  let c:ℝ:=(2*Trace.Over.b0 G*Real.log 2)⁻¹
  let cap:=|c|+1
  have bigger:c<cap:=lt_of_le_of_lt (le_abs_self c) (lt_add_one _)
  have bound:∀ᶠn:ℕ in atTop,((n:ℝ)+1)*kinetic Z F J (radius r n)^2<cap:=
    (tendsto_order.mp (WilsonPositionScaleLawClock.rate funded r hr)).2 _ bigger
  refine ⟨A*cap,mul_nonneg hA (by dsimp [cap];positivity),?_⟩
  filter_upwards [(WilsonPositionScaleLawClock.falls r hr).eventually fee,bound] with n hn hm
  rw [step,add_sub_cancel_left]
  have uq:kinetic Z F J (radius r n)^2≤cap/((n:ℝ)+1):=(le_div_iff₀ (by positivity)).mpr ((mul_comm _ _).trans_le hm.le)
  exact hn.trans ((mul_le_mul_of_nonneg_left uq hA).trans_eq (mul_div_assoc _ _ _).symm)

def controlled {X:Type*}[NormedAddCommGroup X][NormedSpace ℂ X](A:ℕ→X→L[ℂ]X):Prop:=
  ∃N p:ℕ,∀k:ℕ,∀x:X,‖walk A N k x‖≤(((N+k:ℕ):ℝ)+1)^p/((N:ℝ)+1)^p*‖x‖

include H lead paid raw observed funded hr in
theorem original :
    controlled (step Z F J i r) ∧ controlled (fun n=>(step Z F J i r n).inverse) ∧
      ∀ᶠn:ℕ in atTop,(step Z F J i r n).IsInvertible:=by
  obtain ⟨K,hK,paidStep⟩:=cost Z M H ν F J lead paid i raw observed funded r hr
  obtain ⟨L,_hL,inverse⟩:=WilsonPositionScaleLawIteration.backward _ K hK paidStep
  obtain ⟨N,p,_hp,go⟩:=WilsonPositionScaleLawIteration.polynomial _ K paidStep
  obtain ⟨N',p',_hp',back⟩:=WilsonPositionScaleLawIteration.polynomial _ L (inverse.mono fun _ h=>h.2)
  exact ⟨⟨N,p,go⟩,⟨N',p',back⟩,inverse.mono fun _ h=>h.1⟩

end YM.Integration.WilsonPositionScaleLawDyadic
end
