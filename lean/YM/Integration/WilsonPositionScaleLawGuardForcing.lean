import YM.Integration.WilsonPositionScaleLawGuardBlock
import YM.Integration.WilsonPositionScaleLawGuardLog

/-! On the real kinetic clock the entire nonhomogeneous error acting on an original field is smaller than every logarithmic power. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardForcing
open Function Filter Set Spec Table Extraction Climb PhysMS Trace.Pilot Maxwell Maxwell.Free XSpace XSpace.Normalize
open OPE OPE.Orbits PhysicalNext.Repeat.Legato MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionScaleLawHome (Ratio sweep)
open WilsonPositionScaleLawDressedTransport (dressed)
open WilsonPositionScaleLawWholeHome (physical)
open WilsonPositionScaleLawGuardOrbit (size sizePos total)
open WilsonPositionScaleLawKinetic (kinetic)
open WilsonPositionScaleLawGuardPhysical (expected)
open WilsonPositionScaleLawClock (radius)
open WilsonPositionScaleLawWholeGrowth (weight)
open scoped Topology Classical Asymptotics

theorem shift (m n:ℕ):weight m (n+1)≤2^m*weight m n:=by
  change ((↑(n+1):ℝ)+1)^m≤2^m*((n:ℝ)+1)^m
  rw [←mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  rw [Nat.cast_add_one];linarith [Nat.cast_nonneg (α:=ℝ) n]

variable {G:Gauge}{g:ℝ→ℝ}
theorem clock (funded:Coupling G g)(r:ℝ)(hr:0<r)(k:ℕ):
    ∃B:ℝ,0≤B ∧ ∀ᶠn:ℕ in atTop,weight k n*|g (radius r n)|^(2*k)≤B:=by
  let c:ℝ:=(2*Trace.Over.b0 G*Real.log 2)⁻¹
  let a:=|c|+1
  have ha:0≤a:=by dsimp only [a];positivity
  have cap:∀ᶠn:ℕ in atTop,((n:ℝ)+1)*g (radius r n)^2<a:=(tendsto_order.mp (WilsonPositionScaleLawClock.rate funded r hr)).2 _ (lt_of_le_of_lt (le_abs_self _) (lt_add_one _))
  refine ⟨a^k,pow_nonneg ha k,?_⟩;filter_upwards [cap] with n hn
  change ((n:ℝ)+1)^k*|g (radius r n)|^(2*k)≤_
  rw [pow_mul,sq_abs,←mul_pow]
  exact pow_le_pow_left₀ (by positivity) hn.le k

variable (Z:WilsonPrescription G){hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
    {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)
set_option quotPrecheck false
local notation "gθ"=>kinetic Z F J
variable (d:ℕ)(funded:Coupling G (kinetic Z F J))(law:∀q,WilsonPositionScaleLawGuardLittle.scale F J Z M ν d q)(r:ℝ)(hr:0<r)
def amount (q n:ℕ)(t:Ratio):ℝ:=‖dressed Z F J d (radius r n) t-expected F J Z M ν d q (radius r n) t‖

include H funded law hr in
theorem original (m:ℕ):∃q N:ℕ,∀O:S.Field d,∃C:ℝ,0≤C ∧ ∀n,N≤n→∀t:Ratio,
    weight m (n+1)*amount Z M ν F J d r q n t*‖physical F J Z d (t.val*radius r n) O‖≤C:=by
  let X:=(Bel R.family.book).Field d
  letI :NormedAddCommGroup (X→L[ℂ]X):=ContinuousLinearMap.toNormedAddCommGroup
  obtain ⟨K,p,growth⟩:=WilsonPositionScaleLawGuardLog.dyadic Z M H ν F J d funded (law 2) r hr
  obtain ⟨A,hA,times⟩:=WilsonPositionScaleLawGuardLog.budgets Z M H ν F J d funded (law 2) r hr
  let k:=m+p
  let q:=2*k
  obtain ⟨B,hB,beta⟩:=clock funded r hr k
  have offer:=WilsonPositionScaleLawGuardGrowth.allRatios (Asymptotics.isLittleO_iff.mp (law q) (c:=1) one_pos)
  have old:∀ᶠn:ℕ in atTop,∀t:Ratio,amount Z M ν F J d r q n t≤|gθ (radius r n)|^q:=by
    filter_upwards [(WilsonPositionScaleLawClock.falls r hr).eventually offer] with n bill t
    simpa only [amount,one_mul,Real.norm_eq_abs,abs_pow] using bill t
  obtain ⟨N,all⟩:=eventually_atTop.mp (beta.and (old.and times))
  refine ⟨q,max K N,?_⟩;intro O
  let v:=size R.family (physical F J Z d (radius r K) O)
  have hv:0≤v:=sizePos R.family _
  let b0:=(1+A)*v
  have hb:0≤b0:=mul_nonneg (by linarith) hv
  refine ⟨(2^m*b0)*B,mul_nonneg (mul_nonneg (by positivity) hb) hB,?_⟩
  intro n hn t
  obtain ⟨β,marginal,income⟩:=all n ((le_max_right K N).trans hn)
  have cost:1+A/((n:ℝ)+1)≤1+A:=add_le_add (le_refl 1) (div_le_self hA (by linarith [Nat.cast_nonneg (α:=ℝ) n]))
  have head:=growth n ((le_max_left K N).trans hn) O
  have face:‖physical F J Z d (t.val*radius r n) O‖≤b0*weight p n:=calc
    _≤ size R.family _:=total R.family _
    _≤_:=income t O
    _≤(1+A)*(weight p n*v):=mul_le_mul cost head (sizePos R.family _) (by linarith)
    _=_:=by dsimp only [b0];ring
  have hm:0≤weight m n:=zero_le_one.trans (WilsonPositionScaleLawWholeGrowth.positive ..)
  have combined:weight k n=weight m n*weight p n:=pow_add _ _ _
  calc
    _≤(2^m*weight m n)*|gθ (radius r n)|^q*(b0*weight p n):=by
      apply mul_le_mul _ face (norm_nonneg _) (mul_nonneg (mul_nonneg (by positivity) hm) (pow_nonneg (abs_nonneg _) _))
      exact mul_le_mul (shift m n) (marginal t) (norm_nonneg _) (mul_nonneg (by positivity) hm)
    _=(2^m*b0)*(weight k n*|gθ (radius r n)|^q):=by rw [combined];ring
    _≤_:=mul_le_mul_of_nonneg_left β (mul_nonneg (by positivity) hb)

end YM.Integration.WilsonPositionScaleLawGuardForcing
