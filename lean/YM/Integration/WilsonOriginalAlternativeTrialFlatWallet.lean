import YM.Integration.WilsonOriginalAlternativeTrialFlatRegistered
import YM.Integration.WilsonOriginalAlternativeTrialAnyWallet
import YM.Integration.WilsonOriginalAlternativeTrialAnyCharge
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialFlatWallet
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Planned.GuardedAtom Push.Local Source Labels Extra.Histories Next.Foundations
open scoped Classical BigOperators Topology

open Push.AbsoluteSums

private abbrev lampIndex {G:Gauge}{n:Side}{V T I:Type}[DecidableEq V]{J:Census V}{o:V→Site n}{b:BudgetPoint}
    (_:Lamps T I G b o J):Type:=I

variable {V : Type} [DecidableEq V] [Fintype V] {G : Gauge} (R : Run G) {m i b N per k : ℕ}
  (hk : Burn.horizon k+2  ≤  R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ) (hi : m  ≤  i) (cut : i < N)
  (ahead : Mentor.Forecast D R.rolls Q φ books) 
  (grades : V → ℕ) (order shelf seats : ℕ)
  (o:V→Site (R.family.side (b+1) per)) (v:∀j,R.family.label (grades j)) (z:V→ℂ)
  (ib:i  ≤  b) (upper:b+1  ≤  N)

local notation "actors" => (WilsonOriginalAlternativeFiniteSource.disks (V:=V))
local notation "pieces" => (WilsonOriginalAlternativeFiniteSource.sectors (V:=V))
local notation "head_" => WilsonOriginalAlternativeTrialSource.source R grades N per (b+1) o v z
local notation "physical" => WilsonReceivedCloseHistory.history (N:=N) R actors (head_) i ib
variable (P:WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead (WilsonOriginalAlternativeFiniteSource.disks (V:=V))
  (WilsonOriginalAlternativeFiniteSource.sectors (V:=V)) grades order shelf seats i hi
  (WilsonReceivedCloseHistory.history (N:=N) R (WilsonOriginalAlternativeFiniteSource.disks (V:=V))
    (WilsonOriginalAlternativeTrialSource.source R grades N per (b+1) o v z) i ib))
local notation "sheet" => R.family.path.levels.clock.op i per
local notation "student" => Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead actors
  P.model order P.voter
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "fig" => Oak.figureReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "oldG" => Coat.gStep (Ψ (i+1)).beta
local notation "lamps" => (rendered student (Ψ i).p oldG)
local notation "gauge" => (Tint.Patrol.report student P.output oldG)
local notation "κ" => LocalComparison.forcedDivisor R.family i
local notation "width" => ((Ψ i).p.supportExponent+1+1)
local notation "modelFee" => Invoice.price (Ψ i).p (fig).mist (order+shelf+1) P.op.count width (fig).limitC G
local notation "oldFee" => Earn.Earnings.hitPrice (fig) G (sheet).ratio.count (Ψ (i+1)).p (Ψ i).p
  (Ω⁻¹*P.cost) (Ω⁻¹*P.rent) (Burn.young (R.alloy.B.a.clock.hatBeta (i+1)) k) oldG
local notation "account" => (Ω^6)⁻¹*(modelFee*((fig).produce (sheet).ratio.count*P.cost)+Ω^P.op.count*oldFee)
local notation "weights" => Stoop.radius P.w (Ω^6)

local notation "homes" => (P.passport.coarser (sheet).ratio).origin
local notation "configuration" => Config G (R.family.side i per)



local notation "W_" => Ψ i
local notation "J_" => Stock.census (V)

local notation "fire_" => (WilsonOriginalAlternativeFiniteSource.fired (V:=V))
local notation "active_" j:max => WilsonOriginalAlternativeTrialSource.arm R grades N per (b+1) o v z j
local notation "fed_" j:max => actualTransport R.family (N:=N) (active_ j) (ib.trans (Nat.le_succ b))


local notation "heat_" => R.alloy.B.a.clock.hatBeta (i+1)

open Multi Comparison.RG02.Cumulants WilsonThermometerSolitaryFiledExchange WilsonThermometerSolitaryExchange

local notation "mask_" s:max => WilsonOriginalAlternativeTrialSource.mode R grades N per (b+1) o v z fire_ s
local notation "full_" s:max => actualTransport R.family (N:=N) (mask_ s) (ib.trans (Nat.le_succ b))
local notation "ordinary_" U:max s:max => (∏j∈(s).val,((gauge).E.log fire_ U).part ((J_).fire j))
local notation "spent_" U:max s:max => ((((gauge).density fire_ U).part s-((W_).eval U:ℂ)*(Poly.pass ((gauge).E.log fire_ U)).part s)/((W_).eval U:ℂ))


open WilsonThermometerMixedCollarSubpower WilsonOriginalOccupiedCorridor WilsonOriginalMicroscopicEntranceReader
open Filter
def degree (I:Type)[Fintype I]:ℕ:=max 1 (Fintype.card I)
private theorem census (s:(J_).Mode):s.val.card ≤ degree V:=by
  have bound:s.val.card ≤ Fintype.card V:=by simpa using s.val.card_le_univ
  exact bound.trans (le_max_right ..)
private abbrev service (simple:G.Simple)(d a p:ℕ)(C e:ℝ)(cp:0 ≤ C)(ep:0 < e):=
  WilsonOriginalAlternativeTrialFlatRegistered.original R simple (J_) (degree V) d a p (lt_of_lt_of_le Nat.zero_lt_one (le_max_left ..)) census C e cp ep
def start (simple:G.Simple)(d a p:ℕ)(C e:ℝ)(cp:0 ≤ C)(ep:0 < e):ℕ:=
  (service (V:=V) R simple d a p C e cp ep).choose
def onset (simple:G.Simple)(d a p:ℕ)(C e:ℝ)(cp:0 ≤ C)(ep:0 < e):ℕ:=
  (eventually_atTop.mp (service (V:=V) R simple d a p C e cp ep).choose_spec).choose

include course upper in
theorem original (way:WayStation R.kit)(ticket:TicketP R.alloy R.kit D Q)(simple:G.Simple)
    (d a p:ℕ)(C e:ℝ)(cp:0 ≤ C)(ep:0 < e)(it:0 < i)(age:onset (V:=V) R simple d a p C e cp ep ≤ i-1)
    (active:6*seats ≤ R.alloy.B.a.clock.J i)(wide:5 ≤ (W_).p.B)
    (apart:∀v k:V,v≠k→(W_).p.B^2+1 ≤ separation (homes v) (homes k))
    (t reserve:ℕ)(ti:t < i)(old:start (V:=V) R simple d a p C e cp ep ≤ t)
    (time:((i-t+reserve:ℕ):ℝ) ≤ C*(1+Real.log (R.family.path.levels.clock.hatBeta i))^d)
    (s:(J_).Mode)(Z:Support (R.family.side t per))(center:Site (R.family.side t per))(home:center∈Z)
    (held:∀j∈s.val,WilsonOriginalOccupiedCorridor.sites R (homes) ti.le j∈Z)
    (u:ℕ)(mu:m ≤ u)(ut:u ≤ t)(fixed:WilsonSingleHardRadius.first R simple ≤ u):
    let H:=R.family.path.levels.clock.hatBeta i
    let gain:=H^a*(Real.exp (((degree V):ℝ)*reserve*(WilsonThermometerMixedCollarSubpower.scale H)^3)*Poly.toll weights s)
    let fee:=Poly.toll (WilsonOriginalOccupiedCorridor.wallet R weights ti.le) s
    let roof:=((shards (J_) s).card:ℝ)+4*(fee+WilsonOriginalFlatOccupiedRate.bill (Ψ t).p Z 1 s.val.card)*
      R.alloy.B.a.clock.hatBeta t*(LocalComparison.forcedDivisor R.family t)
    let bill:=(e*(Pert.Asymptotics.regulatorRun R.family N per i)^p)*roof
    let soft:=((shards (J_) s).card:ℝ)*Real.exp (-(2:ℝ)*(((W_).p.B/8:ℕ):ℝ))/Poly.toll weights s
    gain*‖actualTransport R.family (N:=N) (fun U=>spent_ U s) (ut.trans ti.le) 1‖ ≤ bill ∧
    (1 ≤ gain → ‖actualTransport R.family (N:=N) (fun U=>(full_ s) U-(ordinary_ U s)) (ut.trans ti.le) 1‖ ≤ bill+soft):=by
  have live:i ≤ N:=(ib.trans (Nat.le_succ b)).trans upper
  have rates:=(eventually_atTop.mp (service (V:=V) R simple d a p C e cp ep).choose_spec).choose_spec (i-1) age
  rw [Nat.sub_add_cancel (by omega:1 ≤ i)] at rates
  obtain ⟨regular,wp,forced,rep⟩:=WilsonOriginalAlternativeTrialAnyWallet.original R hk D Q π Γ Ψ course
    books hi (lt_of_le_of_lt ib upper) ahead actors pieces grades order shelf seats (physical) P way 0 (by simpa using active)
  have quiet:(W_).eval=(R.family.path.rep N per i).eval:=(later R π Γ Ψ course hi live).view
  have nz (U:configuration):(W_).eval U≠0:=by
    rw [quiet];exact (Multi.AxisShift.chosen_positive R.makes.wilson live U).ne'
  have same (U:configuration)(s:(J_).Mode):(full_ s) U=((gauge).density fire_ U).part s/((W_).eval U:ℂ):=by
    have reported:=WilsonOriginalAlternativeTrialTravel.field R grades N per b o v z upper ib fire_ s U
    rw [rep fire_,←quiet,Complex.real_smul] at reported
    exact (eq_div_iff (Complex.ofReal_ne_zero.mpr (nz U))).2 ((mul_comm ..).trans reported.symm)
  have hard:(gauge).K.Paid weights (W_).p.B (W_).p.supportExponent (LocalComparison.forcedDivisor R.family i):=by
    simpa only [pow_zero,inv_one,one_mul] using forced
  have base:=WilsonPrecontactSeparatedLamps.lower (gauge).E (show (W_).p.supportExponent ≤ (W_).p.supportExponent+2 by linarith) wp regular
  letI:Countable P.modelIndex:=P.modelCount
  letI:Countable P.outputIndex:=P.outputCount
  letI counted:Countable (lampIndex (lamps)):=Scene.crewC P.model _ _ (Cruise.funded D R.rolls Q R.alloy φ books P.op
    (Oak.era R hk D Q π Γ hi P.op P.lesson) (R.alloy.B.a.S.oneStep i per).exact_size P.model order P.voter P.lesson.entry P.lesson.studied ahead)
  letI : Nonempty (Wallet actors):=⟨fire_⟩
  have price:=rates N per m k t reserve live ti old time way D Q π Γ Ψ course ticket _ _ (homes) (gauge)
    weights wp base hard fire_ s u u mu le_rfl ut fixed Z center home held
  refine ⟨price.1,fun enough=>?_⟩
  have done:=WilsonOriginalAlternativeTrialAnyCharge.original R π Γ Ψ course mu (ut.trans ti.le) live (homes) (gauge) weights wp wide apart regular hard fire_ s 1
  simp_rw [same]
  exact done.trans (add_le_add (price.2 enough) le_rfl)

end YM.Integration.WilsonOriginalAlternativeTrialFlatWallet
end
