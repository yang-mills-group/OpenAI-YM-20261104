import YM.Integration.WilsonOriginalAlternativeTrialEarlier
import YM.Integration.WilsonOriginalAlternativeTrialThermalRate
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialSettlement
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Planned.GuardedAtom Push.Local Source Labels Extra.Histories Next.Foundations
open scoped Classical BigOperators Topology

open Push.AbsoluteSums

variable {G : Gauge} (R : Run G) {m i b N per k : ℕ}
  (hk : Burn.horizon k+2  ≤  R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ) (hi : m  ≤  i) (cut : i < N)
  (ahead : Mentor.Forecast D R.rolls Q φ books) 
  (grades : Fin 3 → ℕ) (order shelf seats : ℕ)
  (o:Fin 3→Site (R.family.side (b+1) per)) (v:∀j,R.family.label (grades j)) (z:Fin 3→ℂ)
  (ib:i  ≤  b) (upper:b+1  ≤  N)

local notation "actors" => (WilsonOriginalAlternativeFiniteSource.disks (V:=Fin 3))
local notation "pieces" => (WilsonOriginalAlternativeFiniteSource.sectors (V:=Fin 3))
local notation "head_" => WilsonOriginalAlternativeTrialSource.source R grades N per (b+1) o v z
local notation "physical" => WilsonReceivedCloseHistory.history (N:=N) R actors (head_) i ib
variable (P:WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead (WilsonOriginalAlternativeFiniteSource.disks (V:=Fin 3))
  (WilsonOriginalAlternativeFiniteSource.sectors (V:=Fin 3)) grades order shelf seats i hi
  (WilsonReceivedCloseHistory.history (N:=N) R (WilsonOriginalAlternativeFiniteSource.disks (V:=Fin 3))
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
local notation "J_" => Stock.census (Fin 3)

local notation "fire_" => (WilsonOriginalAlternativeFiniteSource.fired (V:=Fin 3))
local notation "active_" j:max => WilsonOriginalAlternativeTrialSource.arm R grades N per (b+1) o v z j
local notation "fed_" j:max => actualTransport R.family (N:=N) (active_ j) (ib.trans (Nat.le_succ b))


local notation "heat_" => R.alloy.B.a.clock.hatBeta (i+1)

open Multi Comparison.RG02.Cumulants WilsonThermometerSolitaryFiledExchange WilsonThermometerSolitaryExchange

local notation "mask_" s:max => WilsonOriginalAlternativeTrialSource.mode R grades N per (b+1) o v z fire_ s
local notation "full_" s:max => actualTransport R.family (N:=N) (mask_ s) (ib.trans (Nat.le_succ b))
local notation "ordinary_" U:max s:max => (word (WilsonThermometerSolitaryFiledExchange.value (gauge).E fire_ U)).part s
local notation "spent_" U:max s:max => (exit (gauge) fire_ U s / ((W_).eval U:ℂ))


open WilsonThermometerMixedCollarSubpower WilsonOriginalOccupiedCorridor WilsonOriginalMicroscopicEntranceReader
open Filter
private theorem census (s:(J_).Mode):s.val.card ≤ 3:=by simpa using s.val.card_le_univ
open WilsonOriginalAlternativeTrialCollateral
private abbrev rates (simple:G.Simple)(a p:ℕ)(C e:ℝ)(cp:0 ≤ C)(ep:0 < e):=
  eventually_atTop.mp (WilsonOriginalAlternativeTrialThermalRate.original R simple 3 (a*3) p C e cp ep)
def onset (simple:G.Simple)(a p:ℕ)(C e:ℝ)(cp:0 ≤ C)(ep:0 < e):ℕ:=
  max (WilsonOriginalAlternativeTrialEarlier.onset R simple 1 (a*3) p C e cp ep) (rates R simple a p C e cp ep).choose

include course upper in
theorem original (way:WayStation R.kit)(ticket:TicketP R.alloy R.kit D Q)(simple:G.Simple)
    (a p:ℕ)(C e:ℝ)(cp:0 ≤ C)(ep:0 < e)(it:0 < i)(age:onset R simple a p C e cp ep ≤ i-1)
    (active:6*seats ≤ R.alloy.B.a.clock.J i)(wide:5 ≤ (W_).p.B)
    (apart:∀v k:Fin 3,v≠k→(W_).p.B^2+1 ≤ separation (homes v) (homes k))
    (u:ℕ)(ui:u ≤ i)(mu:m ≤ u)(old:WilsonOriginalAlternativeTrialEarlier.start R simple 1 (a*3) p C e cp ep ≤ u)
    (span:((i-u+WilsonOriginalAlternativeTrialCollateral.reserve (b+1) i:ℕ):ℝ) ≤ C*(1+Real.log (R.family.path.levels.clock.hatBeta i)))
    (initial:Fin 3→ℝ)(wages:∀j,(initial j)⁻¹ ≤ (R.family.path.levels.clock.hatBeta i)^a)
    (growth:scale (R.family.path.levels.clock.hatBeta (b+1)) ≤ 2*scale (R.family.path.levels.clock.hatBeta i))
    (actual:∀j,(weights j)⁻¹ ≤ (initial j)⁻¹*Real.exp ((9*((b+1-i:ℕ):ℝ)+6)*
      (scale (R.family.path.levels.clock.hatBeta (b+1)))^3))
    (s:(J_).Mode)(W:Config G (R.family.side u per))(clear:flags (Ψ u).p.threshold W=∅):
    ‖actualTransport R.family (N:=N) (fun U=>(full_ s) U-(ordinary_ U s)) ui W‖ ≤
      (3*(e*(Pert.Asymptotics.regulatorRun R.family N per i)^p))*(shards (J_) s).card:=by
  let H:=R.family.path.levels.clock.hatBeta i
  let S:=WilsonOriginalAlternativeTrialCollateral.reserve (b+1) i
  let t:=Poly.toll weights s
  let B:=(W_).p.B
  let ball:=(e*(Pert.Asymptotics.regulatorRun R.family N per i)^p)
  let count:ℝ:=(shards (J_) s).card
  have live:i ≤ N:=(ib.trans (Nat.le_succ b)).trans upper
  have oldAge:= (le_max_left (WilsonOriginalAlternativeTrialEarlier.onset R simple 1 (a*3) p C e cp ep) _).trans age
  have after:= (le_max_right _ (rates R simple a p C e cp ep).choose).trans (age.trans (Nat.sub_le _ _))
  have pos:∀j,0<weights j:=by
    intro j
    exact div_pos (P.salary.positive j) (pow_pos (zero_lt_one.trans_le P.issued.Waffle.cool) _)
  have z0 (x:ℝ):0≤ WilsonThermometerMixedCollarSubpower.scale x:=by unfold WilsonThermometerMixedCollarSubpower.scale;linarith only [le_max_left 0 (Real.log (Real.log x))]
  obtain ⟨restore,gain⟩:=WilsonOriginalAlternativeTrialCollateral.original (n:=3) (a:=a) (z0 _) (z0 _) growth
    (R.family.path.levels.fits.delayed i).le weights initial pos actual wages s (census s)
  have place:(W_).p=R.family.path.levels.budget i:=(course.1.walk i hi live).truep.point
  have area:(Real.log H)^2 ≤ (B:ℝ):=by
    change (Real.log H)^2 ≤ ((W_).p.B:ℝ)
    rw [place]
    exact Nat.le_ceil _
  have length:(S:ℝ) ≤ C*(1+Real.log H):=by
    apply le_trans _ span
    exact_mod_cast (Nat.le_add_left S (i-u))
  have small:=(rates R simple a p C e cp ep).choose_spec i after N per live S B length area
  have considered:=WilsonOriginalAlternativeTrialEarlier.original R hk D Q π Γ Ψ course books hi ahead grades order shelf seats o v z ib upper P way ticket simple 1 (a*3) p C e cp ep it oldAge active wide apart u S ui mu old (by simpa only [pow_one] using span) s W clear
  have whole:=considered.2 gain
  let mexp:=Real.exp (-(2:ℝ)*((B/8:ℕ):ℝ))
  have residue:t⁻¹*mexp ≤ ball:= (mul_le_mul_of_nonneg_right restore (Real.exp_nonneg _)).trans small
  have orderExp:(Real.exp (2*((B/8:ℕ):ℝ)))⁻¹=mexp:=by unfold mexp;rw [←Real.exp_neg];congr 1;ring
  change _ ≤ ball*count+(2*count*(Real.exp (2*((B/8:ℕ):ℝ)))⁻¹/t) at whole
  change _ ≤ (3*ball)*count
  rw [orderExp,div_eq_mul_inv] at whole
  have cp0:0 ≤ count:=Nat.cast_nonneg _
  exact whole.trans (by nlinarith only [mul_le_mul_of_nonneg_left residue cp0])

end YM.Integration.WilsonOriginalAlternativeTrialSettlement
end
