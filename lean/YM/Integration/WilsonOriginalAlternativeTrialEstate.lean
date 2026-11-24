import YM.Integration.WilsonOriginalAlternativeTrialTravel
import YM.Integration.WilsonOriginalAlternativeTrialRegular
import YM.Integration.WilsonThermometerReceivedOccupiedWallet
import YM.Integration.WilsonMeasuredReturnedHardField

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialEstate
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

private theorem balance {D:ℂ} (hd:D≠0) (Y M b:ℂ):Y/D-b-(Y-D*M)/D=M-b:=by
  field_simp
  ring

include course upper in
theorem original (way:WayStation R.kit) (q:ℕ)(active:q+6*seats ≤ R.alloy.B.a.clock.J i)
    (wide:5 ≤ (W_).p.B)
    (apart:∀v k:Fin 3,v≠k→(W_).p.B^2+1 ≤  separation (homes v) (homes k)):
    (gauge).E.Paid weights (W_).p.B ((W_).p.supportExponent+2) 1 ∧
    (∀j,0<weights j) ∧
    (gauge).K.Paid weights (W_).p.B (W_).p.supportExponent ((heat_^q)⁻¹*LocalComparison.forcedDivisor R.family i) ∧
    (∀U s,(full_ s) U= ((gauge).density fire_ U).part s/((W_).eval U:ℂ)) ∧
    ∀s:(J_).Mode,∀ (u:ℕ) (ui:u ≤ i) (F:Config G (R.family.side u per)),
      ‖actualTransport R.family (N:=N) (fun U=>(full_ s) U-(ordinary_ U s)-(spent_ U s)) ui F‖  ≤ 
        2*((shards (J_) s).card:ℝ)*(Real.exp (2*((W_).p.B/8:ℕ)))⁻¹/Poly.toll weights s:=by
  have live:i<N:=lt_of_le_of_lt ib upper
  obtain ⟨regular,wp,forced,rep⟩:=WilsonThermometerReceivedOccupiedWallet.original R hk D Q π Γ Ψ
    course books hi live ahead actors pieces grades order shelf seats (physical) P way q active
  have quiet:(W_).eval=(R.family.path.rep N per i).eval:=(later R π Γ Ψ course hi live.le).view
  have pos (U:configuration):0<(W_).eval U:=by
    rw [quiet]; exact Multi.AxisShift.chosen_positive R.makes.wilson live.le U
  have same (U:configuration)(s:(J_).Mode):(full_ s) U= ((gauge).density fire_ U).part s/((W_).eval U:ℂ):=by
    have reported:=WilsonOriginalAlternativeTrialTravel.field R grades N per b o v z upper ib fire_ s U
    rw [rep fire_,←quiet,Complex.real_smul] at reported
    exact (eq_div_iff (Complex.ofReal_ne_zero.mpr (pos U).ne')).2 ((mul_comm ..).trans reported.symm)
  refine ⟨regular,wp,forced,same,?_⟩
  intro s u ui F
  apply actualTransport_norm_le R.family R.makes live.le _ ui
  intro U
  have earned:=WilsonOriginalAlternativeTrialRegular.original (gauge) weights wp wide apart regular forced fire_ s U (pos U).ne'
  have balance:(full_ s) U-(ordinary_ U s)-(spent_ U s)=
      (Poly.pass ((gauge).E.log fire_ U)).part s-(ordinary_ U s):=by
    rw [same]
    exact balance (Complex.ofReal_ne_zero.mpr (pos U).ne') _ _ _
  rw [balance]
  exact (le_div_iff₀ (Poly.worth wp s)).2 ((mul_comm ..).le.trans earned)

end YM.Integration.WilsonOriginalAlternativeTrialEstate
end
