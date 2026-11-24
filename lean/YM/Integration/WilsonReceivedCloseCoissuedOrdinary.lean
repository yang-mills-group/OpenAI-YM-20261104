import YM.Integration.WilsonReceivedChargedOrdinaryReturn
import YM.Integration.WilsonReceivedCloseFoldedOrdinary
import YM.Integration.WilsonReceivedClosePositionedReturn
/-! At the actual post with the small prior fee, all ordinary proper and full faces
are heard against the independently declared covered history, before either cutoff. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseCoissuedOrdinary
open Filter Finset Multi Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6

open Extra.Histories MergeProof.Accent Pert.Asymptotics Filter WilsonOriginalReceivedChain
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Extra Source
open FullQLocal FullQLocal.RenderedStep Multi Exterior Comparison.RG02.Cumulants
open scoped BigOperators

variable {G : Gauge} (R : Run G) {m b N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V] {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ) (mb : m ≤ b)
  (source : Wallet actors → Config G (R.family.side (b+1) per) → Poly (Stock.census V))

local notation "read" i:max ib:max => WilsonReceivedCloseHistory.history (N:=N) R actors source i ib
local notation "P" i:max f:max y:max => Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i f y
local notation "g" => regulatorRun R.family N per
local notation "move" i:max => R.family.path.levels.clock.op i per


local notation "J₀" => Stock.census V
local notation "Pupil" i:max mi:max L:max =>
  Oak.student (n:=per) (i:=i) R hk D Q π Γ books mi (L).op (L).lesson ahead actors (L).model order (L).voter
local notation "teacher" i:max mi:max L:max x:max => Air.craft (Pupil i mi L)
  (fun s=>((Pupil i mi L) s).paint x) grades (π i) (AllOrder.Floe.Step.tape (Burn.horizon k+2))
local notation "bank" i:max L:max x:max => Air.craft (L).model (fun s=>((L).model s).paint x)
  grades (π (i+1)) (AllOrder.Floe.Step.tape (Burn.horizon k+2))
local notation "Covered" => ∀i:ℕ,i ≤ b → Wallet actors → Stationary.Link G (R.family.side i per) → ℕ → Poly J₀
local notation "Walk" start:max i:max mi:max ib:max L:max =>
  WilsonReceivedCloseHistory.Trail (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
    mb source start i mi (read i ib) L


local notation "charge" i:max mi:max L:max =>
  (8*(Oak.expenseReal (i:=i) R hk D Q π Γ books mi (L).op (L).lesson ahead order shelf)^(L).op.count)*(L).rent
local notation "p" a:max d:max q:max => q+1+(d*a+1)+a

def Heard (start:P b mb source) (top:b<N) (K:Covered) (span:ℕ) (H cap:ℝ) (a d q:ℕ) (ε:ℝ) : Prop :=
  ∀i (ib:i ≤ b)(mi:m ≤ i),∃ L:P i mi (read i ib), Walk start i mi ib L ∧
    (charge i mi L) ≤ (1/2)*(g (i+1))^(p a d q) ∧
    (∀s:(J₀).Mode,(g (i+1))^(d*s.val.card+1) ≤ Poly.toll L.w s) ∧
    ∀ (x:Wallet actors) (F:Forest (move i).ratio) (tag:(move i).Choices)
      (A:Stationary.Link G (R.family.side i per)) (z:ℝ),
      let B:=R.family.path.levels.budget i
      let angle:=Stationary.arm G (R.family.side i per) 1 A
      |z| ≤ |H| *(Real.log (R.family.path.levels.clock.hatBeta i))^span*((B.B:ℝ)^2*B.threshold)/(g (i+1)) →
      (∀e,‖Exterior.collect G angle e‖ ≤ cap*|z|) →
      let U:=Integral.sample (g (i+1)) angle
      flags (Ψ i).p.threshold U=∅ →
      let Y:=(((Ψ i).eval U:ℂ)⁻¹) • LocalComparison.actualPush R.family N per i ((read i ib) x) U
      let W:=Bulk.Fk ((RunFormalChain.fromRun R).step N i per (ib.trans_lt top)) F tag (bank i L x) angle order
      let folded:=WilsonCoveredOrdinaryPolynomial.evaluated order (K i ib x A) (g (i+1):ℂ)
      ∀s:(J₀).Mode,s.val.card ≤ a →
        ‖Y.part s-(Order.value (g (i+1):ℂ) (Order.ratio W)).part s‖ ≤ (ε/2)*(g (i+1))^q ∧
        ‖Y.part s-folded s‖ ≤ ε*(g (i+1))^q

variable (simple:G.Simple)
  (protection:∀a k:ℕ,k≤a → ∀B:ℝ,R.alloy.delay.betaEntry a ≤ B →
      Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) a)⁻¹^2) ≤ B)
  (span a d q:ℕ) (H cap ε:ℝ) (hc:0 ≤ cap) (ep:0<ε)
  (deep:2*((p a d q)+1)+8 ≤ order) (aged:(p a d q)+4 ≤ 3*k+2)
local notation "program" => WilsonReceivedChargedOrdinaryReturn.original R simple D φ grades protection
  order shelf k seats span a (d*a+1) q deep aged H cap hc ep

def Ready (m₀:ℕ) : Prop :=
  (eventually_atTop.mp program).choose ≤ m₀ ∧
    (eventually_atTop.mp (WilsonReceivedTaylorWindow.potential R simple span H)).choose ≤ m₀

theorem scheduled : ∀ᶠ m₀:ℕ in atTop, Ready R D (φ:=φ) grades order shelf seats simple protection
    span a d q H cap ε hc ep deep aged m₀ := by
  filter_upwards [eventually_ge_atTop (eventually_atTop.mp program).choose,
    eventually_ge_atTop (eventually_atTop.mp (WilsonReceivedTaylorWindow.potential R simple span H)).choose]
    with m₀ h r
  exact ⟨h,r⟩

theorem original (start:P b mb source) (top:b<N) (K:Covered)
    (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (law:VowsR.LawScroll G φ) (ch:VowsR.Chamber law R.kit D Q books)
    (volume:Volume.Fund D R.rolls Q φ books R.alloy.delay) (fit:k≤R.alloy.B.a.clock.J m)
    (dates:Ready R D (φ:=φ) grades order shelf seats simple protection span a d q H cap ε hc ep deep aged m)
    (income:∀i (ib:i ≤ b)(mi:m ≤ i),∃ L:P i mi (read i ib), Walk start i mi ib L ∧
      (charge i mi L) ≤ (1/2)*(g (i+1))^(p a d q) ∧
      ∀s:(J₀).Mode,(g (i+1))^(d*s.val.card+1) ≤ Poly.toll L.w s)
    (named:WilsonReceivedCloseFoldedOrdinary.Match R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
      mb source start K) :
    Heard R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats mb source start top K span H cap a d q ε := by
  intro i ib mi
  obtain ⟨L,walk,rent,wages⟩:=income i ib mi
  refine ⟨L,walk,rent,wages,?_⟩
  intro x forest tag A z B angle hz inside U healthy Y W folded s live
  let t:=g (i+1)
  have ci:=ib.trans_lt top
  have gp:0<t:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson ci))
  have cold:=(eventually_atTop.mp (WilsonReceivedTaylorWindow.potential R simple span H)).choose_spec i (dates.2.trans mi) N per ci z hz
  have wage:t^(d*a+1)≤Poly.toll L.w s :=
    (pow_le_pow_of_le_one gp.le cold.1 (Nat.add_le_add_right (Nat.mul_le_mul_left d live) 1)).trans (wages s)
  have receipt:=(eventually_atTop.mp program).choose_spec i (dates.1.trans mi) hk (fit.trans (R.alloy.B.a.fits.mono mi)) Q π Γ Ψ course books law ch volume mi ci ahead
    actors pieces (read i ib) L x A rent z hz inside healthy forest tag s live wage
  have value:=WilsonReceivedClosePositionedReturn.ordinary (named i mi ib L walk x A) (g (i+1):ℂ) s
  exact ⟨receipt.1,(le_of_eq (congrArg (fun a:ℂ=>‖Y.part s-a‖) value)).trans receipt.2⟩

end YM.Integration.WilsonReceivedCloseCoissuedOrdinary
