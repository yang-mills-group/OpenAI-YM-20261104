import YM.Integration.WilsonReceivedGeometricCoveredPrior
import YM.Integration.WilsonReceivedGeometricPriorDates
import YM.Integration.WilsonReceivedCloseCoissuedOrdinary

/-! One chronological signed sale on each housed receiving aperture and all previous true vacua. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonReceivedCloseGeometricPriorCourse
open Filter Finset Multi Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6

open Extra.Histories MergeProof.Accent Pert.Asymptotics Filter WilsonOriginalReceivedChain
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Extra Source
open FullQLocal FullQLocal.RenderedStep Multi Exterior Comparison.RG02.Cumulants
open OPE.Therm WilsonLimitConstruction RG16.Literal Source Labels Extra.Histories
open scoped BigOperators Classical

variable {G : Gauge} (R : Run G) {m b N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {X : Fin 3 → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : Fin 3 → ℕ)
  (order shelf seats : ℕ) (mb : m ≤ b)
  (source : Wallet actors → Config G (R.family.side (b+1) per) → Poly (Stock.census (Fin 3)))

local notation "read" i:max ib:max => WilsonReceivedCloseHistory.history (N:=N) R actors source i ib
local notation "P" i:max f:max y:max => Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i f y
local notation "g" => regulatorRun R.family N per
local notation "move" i:max => R.family.path.levels.clock.op i per


local notation "J₀" => Stock.census (Fin 3)
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

local notation "homes" i:max L:max => ((L).passport.coarser (move i).ratio).origin

/-- All measured alternatives, independently declared scalar grades, and the complete original
compulsory remainder belong to a single receiving post at each date. -/
def Served (start:P b mb source) (K:Covered) (singer:MSbar.Heath.Voice G) (axes:Lattice.Order)
    (d q target sourcePower:ℕ) (ε wallet:ℝ) : Prop :=
  ∀ i (ib : i ≤ b) (mi : m ≤ i),∃L:P i mi (read i ib),Walk start i mi ib L ∧
    (∀s:(J₀).Mode,(g (i+1))^(d*s.val.card+1) ≤ Poly.toll L.w s) ∧
    ∀ (fired:Wallet actors) (c:(J₀).Mode→ℂ)
      (y:Site (R.family.side i per)) (Z:Support (R.family.side i per)),y∈Z → (∀ v, (homes i L) v∈Z) →
      ∀rad : ℕ,(∀v,separation ((homes i L) v) y ≤ rad) → rad ≤ (Ψ i).p.B → Z ⊆ halo (Ψ i).p.B {y} →
      (g (i+1))^sourcePower*(∑s,‖c s‖) ≤ wallet →
      WilsonReceivedGeometricCoveredPrior.Heard R hk D Q π Γ Ψ books mi ahead order shelf seats actors pieces grades
        (read i ib) L fired singer axes q target sourcePower d ε wallet c y (K i ib)

theorem original (simple:G.Simple) (start:P b mb source) (top:b<N) (K:Covered) (span:ℕ) (H cap:ℝ) (a d q:ℕ) (ε₀:ℝ)
    (heard : WilsonReceivedCloseCoissuedOrdinary.Heard R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats mb
      source start top K span H cap a d q ε₀)
    (named : WilsonReceivedCloseFoldedOrdinary.Match R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats mb
      source start K)
    (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ) (gradeCap:(∑v,grades v) ≤ 14)
    (way:WayStation R.kit) (pass:Pass D Q R.alloy R.kit)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (load:seats ≤ Burn.horizon k+2) {η:ℝ} {T:Campaign R} {W:Campaign.Pillars R T}
    (funded:FundedOriginalProperties.{u} simple η W) (slow:∀j,((R.family.S.block j).val:ℝ) ≤ Real.log (RG16.Lambda R.family.path.levels j))
    (singer:MSbar.Heath.Voice G) (clear:MSbar.Heath.Clear G singer) (axes:Lattice.Order)
    (strip:∀a j:ℕ,j≤a→∀v:ℝ,R.alloy.delay.betaEntry a≤v→Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon j) a)⁻¹^2)≤v)
    (law:VowsR.LawScroll G φ) (enrolled:VowsR.Chamber law R.kit D Q books) (fund:Volume.Fund D R.rolls Q φ books R.alloy.delay)
    (gate:WilsonReportingForestAngularReflection.posted R) (ready:WilsonReportLampForecast.Ready R.family.path.levels)
    (target sourcePower:ℕ) (wallet:ℝ) (surplus:target+1+(sourcePower+(d*3+1)+87) ≤ q)
    (deep:2*(q+1)+8 ≤ order) (aged:q+4 ≤ 3*k+2) {ε:ℝ} (ep:0<ε) (half:ε≤1/2) (accurate:ε*((3:ℝ)^q+2)≤1)
    (timed:WilsonReceivedGeometricPriorDates.Ready R simple funded slow singer clear D strip grades order shelf k gate
      q target (sourcePower+(d*3+1)) wallet ep ready deep aged m) :
    Served R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats mb source start K
      singer axes d q target sourcePower ε wallet := by
  intro i ib mi
  obtain ⟨L,trail,carried,sold,other⟩ := heard i ib mi
  obtain ⟨station,sec,early,late,narrow,fit,force,saved,perSeat⟩ := timed i mi
  obtain ⟨opened,dates⟩ := perSeat seats load
  have paid := dates i le_rfl
  have unit := (eventually_atTop.mp (WilsonJointAxialClock.original R simple)).choose_spec i paid.2.2.1 N per (ib.trans_lt top)
  have retained : charge i mi L ≤ (1/2)*(g (i+1))^q :=
    carried.trans (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one unit.1.le unit.2.1 (by omega)) (by norm_num))
  refine ⟨L,trail,sold,fun fired c y Z yz homes_in rad near radius box coefficients=>?_⟩
  rw [←L.capacity] at opened
  exact WilsonReceivedGeometricCoveredPrior.original R simple (ib.trans_lt top) hk D Q π Γ Ψ course books mi ahead
    order shelf seats actors pieces grades (read i ib) L fired gradeCap way station sec slow ready early late pass hospital
    narrow (L.capacity.le.trans load) q force deep aged ep opened half retained c y Z yz homes_in rad near radius box
    sourcePower d wallet sold coefficients target surplus saved funded singer clear axes strip law enrolled fund gate fit
    accurate dates (K i ib) (named i mi ib L trail)

end YM.Integration.WilsonReceivedCloseGeometricPriorCourse
