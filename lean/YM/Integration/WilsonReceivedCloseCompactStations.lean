import YM.Integration.WilsonReceivedCloseGeometricPriorCourse
import YM.Integration.WilsonReceivedCompactCoveredCells
import YM.Integration.WilsonReceivedGeometricCoveredPrior
import YM.Integration.WilsonReceivedGeometricPriorDates
import YM.Integration.WilsonReceivedCloseCoissuedOrdinary

/-! One chronological signed sale on each housed receiving aperture and all previous true vacua. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonReceivedCloseCompactStations
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

open WilsonReceivedGeometricCellReadout RG16.Literal Next.Foundations MeasureTheory XSpace XSpace.Rose OPE.Orbits
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

/-- Original physical housing checked at the occupied lower-date center. -/
structure Housing {n:Lattice.Side} (B:ℕ) (y:Site n) (roots:Fin 3→Site n) where
  cluster : Support n
  contains : y∈cluster
  includes : ∀v,roots v∈cluster
  radius : ℕ
  close : ∀v,separation (roots v) y ≤ radius
  bound : radius ≤ B
  within : cluster ⊆ halo B {y}

structure Station {i:ℕ} (W:Rep G (R.family.side i per)) (domain:Type) (fees:Fares)
    (sourcePower:ℕ) (wallet:ℝ) where
  roots:Fin 3→Site (R.family.side i per)
  colors:domain→((J₀).Mode→ℂ)→Values (Config G (R.family.side i per))
  sale:∀ (fired:domain) (c:(J₀).Mode→ℂ) (y:Site (R.family.side i per)),Housing W.p.B y roots →
    (g (i+1))^sourcePower*(∑s,‖c s‖) ≤ wallet →
    ∃h:Coefficient (R.family.labels.level 0) (R.family.side i per),Paid (N:=N) R W fees y (colors fired c) h

structure Board {i:ℕ} (W:Rep G (R.family.side i per)) (fees:Fares) (pow:ℕ) (wallet:ℝ) where
  domain:Type
  station:Station (N:=N) R W domain fees pow wallet

local notation "income" i:max q:max tgt:max pow:max d:max ε:max w:max => fares (N:=N) (per:=per) (i:=i) R order shelf q tgt pow d ε w

/-- One enrolled receiving post and its complete physical and independently posted readers at each date. -/
def Opened (start:P b mb source) (K:Covered) (singer:MSbar.Heath.Voice G) (axes:Lattice.Order)
    (d q target sourcePower:ℕ) (ε wallet:ℝ):Prop:=
  ∀ i (ib:i ≤ b) (mi:m ≤ i),∃L:P i mi (read i ib),Walk start i mi ib L ∧
    (∀s:(J₀).Mode,(g (i+1))^(d*s.val.card+1) ≤ Poly.toll L.w s) ∧
    ∃T:Station (N:=N) R (Ψ i) (Wallet actors) (income i q target sourcePower d ε wallet) sourcePower wallet,
      T.roots = (homes i L) ∧ T.colors = fun fired c=>WilsonReceivedGeometricCellReadout.values
        R hk D Q π Γ Ψ books mi ahead order shelf seats actors pieces grades (read i ib) L fired singer axes q c (K i ib)

theorem appointed (start:P b mb source) (K:Covered) (singer:MSbar.Heath.Voice G) (axes:Lattice.Order)
    (d q target sourcePower:ℕ) (ε wallet:ℝ)
    (registered:WilsonReceivedCloseGeometricPriorCourse.Served R hk D Q π Γ Ψ books ahead actors pieces grades
      order shelf seats mb source start K singer axes d q target sourcePower ε wallet) :
    Opened R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats mb source start K
      singer axes d q target sourcePower ε wallet := by
  intro i ib mi
  obtain ⟨L,trail,sold,hearing⟩:=registered i ib mi
  refine ⟨L,trail,sold,⟨homes i L,_,?_⟩,rfl,rfl⟩
  intro fired c y H room
  exact hearing fired c y H.cluster H.contains H.includes H.radius H.close H.bound H.within room

include R in
theorem compact {i:ℕ} (live:i ≤ N) (W:Rep G (R.family.side i per)) {Cell:Type} [Fintype Cell]
    [MeasurableSpace Cell] [MeasurableSingletonClass Cell] (test:Test 3) (χ:Points 3→Cell) (measured:Measurable χ)
    {X₀:Cell→Type} (fees:Fares) (pow:ℕ) (wallet:ℝ) (T:∀o,Station (N:=N) R W (X₀ o) fees pow wallet)
    (label:∀o,X₀ o) (c:Cell→(J₀).Mode→ℂ) (y:Cell→Site (R.family.side i per))
    (housed:∀o,WilsonSeparatedOriginalThermometerCells.weight test χ o≠0 → Housing W.p.B (y o) (T o).roots)
    (room:∀o,WilsonSeparatedOriginalThermometerCells.weight test χ o≠0 → (g (i+1))^pow*(∑s,‖c o s‖) ≤ wallet) :
    let keep:=fun o h=>Classical.choose ((T o).sale (label o) (c o) (y o) (housed o h) (room o h))
    (∀o h,Paid (N:=N) R W fees (y o) ((T o).colors (label o) (c o)) (keep o h)) ∧
    WilsonReceivedCompactCoveredCells.Integrated (N:=N) R test χ W
      (fun o=>(T o).colors (label o) (c o)) fees y keep := by
  let keep:=fun o h=>Classical.choose ((T o).sale (label o) (c o) (y o) (housed o h) (room o h))
  have issued (o h):Paid (N:=N) R W fees (y o) ((T o).colors (label o) (c o)) (keep o h):=
    Classical.choose_spec ((T o).sale (label o) (c o) (y o) (housed o h) (room o h))
  exact ⟨issued,WilsonReceivedCompactCoveredCells.original R live test χ measured W _ fees y keep issued⟩

end YM.Integration.WilsonReceivedCloseCompactStations
