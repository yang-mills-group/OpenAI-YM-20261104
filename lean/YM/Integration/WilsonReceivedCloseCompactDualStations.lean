import YM.Integration.WilsonReceivedCloseCompactStations
import YM.Integration.WilsonReceivedCompactPlacedStep
import YM.Integration.WilsonReceivedCloseGeometricPlacedCourse

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonReceivedCloseCompactDualStations
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

open WilsonMeasuredCoefficientTransport Trace.Physical
local notation "F₀" => R.family.labels.level 0
local notation "S₀" => R.family.localSection 0
local notation "Rough" => |WilsonFullFaceSignedPower.constants (S₀) (R.family.params) 100 ((2:ℝ)^(order+shelf+2)+4)|
local notation "κ" j:max => LocalComparison.forcedDivisor R.family j

open WilsonReceivedCloseCompactStations WilsonReceivedGeometricCellReadout
local notation "fee" date₀:max q:max tgt:max s:max d:max ε:max money:max =>
  fares (N:=N) (per:=per) (i:=date₀) R order shelf q tgt s d ε money

/-- The registered upper field and its genuine compulsory return through this particular Wilson step. -/
structure Dual (i:ℕ) (prices:Fares) (pow:ℕ) (wallet:ℝ) where
  upper:Board (N:=N) R (Ψ (i+1)) prices pow wallet
  settle:∀ (fired:upper.domain) (c:(J₀).Mode → ℂ) (y:Site (R.family.side (i+1) per))
    (housed:Housing (Ψ (i+1)).p.B y upper.station.roots)
    (money:(g (i+1+1))^pow*(∑s,‖c s‖) ≤ wallet),
    let h:=Classical.choose (upper.station.sale fired c y housed money)
    ∃ (z:Coefficient (F₀) (R.family.side i per)) (u:ℝ),
      WilsonReceivedCompactPlacedStep.Returned (N:=N) R Ψ y h z u prices.regular

def Turned (start:P b mb source) (K:Covered) (singer:MSbar.Heath.Voice G) (axes:Lattice.Order)
    (d q target sourcePower:ℕ) (ε wallet:ℝ):Prop :=
  ∀ i (ib:i+1 ≤ b) (mi:m ≤ i),∃ (L:P (i+1) (mi.trans (Nat.le_succ i)) (read (i+1) ib))
    (lower:P i mi (read i (Nat.le_trans (Nat.le_succ i) ib))),
    Walk start (i+1) (mi.trans (Nat.le_succ i)) ib L ∧
    Walk start i mi (Nat.le_trans (Nat.le_succ i) ib) lower ∧
    (∀s:(J₀).Mode,(g (i+1+1))^(d*s.val.card+1) ≤ Poly.toll L.w s) ∧
    ∃T:Dual (N:=N) R Ψ i (fee (i+1) q target sourcePower d ε wallet) sourcePower wallet,
      ∃loan:Station (N:=N) R (Ψ (i+1)) (Wallet actors) (fee (i+1) q target sourcePower d ε wallet) sourcePower wallet,
        T.upper=⟨_,loan⟩ ∧ loan.roots=(homes (i+1) L) ∧
        loan.colors=fun fired c=>WilsonReceivedGeometricCellReadout.values R hk D Q π Γ Ψ books
          (mi.trans (Nat.le_succ i)) ahead order shelf seats actors pieces grades (read (i+1) ib) L
          fired singer axes q c (K (i+1) ib)

theorem original (start:P b mb source) (K:Covered) (singer:MSbar.Heath.Voice G) (axes:Lattice.Order)
    (d q target sourcePower:ℕ) (ε wallet:ℝ)
    (paired:WilsonReceivedCloseGeometricPlacedCourse.Repaid R hk D Q π Γ Ψ books ahead actors pieces grades
      order shelf seats mb source start K singer axes d q target sourcePower ε wallet) :
    Turned R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats mb source start K
      singer axes d q target sourcePower ε wallet := by
  intro i ib mi
  obtain ⟨L,lower,trail,path,sold,applyAt⟩:=paired i ib mi
  let loan:Station (N:=N) R (Ψ (i+1)) (Wallet actors) (fee (i+1) q target sourcePower d ε wallet) sourcePower wallet :=
    ⟨homes (i+1) L,fun fired c=>WilsonReceivedGeometricCellReadout.values R hk D Q π Γ Ψ books
      (mi.trans (Nat.le_succ i)) ahead order shelf seats actors pieces grades (read (i+1) ib) L
      fired singer axes q c (K (i+1) ib),fun fired c y H money=>Classical.choose
        (applyAt fired c y H.cluster H.contains H.includes H.radius H.close H.bound H.within money)⟩
  let T:Dual (N:=N) R Ψ i (fee (i+1) q target sourcePower d ε wallet) sourcePower wallet :=
    ⟨⟨_,loan⟩,fun fired c y H money=>Classical.choose_spec
        (applyAt fired c y H.cluster H.contains H.includes H.radius H.close H.bound H.within money)⟩
  exact ⟨L,lower,trail,path,sold,T,loan,rfl,rfl,rfl⟩

end YM.Integration.WilsonReceivedCloseCompactDualStations
