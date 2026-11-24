import YM.Integration.WilsonPositionOriginalDressedQResidualSquare
import YM.Integration.WilsonRootedKioskMeasuredCourse
/-! The complete original Q pair and the two genuinely filed one-name
fields on their common Wilson path. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDressedQWithdrawal
open Set Function Filter MeasureTheory Lattice Wilson RG Marker Cells QuadraticLocal
open OPE.Therm QLocalPhysicalPathKernel WilsonPositionOriginalDressedQFailedPath
open Source Labels FVA1 LocalComparison ComparisonDensity.Address
open PhysicalNext.Repeat.Legato MergeProof MergeProof.Accent MergeProof.Replicums
open RG3.Held RG3.Script.Picnic OriginalForcedAddresses ActualOriginalQReaders
open WilsonMacroscopicForwardTransfer WilsonPositionOriginalDressedQCohortSource
open Push.GridApprox WilsonPositionOriginalDressedQLiteralLamp WilsonPositionOriginalDressedQCutSquare
open scoped Topology Classical BigOperators
variable {G:Gauge}(R:Run G){B:MS.Local.Physical.Deck G}{p i n:ℕ}{hn:n  ≤  i+1}{V:Type}
  [DecidableEq V][Fintype V][Nonempty V](Q:MS.Land.Prescription B)
  (D:ActualRunQlocalNativeTuple.Datum R p (i+1) n hn V)(u:V→MS.Rake.Label B)(μ:ℝ)(orders:V→ℕ)
  {T I:Type}(test:T → TestSpace (ActualRunQlocalNativeTuple.orbit D))(simple:G.Simple){N:ℕ}(live:i<N)
local notation "Γ" => (Stock.census V)
local notation "Ψ" => (R.family.path.rep N p i)
local notation "S" => (R.family.path.levels.clock.op i p)

local notation "Y" => (WilsonPositionOriginalDressedQElectedPair.table R Q D u μ orders test simple live)
local notation "q" => (fun t=>letter R Q D u μ orders (test t))
variable {o:V→Site (R.family.side i p)}{P:Rep G (R.family.side i p)}
  {w:V→ℝ}{k r reg hard:ℝ}(L:QuadraticLocal.Lamps T I G P.p o (Stock.census V))
local notation "ℒ" => (WilsonRootedKioskOccupiedSlip.bare L)

def Paid (B₀:ℕ)(A d qPrice maximum low:ℝ):Prop:=
  ∃ r reg:ℝ,r ≤ maximum ∧ reg ≤ low ∧
  ∃ Z:WilsonRootedKioskSealedPost.Return P o Γ w k r reg hard ℒ Y,
  ∀(a b:V),a≠b → ∀s:(Γ).Mode,s.val={a,b} → ∀(t:T)(m:ℕ),
    2*(m*(4*B₀+2)+2*B₀)<separation (o a) (o b) →
    let arm(v:V):=short L B₀ m ((Γ).fire v) t
    let step:=backTo R.family.path N p (Nat.le_succ i)
    ‖(∫U,((q) t a U-step (arm a) U)*((q) t b U-step (arm b) U) ∂scene R.family.path N p (i+1))-
      (∫W,(Z.output.density t W).part s/(P.eval W:ℂ) ∂scene R.family.path N p i)‖ ≤ 
      tailFee (w:=w) (a:=A) (d:=d) m ((Γ).fire a)*(qPrice+bound (w:=w) (d:=d) ((Γ).fire b))+
      (qPrice+bound (w:=w) (d:=d) ((Γ).fire a))*tailFee (w:=w) (a:=A) (d:=d) m ((Γ).fire b)+
      tailFee (w:=w) (a:=A) (d:=d) m s

theorem purchased [Countable I] (href:∀s:Slot u,R.family.ref s.2.size ≤ i+1)
    (coarse:P.eval=(Ψ).eval)(hw:∀v,0<w v){A d M maximum low:ℝ}{B₀:ℕ}(ha:0 ≤ A)
    (cash:WilsonRootedKioskOccupiedSlip.Gross L w B₀ A d)
    (arms:∀ (t:T)(v:V) U,‖(q) t v U‖ ≤ M)
    (sale:WilsonRootedKioskMeasuredCourse.Payout (touch:=o) P w k hard maximum low ℒ Y):
    Paid R Q D u μ orders test simple live L (w:=w) (k:=k) (hard:=hard) B₀ A d M maximum low:=by
  obtain ⟨r,reg,hr,hreg,⟨Z⟩⟩:=sale
  refine ⟨r,reg,hr,hreg,Z,?_⟩
  intro a b ab s roots t m distant
  exact WilsonPositionOriginalDressedQResidualSquare.original R Q D u μ orders test simple live L href coarse Z
    hw ha cash a b ab s roots t m distant M M (arms t a) (arms t b)

end YM.Integration.WilsonPositionOriginalDressedQWithdrawal
