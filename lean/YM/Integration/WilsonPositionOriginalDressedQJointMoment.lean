import YM.Integration.WilsonPositionOriginalDressedQElectedPair
import YM.Integration.WilsonPositionOriginalDressedQPosterior
import YM.Integration.WilsonPositionOriginalDressedQPublishedField

/-! The complete original Q pair and the two genuinely filed one-name
fields on their common Wilson path. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDressedQJointMoment
open Set Function Filter MeasureTheory Lattice Wilson RG Marker Cells QuadraticLocal
open OPE.Therm QLocalPhysicalPathKernel WilsonPositionOriginalDressedQFailedPath
open Source Labels FVA1 LocalComparison ComparisonDensity.Address
open PhysicalNext.Repeat.Legato MergeProof MergeProof.Accent MergeProof.Replicums
open RG3.Held RG3.Script.Picnic OriginalForcedAddresses ActualOriginalQReaders
open WilsonMacroscopicForwardTransfer WilsonPositionOriginalDressedQCohortSource
open scoped Topology Classical BigOperators
variable {G:Gauge}(R:Run G){B:MS.Local.Physical.Deck G}{p i n:ℕ}{hn:n ≤ i+1}{V:Type}
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

theorem original [Countable I] (href:∀s:Slot u,R.family.ref s.2.size ≤ i+1)
    (coarse:P.eval=(Ψ).eval)
    (Z:WilsonRootedKioskSealedPost.Return P o Γ w k r reg hard ℒ Y)
    (hw:∀v,0<w v){A d:ℝ}{B₀:ℕ}(ha:0 ≤ A)(cash:WilsonRootedKioskOccupiedSlip.Gross L w B₀ A d)
    (a b:V)(apart:a≠b)(s:(Γ).Mode)(roots:s.val={a,b})(t:T):
    (∫ω:ConfigurationPath R p,((q) t a (ω (i+1))-((ℒ) t (ω i)).part ((Γ).fire a))*
      ((q) t b (ω (i+1))-((ℒ) t (ω i)).part ((Γ).fire b)) ∂path R.family R.makes N p)=
    ∫W,(Z.output.density t W).part s/(P.eval W:ℂ)+((ℒ) t W).part s ∂scene R.family.path N p i:=by
  have hq(v:V):Envelope ((q) t v):=Envelope.compactC
    (WilsonPositionOriginalDressedQCohortSource.continuous_letter R Q D u μ orders (test t) v)
  have hl(v:V):Envelope (fun W=>((ℒ) t W).part ((Γ).fire v)):=
    WilsonPositionOriginalDressedQPublishedField.entire L hw ha cash _ v (by simp [Census.fire]) t
  rw [WilsonPositionOriginalDressedQPosterior.full R live _ _ (hq a) (hq b) _ _ (hl a) (hl b)]
  apply integral_congr_ae; filter_upwards with W
  have h:=WilsonPositionOriginalDressedQElectedPair.original R Q D u μ orders test simple live L href coarse Z a b apart s roots t W
  have good:(P.eval W:ℂ)≠0:=by
    rw [coarse];exact_mod_cast (Multi.AxisShift.chosen_positive R.makes.wilson live.le W).ne'
  calc
    _ = ((Z.output.density t W).part s+(P.eval W:ℂ)*((ℒ) t W).part s)/(P.eval W:ℂ):=by
      apply (eq_div_iff good).2;rw [h,mul_comm]
    _ = _:=by field_simp

end YM.Integration.WilsonPositionOriginalDressedQJointMoment
