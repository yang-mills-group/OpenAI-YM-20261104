import YM.Integration.WilsonPositionOriginalDressedQCutSquare
import YM.Integration.WilsonPositionOriginalDressedQSeparation

/-! The complete original Q pair and the two genuinely filed one-name
fields on their common Wilson path. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDressedQResidualSquare
open Set Function Filter MeasureTheory Lattice Wilson RG Marker Cells QuadraticLocal
open OPE.Therm QLocalPhysicalPathKernel WilsonPositionOriginalDressedQFailedPath
open Source Labels FVA1 LocalComparison ComparisonDensity.Address
open PhysicalNext.Repeat.Legato MergeProof MergeProof.Accent MergeProof.Replicums
open RG3.Held RG3.Script.Picnic OriginalForcedAddresses ActualOriginalQReaders
open WilsonMacroscopicForwardTransfer WilsonPositionOriginalDressedQCohortSource
open Push.GridApprox WilsonPositionOriginalDressedQLiteralLamp WilsonPositionOriginalDressedQCutSquare
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

private theorem add_removed (x y z:ℂ)(E T:ℝ)(first:‖x-(y+z)‖≤E)(second:‖z‖≤T):‖x-y‖≤E+T:=by
  calc
    _ = ‖(x-(y+z))+z‖:=by rw [show x-(y+z)+z=x-y by ring]
    _ ≤ _ :=(norm_add_le ..).trans (add_le_add first second)

theorem original [Countable I](href:∀s:Slot u,R.family.ref s.2.size ≤ i+1)
    (coarse:P.eval=(Ψ).eval)
    (Z:WilsonRootedKioskSealedPost.Return P o Γ w k r reg hard ℒ Y)
    (hw:∀v,0<w v){A d:ℝ}{B₀:ℕ}(ha:0 ≤ A)(cash:WilsonRootedKioskOccupiedSlip.Gross L w B₀ A d)
    (a b:V)(apart:a≠b)(s:(Γ).Mode)(roots:s.val={a,b})(t:T)(m:ℕ)
    (distant:2*(m*(4*B₀+2)+2*B₀)<separation (o a) (o b))
    (qa qb:ℝ)(pa:∀U,‖(q) t a U‖≤qa)(pb:∀U,‖(q) t b U‖≤qb):
    let arm(v:V):=short L B₀ m ((Γ).fire v) t
    let step:=backTo R.family.path N p (Nat.le_succ i)
    ‖(∫U,((q) t a U-step (arm a) U)*((q) t b U-step (arm b) U) ∂scene R.family.path N p (i+1))-
      (∫W,(Z.output.density t W).part s/(P.eval W:ℂ) ∂scene R.family.path N p i)‖≤
      tailFee (w:=w) (a:=A) (d:=d) m ((Γ).fire a)*(qb+bound (w:=w) (d:=d) ((Γ).fire b))+
      (qa+bound (w:=w) (d:=d) ((Γ).fire a))*tailFee (w:=w) (a:=A) (d:=d) m ((Γ).fire b)+
      tailFee (w:=w) (a:=A) (d:=d) m s:=by
  classical
  intro arm step
  have hv (v:V):v∈((Γ).fire v).val:=by simp [Census.fire]
  have dis:Disjoint (region B₀ m (o a)) (region B₀ m (o b)):=by
    rw [Set.disjoint_left];intro z hz h'
    have tri:=Lattice.separation_triangle (o a) z (o b)
    rw [separation_comm z] at tri
    change separation (o a) z≤_ at hz
    change separation (o b) z≤_ at h'
    omega
  have group(v:V):Envelope ((q) t v):=Envelope.compactC
    (WilsonPositionOriginalDressedQCohortSource.continuous_letter R Q D u μ orders (test t) v)
  have lamp(v:V):Envelope (fun W=>((ℒ) t W).part ((Γ).fire v)):=
    WilsonPositionOriginalDressedQPublishedField.entire L hw ha cash _ v (hv _) t
  have removed:=WilsonPositionOriginalDressedQCutSquare.original R L live m B₀ hw ha cash a b _ _ (hv a) (hv b) t dis
    _ _ (group a).meas (group b).meas qa qb pa pb
  have joint:=WilsonPositionOriginalDressedQJointMoment.original R Q D u μ orders test simple live L href coarse Z hw ha cash a b apart s roots t
  rw [joint] at removed
  let ν:=scene R.family.path N p i
  letI:IsProbabilityMeasure ν:=probability (H:=R.family.path) (p:=p) R.makes.wilson live.le
  let leftH:=fun W=>(Z.output.density t W).part s/(P.eval W:ℂ)
  let rightH:=fun W=>((ℒ) t W).part s
  have allLeft:Envelope (exterior (C:=R.family) (N:=N) (Nat.le_succ i) (fun U=>(q) t a U*(q) t b U)):=
    WilsonPositionOriginalDressedQPosterior.conditional R live _ ((group a).mulC (group b))
  have cond(v:V):Envelope (exterior (C:=R.family) (N:=N) (Nat.le_succ i) ((q) t v)):=
    WilsonPositionOriginalDressedQPosterior.conditional R live _ (group v)
  have first:=allLeft.integrableC ν
  have mixed₁:=((cond a).mulC (lamp b)).integrableC ν
  have mixed₂:=((cond b).mulC (lamp a)).integrableC ν
  have last:=((lamp a).mulC (lamp b)).integrableC ν
  have plus:Integrable (fun W=>leftH W+rightH W) ν:=by
    refine (((first.sub mixed₁).sub mixed₂).add last).congr (ae_of_all _ fun W=>?_)
    have h:=WilsonPositionOriginalDressedQElectedPair.original R Q D u μ orders test simple live L href coarse Z a b apart s roots t W
    have good:(P.eval W:ℂ)≠0:=by rw [coarse];exact_mod_cast (Multi.AxisShift.chosen_positive R.makes.wilson live.le W).ne'
    change _= (Z.output.density t W).part s/(P.eval W:ℂ)+((ℒ) t W).part s
    have eqn: _ = ((Z.output.density t W).part s+(P.eval W:ℂ)*((ℒ) t W).part s)/(P.eval W:ℂ):=
      (eq_div_iff good).2 ((mul_comm _ _).trans h.symm)
    exact eqn.trans (by field_simp)
  have as':a∈s.val:=by simp [roots]
  have bs':b∈s.val:=by simp [roots]
  have rightI:Integrable rightH ν:=
    (WilsonPositionOriginalDressedQPublishedField.entire L hw ha cash s a as' t).integrableC ν
  have leftI:Integrable leftH ν:= (plus.sub rightI).congr (ae_of_all _ fun W=>by simp)
  have jointSplit:=integral_add leftI rightI
  dsimp only [leftH,rightH,ν] at jointSplit
  rw [jointSplit] at removed
  have seps:m*(4*B₀+2)+2*B₀≤ separation (o a) (o b):=by omega
  have later:‖∫W,rightH W ∂ν‖≤tailFee (w:=w) (a:=A) (d:=d) m s:=by
    simpa [rightH,tailFee,bound,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using norm_integral_le_of_norm_le_const (ae_of_all ν
      (WilsonPositionOriginalDressedQSeparation.original L hw ha cash s a b as' bs' seps t))
  exact add_removed _ _ _ _ _ removed later
end YM.Integration.WilsonPositionOriginalDressedQResidualSquare
