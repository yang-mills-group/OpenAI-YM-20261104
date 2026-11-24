import YM.Integration.WilsonOriginalCensusCanonicalMoments
import YM.Integration.WilsonOriginalCensusCanonicalPageFold
import YM.Integration.WilsonReceivedDepositedOrbitalKinetic

/-! The original kinetic reset and its connected field on the whole independently
repeated canonical top. Every subset retains its own relative page choices. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusCanonicalKinetic
open Function Filter Finset Lattice Wilson Laurent RG Source Labels Marker Multi QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise
open Comparison.RG02 Comparison.RG02.Cumulants Next.SectorChange AllOrder AllOrder.Floe
open PhysicalNext.Repeat.Legato Further.PhysicalPeriodLimitF933 Macrame Shingle
open FVA1Physical.TwoReset WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Embroider WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Soil
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedGeometric
open WilsonOriginalStarSceneWords WilsonThermometerDeclaredSeeds WilsonOriginalThermometerPalette
open WilsonReceivedCanonicalSocketRows WilsonReceivedCanonicalSocketFields WilsonReceivedCanonicalSocketSeed
open Pressure Push Push.AbsoluteSums Precision Tree Exterior Bloch PowerSeries
open PhysicalForestMarkedRay FVA1Physical.TwoReset
open scoped ContDiff Topology Classical BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
open WilsonLimitConstruction Work.F08 FullQLocal FullQLocal.RenderedStep
open WilsonVacuumPreResetDepositedIntegrand WilsonOriginalOccupiedForestIntegral WilsonOriginalMeasuredOccupiedForest
open WilsonVacuumPreResetOriginalOutput (covered)
open WilsonOriginalRelativeFoldedQuiet (relative)
open WilsonOriginalEarnedUnaryDriver (driver)
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonOriginalThreePurchasedRays (prescribed)

open LocalComparison Comparison.RG02.Cumulants Comparison.RG02.Assembly Order AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open PertExtension Series WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank
open WilsonOriginalEarnedUnaryDriver (driver)
open WilsonCoeffUV.Winding WilsonCoeffUV.Power Next.Rank
open FreeResolvent
open WilsonOriginalChargedForestQ WilsonVacuumPreResetFiniteRegister
open WilsonCapturedPrimaryWindingVerseRoster (coefficient)
variable {G:Gauge} {V:Type} [Fintype V] [DecidableEq V] (R:Run G)(d:V→ℕ){h:V→ℕ}(pt:V→Chamber)
  (q:(j:V)→Choice R d j)(N i per:ℕ)(hi:i<N)
  (F:Forest (step R i per).ratio)(tag:(step R i per).Choices)
  (x:Affinity.Wallet (WilsonOriginalMixedBlockRows.room V)) {n:Side}(a:Fin (Pages n (fine R i per))→V→Lattice.Cover)
local notation "J" => Stock.census V
local notation "K" => model R N i per hi
local notation "S" => step R i per
local notation "f" => fine R i per
local notation "A" => saddle R N i per F
local notation "ρ" => fderiv ℝ ((K).b F) 0
local notation "κ" => (fun j=>contact (h j))
local notation "φ" => relative R N i per hi F (covered R N i per)
local notation "badge" => (fun j:V=>(J).fire j)
local notation "c" => (fun j:V=>(x j).val)

open WilsonVacuumPreResetStationaryChange WilsonOriginalFoldedMarkedRightColumn WilsonCoeffUV.Mer
open WilsonReceivedCanonicalVerseRegister WilsonReceivedCanonicalVerseBasis


open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Mer
open WilsonOriginalCensusCanonicalPageFold (localOn folded)
open WilsonReceivedDepositedOrbitalGrade (booked)
local notation "front" y:max => WilsonReceivedCanonicalVerseRegister.start R d (κ) pt q y
local notation "γ" => ratioHigh (levels R) R.metals.O N i
local notation "terms" => WilsonOriginalCensusCanonicalFront.normalized (h:=h) (n:=n) R d pt q N i per F a

def ordinary (y:V → Lattice.Cover)(s:Finset V):Ink (Woods G (coarse R i per)):=
  flash (filed R N i per F (mass d s)
    ((WilsonReceivedDepositedVerseCensus.ordinary (front y) (present h) s).1 (f)))

def connected (kinetic:Cost)(y:V → Lattice.Cover)(s:Finset V):Ink (Woods G (coarse R i per)):=
  flash (pPly (present h) s (mist (S) F (upper R N i) (prediction R N i per) (ratio R)
    (covered R N i per) (front y) kinetic d s))

local notation "raw" => ordinary (h:=h) R d pt q N i per F
local notation "cum" t:max => connected (h:=h) R d pt q N i per F t

theorem ordinary_local:localOn (raw):=by
  intro y z s same
  unfold ordinary
  apply congrArg (fun t=>flash (filed R N i per F (mass d s) t))
  have healthy:= (OriginalCoverReanchoring.deposited (WilsonReceivedCanonicalVerseRegister.offer R d (κ) pt q)
    (fun j _=>WilsonReceivedCanonicalVerseBasis.grade R d (κ) pt j (q j))).1
  have sameField:levelsO (front y) s=levelsO (front z) s:=by
    apply levels_g
    intro T hT
    exact healthy.filial y z T fun j hj=>same j (hT hj)
  simp only [WilsonReceivedDepositedVerseCensus.ordinary,sameField]

include hi

theorem course (simple:G.Simple)(t:Cost)(y:V → Lattice.Cover):
    Equation (fun s=>redo t ((raw) y s)) ((cum t) y):=by
  have health:Eu d (front y):=IndependentSourcePathFamily.legal _ y
    (fun j _=>WilsonReceivedCanonicalVerseBasis.grade R d (κ) pt j (q j))
  change Equation (fun s=>redo t (flash (filed R N i per F (mass d s)
    ((WilsonReceivedDepositedVerseCensus.ordinary (front y) (present h) s).1 (f))))) _
  simp_rw [WilsonReceivedCanonicalSocketMist.reset R N i per hi F (front y) health _ (present h) t simple]
  exact WindE (S) F (upper R N i) (prediction R N i per) (ratio R) (covered R N i per)
    (front y) t (present h) (emera_far (levels R) simple R.alloy.B.ratio hi (f)).1 R.alloy.B.ratio health

theorem folded_course (simple:G.Simple)(t:Cost):
    Equation (fun s=>redo t ((terms) s)) (folded a (cum t)):=by
  have charge:localOn (fun y s=>redo t ((raw) y s)):=fun y z s eqn=>
    congrArg (redo t) (ordinary_local (h:=h) R d pt q N i per F y z s eqn)
  have bill:=WilsonOriginalCensusCanonicalPageFold.original a
    (fun y=>course (h:=h) R d pt q N i per hi F simple t y) charge
  have receipt:(fun s=>redo t ((terms) s))=folded a (fun y s=>redo t ((raw) y s)):=by
    funext s
    rw [WilsonOriginalCensusCanonicalFront.normalized,map_sum]
    rfl
  rw [receipt]
  exact bill

theorem entrance (simple:G.Simple)(B:fieldDir G (coarse R i per) 1)(r:ℕ):
    Extra.Trajectories.connected (WilsonOriginalCensusCanonicalMoments.moments (h:=h) (n:=n)
      R d pt q N i per F x a B r)=booked r (flatten B) (c) (folded a (cum 1)):=by
  have law:=folded_course (h:=h) (n:=n) R d pt q N i per hi F a simple 1
  simp only [WilsonReceivedDepositedOrbitalKinetic.identity,RingHom.id_apply] at law
  exact WilsonReceivedDepositedOrbitalGrade.logged r (flatten B) (c) law

/-- Each accepted thermal and angular coefficient comes from the original clock on
this edge and one common nonlinear vacuum. The sum is over the occupied lifts. -/
theorem original (simple:G.Simple)(B:fieldDir G (coarse R i per) 1)(r:ℕ):
    Extra.Trajectories.connected (booked r (flatten B) (c) (fun s=>redo (γ) ((terms) s)))=
      booked r (flatten B) (c) (folded a (cum (γ))):=
  WilsonReceivedDepositedOrbitalGrade.logged r (flatten B) (c)
    (folded_course (h:=h) (n:=n) R d pt q N i per hi F a simple (γ))

theorem restamp (simple:G.Simple)(s:Finset V):
    redo (γ) (folded a (cum 1) s)=folded a (cum (γ)) s:=by
  have old:=folded_course (h:=h) (n:=n) R d pt q N i per hi F a simple 1
  simp only [WilsonReceivedDepositedOrbitalKinetic.identity,RingHom.id_apply] at old
  exact congrFun (Equation.unique _ _ _ (old.mapKin (redo (γ)))
    (folded_course (h:=h) (n:=n) R d pt q N i per hi F a simple (γ))) s

end YM.Integration.WilsonOriginalCensusCanonicalKinetic
end
