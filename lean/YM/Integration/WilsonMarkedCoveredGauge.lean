import YM.Integration.WilsonPointChildFullGauge
import YM.Integration.WilsonConditionalTaylorWheelAuthStrip
import YM.Integration.WilsonFormalGaugeSections
import YM.FormalBulk08.Kemp.Icy

/-! Nonlinear gauge covariance of the complete independently filed marked
coefficient after its genuine many-period copy. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMarkedCoveredGauge
open Function Filter Finset Lattice RG Laurent Precision
open FormalBulk08 Reef Orb Jets Shore Mesa Kemp Lotus Lava Stationary
open WilsonCoeffUV WilsonCoeffUV.Soil WilsonCoeffUV.Bank WilsonCoeffUV.Mer WilsonCoeffUV.Blue
open scoped Classical BigOperators Topology
variable {G:Gauge}{V:Type}[NormedAddCommGroup V][NormedSpace ℝ V]{k:ℕ}{K:Era G V}

/-- The upper source and every occupied derivative are transported together
to the finite original auxiliary torus. The copy is taken at fixed UV course. -/
theorem published (bought:Auth k K)(o:Loc G 1)(f:V→L[ℝ]ℝ)(n:Side):
    let W:=Kemp.banner k ((tuftV f K).2) n
    Rite W W 1 0:=by
  intro W
  let A:=tuftV f K
  let p:=fun m:Side=>Blue.flash (A.1 m)
  have valid:Auth k A:=bought.tuft f
  have rank (j:ℕ):∀ᶠ m:Side in atTop,∀ l,k+j<l→ rancho (p m) j l=0:=by
    refine Eventually.of_forall fun m l high=>?_
    have hj:=WilsonConditionalTaylorWheelAuthStrip.finite A valid m
    by_contra away
    have leq:=hj j l away
    change l≤k+j at leq
    omega
  have extent:=WilsonConditionalTaylorWheelAuthStrip.cover A valid
  have even (j r):Agate (A.2 j r):=by
    have symmetric:Blue.Smooth (A.2 j r):=(valid.wing j r).pure (.of_forall fun n=>valid.pale n j r)
    intro x σ
    exact symmetric σ x
  have copy (j r):rancho W j r=sieve n (A.2 j r):=Kemp.badge _ extent even le_rfl n j r
  have salary:=WilsonConditionalTaylorWheelAuthStrip.original A valid o
  exact Kemp.verdict n 1 (fun m=>WilsonPointChildFullGauge.submitted bought m f.toLinearMap)
    (fun j=>k+j) (fun j=>k+j) rank rank salary salary copy copy

/-- Original physical group-law gauge tests on the folded source, with its
actual scalar at every finite coupling grade and one arbitrary center test. -/
theorem panel (bought:Auth k K)(o:Loc G 1)(f:V→L[ℝ]ℝ)(n:Side)(s:Site n→ℝ)(j:ℕ):
    let W:=Kemp.banner k ((tuftV f K).2) n
    AllOrder.Haiku.Vernal G n (WilsonFormalGaugeSections.panel s W) j:=
  WilsonFormalGaugeSections.original j s _ (published bought o f n)

end YM.Integration.WilsonMarkedCoveredGauge
end
