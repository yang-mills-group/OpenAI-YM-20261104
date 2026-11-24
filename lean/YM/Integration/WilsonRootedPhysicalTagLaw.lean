import YM.Integration.WilsonRootedMayerTagLaw
import YM.Integration.WilsonLimitConstruction.FundedCensusVacuum

/-! Native local tag normalization on the actual pre-reset station and the held original Haar field. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedPhysicalTagLaw

open Function Filter Lattice RG Wilson Pressure Tree Finset
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open ConnectedActivityE6 ConnectedActivityE6.Coat AnalyticBridge VerifiedReset Collection Quotes Push.PriceCompiler
open RG.Supply RG.Shoot Input Org Time Height Opera Boulevard Roof Greenbelt Lotus
open Push Push.SectorMeasure Progress.DirectedRecipe
open scoped Classical BigOperators Topology Matrix.Norms.Frobenius

variable {G : Gauge} (R : Run G) {N per m : ℕ} (hm : m<N)
variable (P : WilsonLimitConstruction.FundedCensusVacuum.Station R N per m)
local notation "Sₘ" => R.alloy.B.a.clock.op m per
local notation "Tₘ" => Pressure.Testing.ships R.alloy.B N m per
local notation "Y₁" => R.family.path.rep N per (m+1)
local notation "J₁" => R.alloy.B.a.clock.J (m+1)
local notation "J₀" => R.alloy.B.a.clock.J m
local notation "q₀" => R.kit.walls J₁ J₀

include hm

/-- The physical chart furnishes the native tag law and stamp. The remaining
likelihood and old forced contract are retained for every rough field and every original tag. -/
theorem original (p : Molecule Sₘ) {F : Forest (Sₘ).ratio} (X : Coat Tₘ F)
    (hx : X.x=R.alloy.B.a.clock.hatBeta m) (hw : X.width=(R.kit.shape.o J₁ J₀).K)
    (hmf : X.manifest) (y : F.Slice G) (z : Air (R.family.side (m+1) per) G) :
    let A:=X.wrapY y
    let v:=A.liftA (Y₁).beta z
    let U:=A.input v
    let c:=(Fintype.card (Sₘ).Choices:ℝ)⁻¹
    let fail:=WilsonRootedMayerTagLaw.remaining P.guide p A z
    (Sₘ).likelihood U A.k=c*fail ∧ ∀ k : Finset ℕ,
      c*(∏ i : Panic (R.family.side m per) (R.family.side (m+1) per),A.rawStorm v q₀ A.seeds Y₁ k i) =
        A.χ.distribute A.seeds A.x q₀ U A.k A.V * (c*fail) * Contract.order Y₁ k univ U := by
  intro A v U c fail
  have stamp := Pane.ovation R.alloy N (R.alloy.B.a.S.oneStep m per).exact_size hm R.kit.pledging.conducts.full
  exact ⟨WilsonRootedMayerTagLaw.original P.guide p A hx hw hmf stamp z,fun k=>
    WilsonRootedMayerTagLaw.storm P.guide p A hx hw hmf stamp z k⟩

end YM.Integration.WilsonRootedPhysicalTagLaw
