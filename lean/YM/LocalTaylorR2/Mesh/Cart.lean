import YM.LocalTaylorR2.Mesh.Grace
import YM.LocalTaylorR2.Send
/-!
# Pre-reset readout **before** the actual nonlinear reclosure

Keep the scalar term and quadratic readout of this representation
separate. Affine statements on unmasked centered germs, not asserting
invariance of affine readout after realignment or in a different scheme.
Numerical uncertainty of quadratic projection retains TWO inverse
threshold powers, of scalar per site BEFORE the extensive conversion.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.CalendarStep
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Gas Ursell Trees Multiple OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration RG.Shoot Push.SectorMeasure Supply Input Testing Push.PriceCompiler Org
open ConnectedActivityE6.Blaze Blaze.March Captain Silica PhysicalNext PhysicalNext.Repeat Height Refrain Song
open PhysicalNext.Repeat.Greenbelt Match Roof Roost Geo Time Opera
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Progress.DirectedRecipe RG01.Vacuum Tail RG01.Survive
variable {G : Gauge}
open UVNext.CouplingReset Averaging
variable (Ξ : Mesh.Regime G)
variable {X: Metals G} {D:Rolls X.p} {A : Alloy X D} (R:Factor A) {m n N : ℕ}
variable {u: RG.Rep G (A.B.a.S.side (m+1) n)}
local notation "b" => A.B.a.budget m
local notation "β" => A.B.a.clock.hatBeta m
local notation "α" => (Alpha (A:=A) N m)
local notation "j₀" => A.B.a.clock.J m
local notation "j₁" => A.B.a.clock.J (m+1)
variable (H:Guide A.B R.shape N m n u) (O: Return.Wood A.B m n)
    (hH:Opera.Price A.B R.shape N m n u H)(hm:m<N)(hl:Lives A.B.bake N (m+1) n u)(hb:u.beta∈band A.B.a (m+1))
set_option quotPrecheck false
local notation "h₀"=> R.target (j₁) (j₀)
local notation "Γ"=> R.expense (j₁) (j₀)
local notation "Wg"=>A.B.a.clock.forcedAllowance m
local notation "Ef"=>Opera.earlyFee (p:=R.expense) A.B N m u.beta
local notation "L!"=>D.L (j₁)
local notation "Z!" => Song.posting (b) H
local notation "ι" => (RG01.Survive.identityX H)
local notation "C!"=>plusone H ι Chi.canonical α
local notation "xF" => A.B.a.clock.hatBeta (m+1)
include hH hl hb O hm
lemma postcard (hp:Mallow.RG12.Earned (survey Ξ) R.shape A.delay) (l:ℕ) (hy:l ≤ j₁) (ε:ℝ)(hε:loss j₁ ≤ ε)(h0:G.Simple):
    let x:= interp2 Ξ R H l true
    let y:= interp2 Ξ R H l false
    let Δ:= Averaging.delta ((Z!).read y)
    let err:= xF^requested (l+1) ε
    let t:= Song.weighty H Chi.canonical O
    Collection.Local Z! b y err Wg ∧ (b).threshold^2*|Δ| ≤ err ∧
      |Collection.vac y 0|≤err ∧
      Collection.vac (C!) t- Collection.vac x t=Collection.vac y 0 ∧
      Averaging.delta ((Z!).read (C!))-Averaging.delta ((Z!).read x)=Δ:= by
  obtain ⟨hx,hj,-,-,-,hA,hB,he⟩:=viaMesh Ξ R H O hH hm hl hb hp l hy ε hε
  intro x y Δ err t
  have hz : Collection.Local Z! b y err Wg:= by unfold y interp2; simpa only [Bool.false_eq_true,ite_false] using! he (fun i=> l+1 ≤ i) (l+1) le_rfl (fun _ h=> h)
  exact ⟨hz,Averaging.delta_bound h0 hz.projects,vac_ledger h0 hz,scalarFee h0 hB hz hx t, kineticFee h0 hA hB hx⟩
end YM.LocalTaylorR2.CalendarStep
