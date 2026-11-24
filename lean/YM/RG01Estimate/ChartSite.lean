import YM.RG01Estimate.Parchment
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Pane.Thrills
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Reps
/-!
 # Price the actual stencil family. Must still pay curvature/candidate inputs!
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Board
open PhysicalNext.Repeat
open Filter Function Lattice Wilson RG RG.Supply Input Precision Org Tree Exterior Gauge
open Matrix Finset Push AbsoluteSums Gas Extra.Iteration Extra.Iteration.Calibration Bid Bloch Laurent UVNext UVNext.PricedKernels
open Pressure AnalyticBridge VerifiedReset Collection Quotes PriceCompiler Uniform RG.Shoot
open ConnectedActivityE6 Testing SectorMeasure Further.PhysicalPeriodLimitF933 Further.PhysicalPeriodLimitF933.Mural
open Sienna Token Lantern Lapis Shellac Fare Planned.JetPort Pane
open Laplace Courtyard Receipt ConnectedActivityE6.Coat
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {X:Metals G} {D:Rolls X.p} {c f L : Side} {i j m n N : ℕ}
variable {C:Targets X.p X.K}{Z:Expenses C}{p:Return.Wages}{v:ℕ→ℝ}(R:PhysicalNext.Repeat.Register D Z p v)
   (hP:4 ≤ j)(d:ℕ)

-- ALL y selected uniformly: exist ρ after pieces? coefficient producer can use whatever trajectory here
-- including proofs `Service`/`ClassicalMatch` for RG02 uses.
section orders
local notation "P" => Mural.sheet X.p D hP
local notation "K" => X.p.kernel
local notation "σ" => X.p.profile j
local notation "G₀" => (C j i)
local notation "hh" => (Trio.paySide G (D.L j) d)
set_option quotPrecheck false
local notation "α" => (σ).clip
local notation "γ" => X.p.profile i
variable (A:Before G (X.p.profile j).width (X.p.profile j).paths (Mural.sheet X.p D hP).J X.p.kernel (n+3))

-- per Qo. Υ after d opened. 
def Boardwalk (m r i':ℕ) (D' : ℝ)(Y a e s W w Z' Q Q':ℝ→ℝ)(t:ℝ) :=
     ∀ (c f:Side) (S:StepData c f) (T:Tube G S)(h:S.patch=P)(hT:S.kernel=X.p.kernel)
       (F:Forest S.ratio) (O:ChartRatio G) (α' Φ κ α₀:ℝ) (B B': BudgetPoint)(β x':ℝ)
       (u: Bid.Dir G c→AxisChart G F) (U:Coat T F),
       Quilt T F (hh t) → T.high=(X.p.profile j).clip → T.low=(X.p.profile i).clip →
       T.up.Bounds T.high (X.p.profile j).width (X.p.profile j).paths (ConnectedActivityE6.loopBill G S.patch.L t) →
       (∃ Λ, T.down.Bounds T.low (X.p.profile i).width (X.p.profile i).paths Λ) →
       Critical F T.high T.up u → ClassicalMatch F T.high T.low T.up T.down u →
       FiniteBound F T.up T.down T.high T.low α' O u Φ κ α₀ → (warm A h hT).Service F T.high T.up u →
       ∀ l:S.Choices, U.x=t → U.width=(R.o j i).K → U.manifest → B'.threshold=Pressure.temp t →
       Cash (p j i) t (R.μ j i) (D.L j) (C j i) (R.o j i) x' T (Pane.virgin T B β) →
       ∀ (x:Positions (Uniform.Primary c G)), 0≤ s t → 1≤Y t → ‖x‖+1<Y t → U.V=represent (Uniform.tint G _ (gStep β • x)) → flags (Pressure.temp t) U.V=∅ →
       Note T F B l u (C j i).table t (a t) (wick G S.patch.L D' t) (Y t) β (s t) (e t) (W t) (w t) (Q t) (Q' t) x i' n r m ∧
        ∃ ε:ℝ, ∀ z ∈ Metric.closedBall (gStep β • x) (furl G S.patch.L t), (gStep β)⁻¹ • z ∈ Metric.ball 0 (Y t) ∧ Courtyard.Interior F T (C j i).table l u B β (wick G S.patch.L D' t) z (eaves G S.patch.L t) (Z' t) ε n

lemma billboard (he:2 ≤ n)(hi:StepStages j i) : ∃ (d':ℝ) (V:ℝ→ℝ), 0<d' ∧ Cookie G (D.L j) V ∧
      ∀ (R' m' i':ℕ) (s Y a e:ℝ→ℝ)(q:ℝ), R'+m'≤n → 0<R'→ Cookie G (D.L j) a → Cookie G (D.L j) e→ Cookie G (D.L j) Y→ Rate G (D.L j) q s→
      ∃ W w K' Z':ℝ→ℝ, Cookie G (D.L j) W ∧ Cookie G (D.L j) w ∧ Cookie G (D.L j) K' ∧ Cookie G (D.L j) Z' ∧ ∀ᶠ t in atTop, Boardwalk (i:=i) R hP d A m' R' i' d' Y a e s W w V K' Z' t:= by
   obtain ⟨d',T₀,h,h₀,H⟩:= Receipt.wide_pay P (X.p.profile j).clip (X.p.profile i).clip G₀ (R.o j i) A
      (Classical.choice (BareRates.offered G (γ).width (γ).paths _)) (Classical.choice (Planned.JetPort.purchase (G₀).table (G₀).table_exists _)) (fun t=>hh t) he ((R.consumes j i hi).2.1) (Trio.circles G (D.L j) d)
   refine ⟨d',T₀,h,h₀,fun R' m' i' s Y a e q hQ hM he hv hr hS=>?_⟩
   obtain ⟨W,w,K',Z',hL,hM,hq,hz,hZ⟩:= H R' m' i' s Y a e q hQ hM he hv hr hS
   refine ⟨W,w,K',Z',hL,hM,hq,hz,?_⟩
   filter_upwards [hZ] with t ht
   intro c f S T hp hT F O a' v y α' B B' β x ρ U hJ hk hK' hU hD hM' hc hX hv l hΦ hW hS hB hY z hm hz hr hx hZ
   obtain ⟨Λ,hΛ⟩:=hD; have h':S.patch.L=(D.L j):= congr_arg RG.Patch.L hp
   have hs:S.patch.L=(P).L:= congr_arg RG.Patch.L hp
   rw [hs] at hU ⊢
   simpa only [hs] using!  ht _ _ S T F hp hT hJ hk hK' (hk ▸ hU) Λ (hK' ▸ hΛ) ρ hv hc l U hΦ hW hS z B B' β x hB hY hm hz hr hx hZ -- ht inner ε furl S.patch.L differs
end orders
end YM.RG01Estimate.Board
