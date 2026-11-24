import YM.LocalLTE.Fabric.Tack
import YM.LocalLTE.Fabric.Jazz
import YM.LocalLTE.Bonnet.Quiet
import YM.LocalLTE.Fabric.Priced
import YM.LocalLTE.Rate.Permit
/-! Curve witness & receipts. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost
open UVNext.CouplingReset Animals
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open YM.LocalLTE.Inset ClockB Urns Trio Slide Marlin
-- NOTE scope. factor uses `T` Launch.
variable {G:Gauge} {X:Metals G} {D:Rolls X.p} {A: Alloy X D} (R: Roost.Factor A){p0:ℕ} -- use eta
variable {R} {ε : ℝ} (H:Funding R p0 ε)
local notation "Wf"=> H.w
variable {N m n k:ℕ} {s:Set ℝ} {a:ℝ} {Q:In A.B.a m n}(F:Career H N m n s a Q)
local notation "T" => A.B.a
local notation "x₀" => A.B.a.clock.hatBeta m
local notation "B" => (A.B.a.budget m)
local notation "C₀" => R.target
local notation "J"=> A.B.a.clock.J (m+1)
local notation "I"=> A.B.a.clock.J m
local notation "s₀"=> ClockB.lanternPay G (D.L J) (X.p.profile I) H.w.q x₀
local notation "z" => Trio.base (Trio.resize H.w.ℓ (Rain.lint R.target A m)) (radiusB x₀)
local notation "A₀" => A.B.a.S.side m n
local notation "O" => Chi.canonical
local notation "γ" => A.B.kin.alpha N m
open Coup Scarf East LocalLTE.Fan Pastel
-- Tag for outputs. Function for any Era. Layer J. `ψ` pre-general as low as needed at all stages.
variable {p:ℕ} (W : Trail H p) (hm:m<N)
variable {R₁:Rep G (A.B.a.S.side (m+1) n)}
    (hV: Lives A.B.bake N (m+1) n R₁)(hx:R₁.beta∈ band A.B.a (m+1))
    (U: Guide A.B R.shape N m n R₁) (hU:Opera.Price A.B R.shape N m n R₁ U)
namespace Trail
local notation "L'"=> D.L J
local notation "A'"=> A.B.a
local notation "ξ"=>betaF G x₀ L'
local notation "J'"=> X.p.profile I
local notation "µ"=>Coup.monthly (G:=G) (D.L J) x₀ (3*(W.mass H m))
local notation "κ"=> W.crew H m*radiusB x₀
-- Local permit inputs. Tag budget wiring.Plaw. Use independent F tables.
variable {tag:ℕ→ℕ}
variable (hl : W.Hired H R₁ tag)
set_option quotPrecheck false
-- Exact cost EARLY per Step in projects.Budgets. ADD Pure predictor soon
local notation "S₁"=> (stagnate H.w.ℓ (Rain.lint R.target A m))*radiusB x₀
local notation "S'"=> ClockB.lanternPay G (D.L J) (X.p.profile I) H.w.q x₀
local notation "Q'"=> (fronts (m:=m) (A:=A) (C:=R.target) H.w)
local notation "ℒ" => East.lectures U p H.w.ℓ tag
local notation "D'"=> Beam.marquee U B
local notation "M"=> (lobby H W U tag)
local notation "V$"=> vested (p:=p) H U tag
local notation "e₁"=> Coup.lacquer (G:=G) (D.L J) (X.p.profile I) H.w x₀ (3*W.mass H m)
local notation "t₁"=> Coup.tune (G:=G) (D.L J) (X.p.profile I) H.w (Rain.lint R.target A m) x₀
local notation "t₀"=> (Meadow.timbresN (Meadow.intern U) («χ»:=Chi.canonical) γ H.w.ℓ)
local notation "e"=> Coup.bring (G:=G) (D.L J) (X.p.profile I) H.w (Rain.lint R.target A m) (W.crew H m) x₀ (3*W.mass H m)
variable (Y₁:Expose (A:=A) (R:=R.shape) H.w R₁.beta N m) (M₁:Maps (A:=A) (C:=R.target) H.w m N)
local notation "fa"=> Y₁.read H.w k
local notation "A!"=> Meadow.ash U O H.w.ℓ k γ
local notation "g"=> (ornament (c:=A₀) Q' fa)
local notation "Y!"=> (YM.LocalLTE.Patch.failure B Q' z fa U γ H.w.ℓ k)
local notation "F'"=> Coup.freezes (G:=G) (D.L J) (X.p.profile I) H.w (Rain.lint R.target A m) x₀ (3*W.mass H m)
variable (hp: Meadow.Budget (A.B.a.budget m) ((Beam.marquee U (A.B.a.budget m)).reg) (Meadow.ash U Chi.canonical H.w.ℓ k (A.B.kin.alpha N m)) (ClockB.lanternPay G (D.L (A.B.a.clock.J (m+1))) (X.p.profile (A.B.a.clock.J m)) H.w.q (A.B.a.clock.hatBeta m))) (hq:Y₁.Yields H.w k)
variable (k₁:ℕ)
local notation "η₀"=> (vested (p:=p) H U tag k₁)
local notation "X!"=> Trail.lobby H W U tag k₁
local notation "S!"=> Trail.bindZ H W U tag k₁

-- Standard layout at x.ψ.Sharp early target.
def seasonal (tag:ℕ→ℕ)(j:ℕ) (k':ℕ) := Marlin.bison (t₀ j) (Trio.ornament (c:=A₀) Q' (Y₁.read H.w j)) (Trail.sense H W U Y₁ tag j k')
def nations (tag:ℕ→ℕ)(k:ℕ)(p:ℕ):= Marlin.poursP B (Trail.bindZ H W U tag p) (Trail.seasonal H W U Y₁ tag k p)
abbrev jerseyX (tag:ℕ→ℕ)(k:ℕ):= Marlin.pluck B (Trail.bindZ H W U tag k)
local notation "q₀"=> forecastK A.B.a m R.scout R₁.beta
local notation "ℓ"=>Trail.seasonal H W U Y₁ tag k k₁
local notation "Y₀"=> Trail.nations H W U Y₁ tag k k₁
local notation "V₀"=> Trail.jerseyX H W U tag k₁
local notation "w₀"=> Trail.sense H W U Y₁ tag k k₁

lemma beads (tag:ℕ→ℕ) (θ:Signed)(x: Site A₀) : Nonempty (((Trail.lobby H W U tag k₁).read (t₀ k)).Moves θ x):=by
   exact packedMoves U (East.lectures U p H.w.ℓ tag) B (Meadow.intern U) _ _ _ k₁
include U M₁ hp hq hx hU hl hV hm
open Progress.DirectedRecipe
set_option maxHeartbeats 400000 in
lemma assessment : Ingredients (Trail.bindZ H W U tag k₁) (Marlin.dummy ℓ) (raiser B) 0 q₀:=by
    have he i:= Trail.hosts H W hm hV hx U hU hl Y₁ M₁ hp hq k₁ i -- order
    let b':=forecastK A.B.a m R.scout R₁.beta
    have hR:= Trail.earned H W (m:=m)
    have hB i:(coverNumber (B).B (neighbors (κ) (i:Site A₀)):ℝ) ≤ ballCost (W.crew H m):= by exact_mod_cast Scarf.standing (κ) (B) _ i le_rfl
    let f':= (F')
    let p':= Marlin.tithe (κ) f' (B) (ballCost (W.crew H m):ℝ)
    have hv:= R.pledging
    let d':= Cash.armK ((R.target J I)) L' (R.shape.μ J I) x₀ 0 (R.expense J I|>.degrees)
    have hT:d' ≤ q₀/8:= (Opera.backing A.B R.shape hv.conducts.income hx).trans_eq (by ring)
    obtain ⟨hi,hh,hΨ,hΓ⟩:= Rain.jersey (A:=A) (m:=m)
    have hK : (raiser B).supportExponent+1 ≤ (R.expense J I).earn:= by change (B).supportExponent+1+1 ≤ _; rw [hΨ]; linarith only [hv.agenda (J) (I) (step_paid A.B.a m)|>.1]
    obtain ⟨v,h₁,h₂⟩:= Refrain.chargesOut (raiser B) U (Meadow.intern U) O hU rfl hK
    obtain ⟨-,-,hP,_⟩:= R.inn.terms.allot (J) (I) (step_paid A.B.a m) x₀ (A.B.valid.pays m)
    let α (β:ℝ):= (R.scout (J) (I)).pair.strong (ξ) β
    have hm': q₀= α R₁.beta:= by unfold forecastK α; rw [PriceCompiler.beta_eq A.B.valid]
    have hν : Next.Scheduling.inBand (betaF G x₀ L') R₁.beta:=by rw [← PriceCompiler.beta_eq A.B.valid]; exact trial_in hx
    have hξ:p' ≤ betaF G x₀ L' ^(-(1/8):ℝ):= by unfold p' Marlin.tithe; rw [hΨ]; exact hR.frost
    have h₀:0≤ f':=(norm_nonneg _).trans ((he 0).2.2 1); have hθ:0≤p':=by unfold p' Marlin.tithe; positivity
    rw [hm']; obtain ⟨v₁,h₃⟩:=hP _ hν d' p' (budget_nonneg (h₂ 0)) hθ (show _≤ α R₁.beta/8 from hm' ▸ hT) hξ
    refine Marlin.stakes B (X!) (κ) (κ) (t₀ k) g w₀ (?_) (fun θ x=> W.beads H U k₁ tag θ x) h₃ h₁ h₂ (fun i=> (he i).1) (fun i=> (he i).2.1) (fun i=> (he i).2.2) hB (le_refl p') -- check
    exact Refrain.qualified _ _ _ _ _ _ rfl

-- wide Norm E ALL
end Trail
end YM.PhysicalNext.Repeat.Mallow
