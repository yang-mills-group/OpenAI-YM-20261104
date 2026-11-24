import YM.LocalLTE.Key.Call
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
-- Career lift. uniform Θ with Horites
variable (k':ℕ) (tag:ℕ→ℕ)
-- permits initial Loft post l_b. Needs W.l<chip.I ad.
local notation "P"=>X.p.profile I
local notation "L"=>D.L J
open Collection.Price LocalLTE.FrameBox Progress.DirectedRecipe Averaging
namespace Career
local notation "Ω"=> F.hearth H
local notation "d'"=> W.crew H m*radiusB x₀
local notation "Q₀"=> (fronts (m:=m) (A:=A) (C:=R.target) H.w)
local notation "t₀"=> (F.school H W k' tag)
local notation "V₀"=> (F.porch H W k' tag)
local notation "κ₀"=> H.κ
local notation "T₁"=> (Trio.resize H.w.ℓ (Rain.lint R.target A m))
local notation "S"=> (A.B.a.S)
local notation "u"=> W.hop H m
local notation "κd"=> W.pay
variable (J' : Adorn H W) (hk:F.Accepts H k)(hF:∀ x∈s, Trail.Hired H W (Q x) tag)
variable (hG:G.Simple)(x:ℝ)(hx:x∈s)
set_option quotPrecheck false
local notation "Φ" x=> F.fruits H W k' tag x
local notation "Π" => F.billow H W k' tag
local notation "R₀" => A.B.kin.path N m
local notation "X₀"=> F.index H W k' tag k
local notation "L₀" => (A.B.a.params m).clip
local notation "ts"=> A.B.a.params m
-- use Actual P-with height. D.
def barn := Price.bells B R₀ t₀ p
def goals(x:ℝ) := Price.merits ts R₀ B t₀ (Φ x) γ Π H.κ -- use k? remove
-- Clip ν

def tongue (k:ℕ)(x:ℝ):= Price.azures (A.B.a.params m).clip B R₀ t₀ (F.index H W k' tag k x) p (Averaging.delta ((F.school H W k' tag).read (F.index H W k' tag k x))) γ (F.goals H W k' tag x)
local notation "B!"=> F.barn H W k' tag
local notation "v"=> F.tongue H W k' tag k
local notation "κT"=> forecastK A.B.a m R.scout
local notation "q"=> quoteHard A.B.a m R.book
local notation "R!"=> fraction A.B.a m
local notation "eo"=> forecastE A.B.a m
local notation "u₀"=> (q (Q x).beta)
local notation "U"=> F.rea H W k' tag (k:=k)
local notation "D₁"=> delta ((F.school H W k' tag).read (F.index H W k' tag k x))
variable (hX:Trail.Keeps H (F.hearth H x) tag p k')
include J' hx hX hG hk hm hF
set_option maxHeartbeats 600000 in
lemma clockW : Ingredients (B!) (F.tongue H W k' tag k x) B R! u₀ ∧ (∀ (β r:ℝ), Coup.License p (finish R₀ L₀ B (B!) (v x) β r) H.κ (betaF G x₀ L) (Price.grade (A₀) p) (d')) ∧
    ∀ (β r:ℝ)(V:Config G (A₀)), (Progress.DirectedRecipe.trunk R₀ L₀ B (B!) (v x) β r).eval V*Real.exp (∑' i,(v x|>.logarithm i V))=(Progress.DirectedRecipe.trunk R₀ L₀ B (shelves t₀ R₀ B) (branch t₀ R₀ L₀ B (X₀ x) γ) β r).eval V*Real.exp (∑' i,(branch t₀ R₀ L₀ B (X₀ x) γ).logarithm i V):=by
    have he:= step_paid A.B.a m; have h:=A.B.valid.pays m
    have hQ:= params_eq A.B.valid m; let t:= (A.B.a.budget m); let g:=ts; let C:=A.B.a.clock
    have ht : Price.Colors G L g (Pane.cloak D J) p (u) (J'.revenue J I) H.κ x₀ (d'):= by rw [show g=P from hQ]; exact J'.canopy _ _ he _ h
    have hp :2*(B).B≤ (d'):= by
       let b:= (B).B; have hz:= Trail.breadth H W (m:=m) (n:=n)
       have hy:= hz.2.1; unfold Trio.base Trio.tent at hy; exact le_trans (by change 2*radiusB x₀ ≤ _; omega) hy -- radius
    have ha: |γ|≤ |Pane.cloak D J|:= (Boulevard.coupling A N m hm).trans (le_abs_self _)
    have hx':=(R.machine.passes hm F.turns)
    apply Price.furlong g R₀ B t₀ (X₀ x) (F.fruits H W k' tag x) γ L x₀ Π H.κ p u (J'.revenue J I) (A.B.support.cap _ _ hm.le) ht ⟨rfl,rfl,rfl⟩ rfl rfl (Trail.breadth H W (n:=n)|>.2.2) hp hx'.1.width hx'.1.decent hG ha H.paid.choose_spec (F.atEarn H W hm k' tag hk hF _ hx) (fun i hi=> ?_) (hx'.1.fees x hx) -- order Career. printing
    exact ⟨F.wealthy H W k' tag x i, F.primordial H W hm k' tag J' hk hF x hx i hi hX⟩
end Career
end YM.PhysicalNext.Repeat.Mallow
