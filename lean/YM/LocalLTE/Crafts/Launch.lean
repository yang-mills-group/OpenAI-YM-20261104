import YM.LocalLTE.Motion.Pre
import YM.LocalLTE.Crafts.Trestle
import YM.LocalLTE.Crafts.Canal
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
variable (x:ℝ)(hx:x∈s)(j:ℕ)(hj:j≤p)
local notation "s'"=> (A.B.a.budget (m+1))
local notation "A!"=> (A.B.a.S.side (m+1) n)
-- Need Post for gears. Price after all L.Y wait.Stokes paths. Crew.Shape from Trail finite K tags. 
local notation "C"=> (R.target (J) (I))
local notation "d₁"=> (R.shape)
variable (hp : East.Peers (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m) (Testing.query X.p X.K (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (R.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (R.walls (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (R.shape.o (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (pie j+1) p (W.lease H m j) H.w.ℓ H.κ)
    -- R.walls edit. includes all old geometry.
variable (hX:∀ x∈s,Trail.Keeps H (F.hearth H x) tag p k')
set_option quotPrecheck false
local notation "T₀" => F.fruits H W k' tag
include hp hF hx hj hk hX hm J'
variable (hG:G.Simple)
include hG
local notation "Π" => F.billow H W k' tag
local notation "R₀" => A.B.kin.path N m
local notation "X₀"=> F.index H W k' tag k
local notation "L₀" => (A.B.a.params m).clip
lemma fizz (v:ℝ)(he:0<v) : ∀ᶠ y in 𝓝[s] x, Stocked B (Price.tubeX R₀ B t₀) (F.goals H W k' tag x j-F.goals H W k' tag y j) v:=by
   let P₀:= A.B.a.params m; have ht : Price.Colors G L P₀ (Pane.cloak D J) p u (J'.revenue J I) H.κ x₀ d':= by rw [show P₀=P from params_eq A.B.valid m]; exact J'.canopy _ _ (step_paid A.B.a m) _ (A.B.valid.pays m)
   have hC:= R.machine.passes hm F.turns; let f(x:ℝ):= F.fruits H W k' tag x j; let o:= Π
   have hh:= Trail.breadth H W (m:=m) (n:=n); let i:=(B)
   have hv: i.B=radiusB x₀:= rfl; have hs:2*(B).B ≤ (d'):= by
      have hz:= hh.2.1; unfold Trio.base Trio.tent at hz; exact le_trans (by change 2*radiusB x₀ ≤ _; omega) hz
   have hr: Price.Merchant G L H.κ (B).order (B).power j d' x₀:= ht.warm _ hj; have hV: Price.Found G L H.κ (B).order (B).power j x₀:= ht.wake _ hj
   exact Price.cred (p:=B) (t:=x₀) (A.B.support.cap _ _ hm.le) hC.1.width hG (Return.enough_room A.B m n) (lt_of_le_of_lt (Nat.mul_le_mul_left _ (show (B).B≤ (d') by omega)) hh.2.2) hv rfl ht.temp ht.ramp ht.scale H.paid.choose_spec hC.1.decent t₀ o s f hx (j:=j) (fun y hy=> ⟨F.wealthy H W k' tag _ _, F.plotted H W hm k' tag J' hk hF y hy j hj hX ⟩) (F.gateU H W hm k' tag J' hk hF _ hx j hj hp hX) hr hV hh.2.2 v he γ -- order
omit hp hx hj
-- ALL Peers schedule out. single Tape
variable (hE:∀ j≤p, East.Peers (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m) (Testing.query X.p X.K (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (R.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (R.walls (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (R.shape.o (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (pie j+1) p (W.lease H m j) H.w.ℓ H.κ)
variable (C':Return.Bookings A.B m n R.walls)
local notation "Vp" => F.Voy H W k' tag k
include hE C'
lemma plot : Curve (A.B.a.budget m) (F.Voy H W k' tag k) s:=by
    have h:= F.launch H W hm k' tag hk hF hG C'|>.1; have hx':= R.machine.passes hm F.turns; let G':=F.goals H W k' tag
    exact Price.harbor (q:=fun _=> fraction A.B.a m) (w₀:=fun x=>quoteHard A.B.a m R.book (Q x).beta) (p:=B) (A.B.support.cap _ _ hm.le) hx'.1.width hG (Return.enough_room A.B m n) hx'.1.decent t₀ s X₀ (F.atEarn H W hm k' tag hk hF) (F.meets H W hm k' tag hk hF) γ p G' (fun j hj x hx=> F.fizz H W hm k' tag J' hk hF _ hx j hj (hE _ hj) hX hG) (fun x hx=>(F.clockW H W hm k' tag J' hk hF hG x hx (hX x hx)|>.1)) h.beta h.v -- order
end Career
end YM.PhysicalNext.Repeat.Mallow
