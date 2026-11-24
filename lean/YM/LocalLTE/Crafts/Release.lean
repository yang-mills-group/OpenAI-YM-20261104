import YM.LocalLTE.Crafts.Launch
import YM.LocalLTE.Pool.Dawn
import YM.LocalLTE.Bonnet.Canopy
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
omit hp hF hx hj hk hX hm J' hG
end Career
-- all budgets geometry. pre or post enact N not chosen prior to trajectory.
open Progress.DirectedRecipe WilsonStartup
set_option quotPrecheck false
structure Cready (W:Trail H p) : Prop where
    «cup» (m:ℕ): ∃ η:ℝ, WilsonStartup.Frost.Cup G p η (D.L (A.B.a.clock.J m)) A.B.a m H.κ -- L index choose I rather than upper. post_delay uses payhigher? investigate
    peers (j i:ℕ) : StepStages j i → ∀ x:ℝ,x≥ A.delay.betaEntry j →∀ k:ℕ,k ≤ p → East.Peers (D.L j) x (Testing.query X.p X.K j i) (R.target j i) (R.walls j i) (R.shape.o j i) (Pastel.pie k+1) p (W.κT j i k) H.w.ℓ H.κ
    at_top: Planned.Port.AtTop A.B.kin
-- Need ε results later. 
open Set Filter
variable (hp: Cready H W) (hG:G.Simple) (J':Adorn H W)
include hp
local notation "U"=> Frost.iceCap (n:=(A₀)) G p (B) (A.B.a.params m|>.clip)
local notation "w"=> Frost.bank (A₀) G p
local notation "u"=> O
def chorus (x:ℝ)(m n:ℕ):= fromTop A.B.kin m n x (Frost.bank (A.B.a.S.side m n) G p) (Frost.iceCap G p (A.B.a.budget m) (A.B.a.params m).clip x H.κ)
-- numeral.Budget equal
include hG
abbrev origin := w
variable (m n)
lemma beginning : let f(x:ℝ):= chorus H (p:=p) x m n; Curve (B) f (band A.B.a m) ∧ ∀ x∈band A.B.a m,(f x).beta=x∧ Lives A.B.bake m m n (f x) ∧ A.B.bake.Starter m n (f x)∧HasSlots (f x).p (f x).activities∧ Coup.License p (f x) H.κ (A.B.a.clock.hatBeta m) (Frost.trunkTag (A₀) p) (Trail.extent H W m):=by
    intro f; obtain ⟨η,Q'⟩:= hp.cup m; let X:= (A.B.a.params m); let θ:= x₀; let V x:= Frost.iceCap (n:=A₀) G p B X.clip x H.κ
    let T₁:=w; let Y:= band A.B.a m
    have hh : θ^(chip 0)= A.B.a.clock.allowance m :=by
       have he:0<θ:= (zero_lt_one.trans_le Q'.time); rw [Coup.chip_zero]; change _= (Real.sqrt θ)⁻¹^((11:ℝ)/5); rw [Real.sqrt_eq_rpow,← Real.rpow_neg he.le, ← Real.rpow_mul he.le]; congr 1; norm_num
    have hf x: f x=finish (Design.top G X.clip) X.clip B T₁ (V x) x 0:=by unfold f chorus fromTop; rw [hp.at_top]
    have hP:= Return.enough_room A.B m n
    have ht(x:ℝ)(hx:x∈Y) :‖x‖≤2*θ:= by have he:0≤x:=((half_pos (zero_lt_one.trans_le Q'.time)).le).trans hx.1; rw [Real.norm_of_nonneg he]; exact hx.2
    let Z:= A.B.a.clock.forcedAllowance m; have hV (x:ℝ)(hx:x∈Y):Ingredients T₁ (V x) B (A.B.a.clock.allowance m) Z:=by rw [← hh]; exact Frost.streamers G p B X.clip H.paid.choose_spec hG hP Q'.must.clip η _ Q'.time (ht _ hx) Q'.must.radius Q'.size Q'.e Q'.income Q'.frost (fun i hi=> Q'.bills _ hi _ hP) Q'.hank Q'.loan Q'.rates hx.1 -- order
    constructor; swap
    · intro x hx; have ht':SurfacePay A.B.kin (permissions A.B.a) m n x T₁ (V x):= ⟨hV x hx,(by intro U'; rw [hp.at_top]; exact Frost.eats G p (B) X.clip U' Q'.must.clip),trivial⟩
      rw [R.machine.ready]; refine ⟨rfl,⟨rfl,rfl,rfl,⟨A.B.support.cap _ _ le_rfl,(hV _ hx).gates ..⟩, PeriodFuture.begin hx ht'⟩,starter ht' hx _ _, (hV _ hx).spare_room (A.B.kin.path m m) X.clip x 0,?_⟩ -- type ν' derives numerics.rw ready changes W?
      rw [hf]; have hv:= Frost.seed (κ:=H.κ) G p B X.clip H.paid.choose_spec hG hP Q'.must.clip η _ Q'.time (ht _ hx) Q'.must.radius Q'.size Q'.e Q'.income Q'.frost (fun i hi=> Q'.bills _ hi _ hP) Q'.hank -- Packs.P radius→Ceiling
      have hz:4 ≤ Trail.extent H W m:= by
          have hi:= step_paid A.B.a m; have hv: W.crew H m ≤ CeilingExtent W.nextFloor (I):= (W.deep (J) (I) hi).trans (Coup.overhead _ hi); have hz:= Trail.breadth H W (m:=m) (n:=n)|>.1
          have ht:1 ≤ Coup.CeilingExtent W.nextFloor (I):=by
              by_contra! he
              have ht: W.crew H m=0:=by omega
              rw [ht,zero_mul] at hz; omega
          unfold Trail.extent; exact le_trans (Nat.mul_le_mul ht Q'.size) (le_refl _)
      exact Career.currencies _ _ hv Q'.time le_rfl hz
    rw [funext hf]; exact Frost.onR G p B X.clip Q'.must.clip Q'.time hV Q'.loan
end YM.PhysicalNext.Repeat.Mallow
