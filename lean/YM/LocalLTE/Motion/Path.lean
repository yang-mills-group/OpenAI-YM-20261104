import YM.LocalLTE.Motion.Style
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
include hp hF hx hj hk hX hm
lemma terrain (v:ℝ)(hv:0<v)(i:ℕ) : ∀ᶠ y in 𝓝[s] x, let A:= (F.porch H W k' tag).reg i; (B).supBounds A.site A.support (Trail.histogram H W (F.hearth H x) tag k' j i - Trail.histogram H W (F.hearth H y) tag k' j i) v:=by
    let Tz:=F.borough H; have hM y : (F.holds.latch y).1 ∈ s := (F.holds.latch y).2
    let X':=(F.porch H W k' tag).reg i; have ht y:= F.turns _ (hM y); let L₁:= D.L J
    let u₀:= L₁.val*radiusB x₀; let K y:= F.hearth H y; have hk' y : Coup.License p (Tz y) H.κ (betaF G x₀ L) tag u₀ :=by
       have hp : Trail.Hired H W (Tz y) tag := hF _ (hM y); have hz:1 ≤ betaF G x₀ L:=(H.vote.cash (J) (I) (step_paid A.B.a m)).2 _ (A.B.valid.pays m)|>.light.1
       unfold Trail.Hired at hp; rw [beta_eq A.B.valid] at hp
       exact Career.currencies p tag hp hz le_rfl (Coup.forecast_ge («C»:=A) (m:=m) W.enough) -- syntax
    have hm':= Pane.ovation A N (A.B.a.S.oneStep m n).exact_size hm R.pledging.conducts.full
    let f y:= Trail.histogram H W (F.hearth H y) tag k' j
    have he y (hy:y∈s): (B).Regular X'.support (f y i)∧∃ v,(B).supBounds X'.site X'.support (f y i) v:=by
       have hv:= F.cartons H W hm k' tag hk hF y hy (hX _ hy) _ hj
       let Zx:= F.holds.latch y; have hU:= F.menuX H W k' tag y; have hP:= Trail.oldTol H W hm (ht y).1 (ht y).2 (K y) (hF _ (hM y)) (hk y hy|>.1); have h':= Scarf.acreage _ _ _ _ (Trail.stairV H W (tag:=tag) (K y) k') _ hP; obtain ⟨w,hW,hq⟩:= hv; let f':=(F.folio H k y).logRead
       have hp : f'= (Meadow.timbresN (Meadow.intern (K y)) («χ»:=Chi.canonical) γ H.w.ℓ k).logRead:= congr_arg Source.logRead (F.aloft H y) -- collision
       have hh : Meadow.Budget B (F.porch H W k' tag).reg f' (kiosk (preExponent B) (W.crew H m) * lacquer (G:=G) (D.L J) (X.p.profile I) H.w x₀ (3*Trail.mass H W m)):=by rw [hU,hp]; exact h' -- param underscore\ budget
       obtain ⟨Vb,hs,hF⟩:= hh
       have hxg : f y i=f' i-(f' i-f y i):=(sub_sub_cancel ..).symm
       rw [hxg]; exact ⟨VerifiedReset.reg_sub (hF _|>.1) (hq _|>.1),_,VerifiedReset.sup_sub (hF _|>.1) (hq _|>.1) (hF _|>.2) (hq _|>.2)⟩
    apply East.waves (K x) tag Tz K hm' hp (fun y=> ?_) (fun i hi=> F.flowE H x hx i) (F.movesY H x hx) hk' O (hk' x) v hv X'.site X'.support k' j B i le_rfl (he x hx) (by filter_upwards [self_mem_nhdsWithin] with tv htv; exact he _ htv) -- z notation fix
    exact ⟨(ht y).1.path.trans (ht x).1.path.symm,(ht y).1.point.trans (ht x).1.point.symm,F.wave.reg _ (hM y) _ (hM x), F.wave.forced _ (hM y) _ (hM x)⟩
end Career
end YM.PhysicalNext.Repeat.Mallow
