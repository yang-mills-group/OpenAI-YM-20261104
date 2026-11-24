import YM.LocalLTE.Key.Pounds
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
-- Clip ν

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
abbrev Voy (k:ℕ)(x:ℝ):= finish R₀ L₀ B (F.barn H W k' tag) (F.tongue H W k' tag k x) (F.rea H W k' tag (k:=k) x|>.beta) (F.rea H W k' tag (k:=k) x|>.v)
local notation "Vp"=> Voy H F W k' tag k x
-- loosen Currency after projection ∀tag pc.
omit J' hx hX hG hk hm hF
section reduce
variable {G:Gauge}{Z:Side}{W:Rep G Z}{r t c:ℝ} {e A:ℕ}
lemma currencies (p:ℕ)(f:ℕ→ℕ)(h:Coup.License p W c t f e)(ht:1 ≤ r)(hp:r≤ t)(hv:e≤A): Coup.License p W c r f A:=by
    obtain ⟨f',y,hq,hy⟩:= h.bills; have hB i: 1 ≤ East.bloom r (f i):= East.bloom_bill ht _
    refine ⟨⟨hB,y,hq,fun i=> ?_⟩,fun i hi=> ?_,fun {i} hi hp j hj=> ?_⟩
    · refine budget_loosen (budget_mono (hy i) (fun j=> ?_) (fun j=> ?_)) (Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le ht) hp (by norm_num [Pastel.chip])) -- edit
      · split; exact mul_nonneg (Real.exp_nonneg _) (mul_nonneg (zero_le_one.trans (hB _)) (hq _|>.1)); exact le_rfl
      split; next h=> exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (zero_le_one.trans ht) hp (by positivity)) (hq _|>.1)) (Real.exp_nonneg _)
      exact le_rfl
    · obtain ⟨z',hz,hS⟩:=h.crop i hi; exact ⟨z',hz.trans hv,hS⟩
    exact (neighbors_mem ..).mpr (((neighbors_mem ..).1 (h.room hi hp hj)).trans hv)
end reduce
include J' hx hX hG hk hm hF
-- REAL Move layout.advance.G.Y. Normalization charged.K payment via Prices.
variable (C':Return.Bookings A.B m n R.walls)
include C'
lemma accepted : A.B.Move N m n Vp (Q x) ∧ Accurate A.B R.post N m n Vp (Q x)∧ (Vp|>.v)=Collection.vac (F.index H W k' tag k x) (F.peeled H k x) ∧ Coup.License p Vp H.κ x₀ (Price.grade (A₀) p) (Trail.extent H W m):= by
    let B₀:= A.B.a; let p':= B; let Z:= R₀; let U₁:= F.atLamp H W hm k' tag hk hF; let Y₀:=Vp
    obtain ⟨hr,he⟩:=F.clockW H W hm k' tag J' hk hF hG x hx hX
    have hp:=(F.launch H W hm k' tag hk hF hG C' (k:=k)).2 _ hx; have hl:= hp.1; let Z':=(U x); let M:=R.machine
    obtain ⟨h₁,h₂⟩:=M.passes hm F.turns; obtain ⟨hB,hΓ⟩:= h₁.closes _ hx _ (hr.gates Z L₀ (U x|>.beta) (U x|>.v))
    have ht : Z'=finish R₀ L₀ B (shelves (F.school H W k' tag) R₀ B) (branch t₀ R₀ L₀ B (X₀ x) γ) (Z'.beta) (Z'.v):=by
       unfold Z' Career.rea Return.result Template.install Template.trial board; simp only [A.B.bases]; rfl
    have hE: (Vp).eval=(A.B.a.clock.op m n).push (Q x).beta (Q x).eval:=by
       rw [← hl.ident]; funext i; rw [show U x= _ from ht];
       -- rewrite LHS after though changes U x inside? rw outside Voy reducibility
       exact (hr.unshifted ..).trans ((he.2 _ _ _).trans (((U₁ x hx|>.renew hG (A.B.support.cap N m hm.le) h₁.decent h₁.width γ (Return.enough_room A.B m n) (h₁.fees _ hx)).unshifted _ _ _ _ i).symm)) -- edit
    let R':= predictor A.B N Q x; let g:=X₀ x; have hδ : Z'.beta=R'+delta (t₀|>.read g):=rfl
    let Vv:=board A.B N (Return.ledger A.B N m n t₀ X₀); have hc: 0 < target Q x 1:=by
       change 0 < (A.B.a.clock.op m n).push (Q x).beta (Q x).eval 1; rw [← hl.ident]; exact lt_of_lt_of_eq (Real.exp_pos _) (Vv.trial_one (predictor A.B N Q) (x:=x) (d:= Averaging.delta (t₀|>.read g)) («v»:=Z'.v) (fun i=> hl.bundle.valid.labels.regular.at_flat _)).symm -- edit
    have h:=M.ring; obtain ⟨hL,hM⟩:= Return.grants A.B N F.forest C' O _ h M.bill hm F.turns (fun i hi=>F.atAtlas H W hm k' tag hk hF i hi C') (U₁) h₁.early
    obtain ⟨hk₀,hk₁⟩:= h₂ _ hx (F.turns _ hx).1 (F.turns _ hx).2 (Averaging.delta ((F.school H W k' tag).read g)) (F.barn H W k' tag) (F.tongue H W k' tag k x) hr (Averaging.delta_bound hG ((U₁ x hx).projects)) (fun i=> (he.2 _ _ i).trans (Return.splits_zero hG hm h₁ (U₁) hL hx hc i))
    have hV:= step_paid (A.B.a) m; have ht: W.crew H m ≤ CeilingExtent W.nextFloor (I):= (W.deep (J) (I) hV).trans (Coup.overhead _ hV)
    exact ⟨⟨hE,hk₁,⟨(congr_fun (congr_fun A.B.bases N) m).symm,rfl,rfl,⟨A.B.support.cap _ _ hm.le,hB⟩,hk₀⟩,hΓ, hp.1.δ⟩,hp.2.1,hp.2.2,(Career.currencies p (Price.grade (A₀) p) (he.1 _ _) ((A.B.a.fits.delayed m).le) (le_add_of_nonneg_right (Work.E04.shift_nonneg ..)) (Nat.mul_le_mul_right _ ht))⟩ -- order
end Career
end YM.PhysicalNext.Repeat.Mallow
