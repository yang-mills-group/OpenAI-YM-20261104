import YM.LocalLTE.Bonnet.Tower
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Graces.Eagles
/-!
 Career:X curves yielding literal SAME representations.
 Native `Guide U x` bids vary at x.We compare layout uphill. Records intrusive.
-/
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
structure Funding (p:ℕ)(η:ℝ) where
  α : ℝ
  w : Wind p α
  κ : ℝ
  d : ℕ→ℕ→ℝ
  paid : ∃ y, Reliable G κ y
  vote : Spoke D R.shape w A.post κ d A.delay
  due : Urns.Balance D A.post A.delay p w.e η
variable {R} {ε : ℝ} (H:Funding R p0 ε)
local notation "Wf"=> H.w
structure Career (N m n:ℕ) (s:Set ℝ) (a:ℝ)(Q:UVNext.CouplingReset.In A.B.a m n) where
  wave: Curve (A.B.a.budget (m+1)) Q s
  turns : ∀ x∈s,Lives A.B.bake N (m+1) n (Q x)∧ (Q x).beta∈band A.B.a (m+1)
  holds : Roof.Embrasure (U:=A) (Y:=R.shape) (N:=N) (n:=n) Q s a
  aura (b: band A.B.a (m+1)): Expose (A:=A) (R:=R.shape) H.w b.val N m
  maps : Maps (A:=A) (C:=R.target) H.w m N
  forest : Return.Wood A.B m n
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
namespace Career
abbrev codec (x:ℝ) := Rain.noteX F.holds F.turns x
abbrev exhibit (x:ℝ) := F.aura (F.codec H x)
abbrev hearth (x:ℝ):= F.holds.houses (F.holds.latch x)
abbrev cords (x:ℝ):= F.holds.sister (F.holds.latch x)
abbrev dors := F.holds.doors
abbrev spine := Marlin.lodge (F.dors H) z (2*z)
abbrev issue := Marlin.pluck B (F.spine H)
local notation "Q₀" => (fronts (m:=m) (A:=A) (C:=R.target) H.w)
def impression (x:ℝ)(k:ℕ):= (F.exhibit H x).read H.w k
def folio (k:ℕ)(x:ℝ) := Meadow.timbresN (F.cords H x) (χ:=O) γ H.w.ℓ k
def dapple (k:ℕ) (x:ℝ): Offer G (A₀):= ornament Q₀ (F.impression H x k)
def wilt (k:ℕ)(x:ℝ): Offer G (A₀):= insightN B (F.cords H x) γ k Q₀ z (F.impression H x k) H.w.ℓ
def taped (k:ℕ)(x:ℝ) := Marlin.bison (F.folio H k x) (F.dapple H k x) (F.wilt H k x)
def plated (k:ℕ)(x:ℝ):= Marlin.poursP B (F.spine H) (F.taped H k x)
def peeled (k:ℕ)(x:ℝ):= Urns.tattoo H.w (F.hearth H x) F.forest k

lemma identity (k:ℕ)(x:ℝ) :
    let y:= F.holds.latch x; let _a:=Q y; let H':=F.hearth H x
    let fa:=F.impression H x k; let X':=F.exhibit H x
    F.wilt H k x = YM.LocalLTE.Patch.failure B Q₀ z fa H' γ H.w.ℓ k ∧
    F.spine H = YM.LocalLTE.Patch.marked B H' z ∧
    F.taped H k x = YM.LocalLTE.Patch.deposit B Q₀ z fa H' γ H.w.ℓ k ∧
    F.issue H=stock H.w H'∧ F.plated H k x=reads H.w H' X' k:= by
  intro y a' H' fa X'; let b:=F.holds.base; let V:= F.cords H x
  have hO:= F.holds.agrees y; have hv:= (F.turns a F.holds.he).1.path.trans (F.turns _ y.2).1.path.symm; have hp:= F.wave.reg _ F.holds.he _ y.2; have hk:= F.wave.forced _ F.holds.he _ y.2
  have hz:= Meadow.signageN (H:=b) («I»:=H') hv hp hk (B)
  have hs:F.spine H=YM.LocalLTE.Patch.marked B H' z:= congr_arg (fun y=> Marlin.lodge y z (2*z)) hz
  have hh:F.wilt H k x=YM.LocalLTE.Patch.failure B Q₀ z fa H' γ H.w.ℓ k := by
    have hp:= Meadow.watts (H:=b) V hO hv hp hk (B) k H.w.ℓ γ
    unfold Career.wilt Trio.insightN; rw [show Trio.earnedN B _ γ k H.w.ℓ=_ from hp]; rfl
  have he:F.taped H k x=YM.LocalLTE.Patch.deposit B Q₀ z fa H' γ H.w.ℓ k:=by
    unfold Career.taped Career.folio; rw [hh,show Meadow.timbresN _ _ _ _=_ from Meadow.writtenN O V hO hv hp hk γ k H.w.ℓ]; rfl
  refine ⟨hh,hs,he,congr_arg (Marlin.pluck B) hs,?_⟩; unfold Career.plated; rw [hs,he]; rfl
variable (hm:m<N)
include hm
def Accepts (k:ℕ):= ∀ x∈s, Meadow.Budget B (Beam.marquee (F.hearth H x) B|>.reg) (Meadow.ash (F.hearth H x) O H.w.ℓ k γ) s₀∧(F.exhibit H x).Yields H.w k
set_option maxHeartbeats 300000 in
lemma horizon (h:IsCompact s) :∀ᶠ k in atTop,F.Accepts H k:=by
  have hi:= step_paid A.B.a m; let b:= F.holds.base; let y:= F.holds; have he:= Yearling.hearthcast R.pledging.conducts F.holds F.turns F.wave R.inn.year R.pledging.range hm
  have ht x:= Rain.twined R.pledging hm F.holds F.turns R.inn x; have hK:= R.machine.passes hm F.turns|>.1; have h₀:= A.B.valid.pays m; have hs:= R.pledging.agenda _ _ hi|>.1; have hu:= Urns.rebates H.w hm R.inn H.vote R.pledging.peak R.pledging.jewels hK.decent hs R.pledging.conducts.full F.aura
  let u:= betaF G x₀ (D.L J) ^ H.w.q; have hg: 0<u:= Real.rpow_pos_of_pos (zero_lt_one.trans_le (H.vote.cash _ _ hi|>.2 _ h₀|>.light.1)) _
  filter_upwards [Meadow.cashier (Z:=posting B b) (fun i=>(Beam.rewrite_rule b B i).symm) B (Meadow.debrisN F.holds.base H.w.ℓ) h (Meadow.dissolvedN F.holds.base) he (fun x hx=> ⟨_,_,ht x⟩) u hg,hu] with k hV hh x hx -- A marker
  refine ⟨?_,hh (F.codec H x)⟩; let t:= y.latch x; let a':=Q t; let H':=F.hearth H x
  have hp := (F.turns a F.holds.he).1; have ha:=(F.turns _ t.2).1; have hv:=(F.holds.agrees t); have hE:= F.wave.reg a F.holds.he t t.2; have hW:= F.wave.forced _ F.holds.he _ t.2
  have hf: Meadow.Budget B (Beam.marquee H' B).reg (Meadow.sortable H' O H.w.ℓ k γ) u:= by
    rw [← Meadow.signageN (H:=b) («I»:=H') (hp.path.trans ha.path.symm) hE hW]
    rw [Meadow.abounds (H:=F.holds.base) («I»:=H') O (F.cords H x) hv (hp.path.trans ha.path.symm) hE hW]; exact hV _ hx
  exact Urns.polished H.w hm R.inn H.vote R.pledging.peak R.pledging.jewels hK.decent hs R.pledging.conducts.full (A.B.a.S.oneStep m n).exact_size H' (y.honors t) k hf
variable (hG:G.Simple)
include hG
lemma ascend (hP:F.Accepts H k)(x:ℝ)(hx:x∈s)(k':Return.Bookings A.B m n R.walls):
    Firings H.w F.maps (F.hearth H x) (F.exhibit H x) R.scout H.κ (H.d J I) k R.rider F.forest k':=by
  obtain ⟨he,hA⟩:=hP x hx; let y:=F.holds.latch x; let b:= F.hearth H x; have hz:=F.turns _ y.2; let X':= F.exhibit H x; let q:= reads H.w b X' k; let p₀:=tattoo H.w b F.forest k
  have hu:= Urns.charged R.pledging hm H.w R.inn H.vote R.floor (R.settles _ _) F.maps hz.1 hz.2 b (F.holds.honors y) X' k he hA
  have hp:Return.atlas A.B N F.forest k' Chi.canonical (radiusW R.rider) (Q y.val) (stock H.w b) q p₀:= (Return.earnings A.B N F.forest k' O (radiusW R.rider) R.machine.ring R.machine.bill hm _ hz.1 hz.2).2.2.symm.trans (funext fun i=> Urns.flowing R.pledging hm H.w R.inn H.vote hz.1 hz.2 b (F.holds.honors y) X' k he F.forest i)
  have hh:= R.machine.run (l:=Set.univ) (Q:=fun _=>Q y) (τ:=fun _=>p₀) hm (fun _ _=>hz) hG F.forest k' Chi.canonical (fun _ _=>hp) (fun _ _=>hu) (Urns.aware (B) hu) (uniform_curve (A.B.a.budget (m+1)) (Q y)) |>.2 (0:ℝ) (Set.mem_univ _)
  exact ⟨hp,hu,Urns.tollgate R.pledging hm H.w hz.1 hz.2 b (F.holds.honors y),Urns.authority R.pledging hm H.w H.paid.choose_spec R.inn H.vote R.floor (R.settles _ _) _ hz.1 hz.2 b _ k he hA,hh.1,hh.2.1,hh.2.2.2.2⟩
end Career
end YM.PhysicalNext.Repeat.Mallow
