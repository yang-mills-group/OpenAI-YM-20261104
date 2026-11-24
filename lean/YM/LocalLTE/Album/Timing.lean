import YM.LocalLTE.Album.Ground
import YM.LocalLTE.Album.Level
import YM.LocalLTE.Key.Race
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

namespace Career
-- x physically. Tape choice. Avoid cancellation using arbitrary flags.
open Ovens Ovens.Pipes
open Collection.Price Progress.DirectedRecipe Refrain
variable (x:ℝ)(hx:x∈s)(J':Adorn H W) (hk:F.Accepts H k) (hF:∀ x∈s, Trail.Hired H W (Q x) tag)
local notation "R₀"=> A.B.kin.path N m
set_option quotPrecheck false
local notation "L₀"=> (A.B.a.params m).clip
local notation "Y₀"=> F.holds.latch x
local notation "V₀"=> (F.hearth H x)
local notation "f"=> F.daily H W k' tag k x
local notation "tap'"=> F.tap H W k' tag k x
local notation "τ"=>F.peeled H k x
local notation "e'"=>F.holds.base
local notation "P₀"=>F.porch H W k' tag
local notation "S₀"=>F.school H W k' tag
local notation "g"=>F.index H W k' tag k x
local notation "A'"=>F.barn H W k' tag
local notation "H₁" => F.tongue H W k' tag k x
local notation "Y₁"=> F.Voy H W k' tag k x
lemma pre_tap : F.tap H W k' tag k x= Trail.seasonal H W (F.hearth H x) (F.exhibit H x) tag k k':=by
    unfold Career.tap; rw [F.flowDaily, F.aloft]; rfl
include hm hF hk hx
lemma preAdd (U:Config G (A₀)):
    (Collection.frozen (posting B V₀) (R₀) L₀ B (Song.plusone (V₀) (Meadow.intern V₀) O γ) (Q (Y₀)).beta (Song.weighty V₀ O F.forest)).exponent U= (Collection.frozen S₀ (R₀) L₀ B (F.index H W k' tag k x) (Q x).beta τ).exponent U+∑' i,(tap').logarithm i U:=by
    let M:=F.hearth H x; let Ξ:=F.holds.latch x; let T' := Q Ξ; have hf:=(F.turns _ Ξ.2); obtain ⟨h,hP⟩:=hk x hx
    have ht:=F.indices H W k' tag (k:=k) x
    rw [ht.1,ht.2,F.pre_tap, ← show Q (F.holds.latch x)=Q x from (by rw [Embrasure.click _ x hx])]; exact W.soil_add H hm hf.1 hf.2 M (F.holds.honors Ξ) (hF _ Ξ.2) _ F.maps h hP k' F.forest _
variable (G':G.Simple)(hX: Trail.Keeps H (F.hearth H x) tag p k')
include G' J' hX
-- career scalar extraction.R
lemma postAdd (U:Config G (A₀)):
    ((F.Voy H W k' tag k x).exponent U)+(∑' i,(H₁).logarithm i U)=(Collection.frozen (F.school H W k' tag) (R₀) L₀ B (F.index H W k' tag k x) (Q x).beta τ).exponent U-γ*Collection.receipt R₀ L₀ B U:=by
    let Z:= (Y₁); let V':= A.B.a.clock.hatBeta m
    let d:= Averaging.delta (S₀|>.read g); let β:= Z.beta; let v:=Z.v
    have hv:= (F.accepted H W hm k' tag J' hk hF G' _ hx hX (Opera.forum A.B R.shape))
    have hp:= (R.machine.passes hm F.turns); have ht:= F.atLamp H W hm k' tag hk hF _ hx
    have hβ: β=(Q x).beta + γ + d:=rfl
    obtain ⟨i,j,u,he,-⟩:= (F.clockW H W hm k' tag J' hk hF G' x hx hX).1.pays
    have he₀:= Price.echo_add (A.B.support.cap N m hm.le) hp.1.width G' (Return.enough_room ..) hp.1.decent (F.school H W k' tag) g γ d (F.goals H W k' tag x) ht (Averaging.delta_bound G' ht.projects) β v U he.stamp.boundE
    rw [show Y₁=finish R₀ L₀ B A' H₁ β v from rfl, cruise_EX]; apply Eq.trans he₀
    rw [hβ, show v= Collection.vac (F.index H W k' tag k x) (F.peeled H k x) from hv.2.2.1]; exact ht.exponent G' (A.B.support.cap N m hm.le) hp.1.decent hp.1.width γ (Return.enough_room ..) _ _ _ -- edit
variable {b v₁ b₁ t q t₁ t₂ L₁ b₂ : ℝ}{n':ℕ}(TZ: Captain (F.hearth H x) (X.p.profile (A.B.a.clock.J m)).order t q v₁ t₁ L₁ b₂ t₂ b₁ b n' Chi.canonical)
include TZ
lemma closure (U:Config G (A₀)):
    let c:= (F.hearth H x); let a:= overhead (prism (ships A.B N m n) x₀ O (R.shape.o J I).K U F.forest) (Q Y₀) (R.target J I).table -- edit
    Real.exp ((F.Voy H W k' tag k x).exponent U)*Real.exp (∑' i,(tap').logarithm i U)*Real.exp (∑' i,(H₁).logarithm i U)= a * c.homesteadPool Chi.canonical U:=by
    intro c p; have ht:= F.preAdd H W hm k' tag x hx hk hF U; have hv:= F.postAdd H W hm k' tag x hx J' hk hF G' hX U
    have he:= Song.creditRing B V₀ (Meadow.intern (V₀)) O γ TZ F.forest rfl (Rain.jersey (A:=A) (m:=m)|>.1.le) (show (ships A.B N m n).down.Bounds (ships A.B N m n).low _ _ _ from A.B.support.cap N m hm.le) (F.holds.honors (Y₀)) U
    have hz: (Q x).beta=(Q Y₀).beta:=by rw [Embrasure.click _ x hx]
    rw [hz] at hv ht
    rw [← Real.exp_add,← Real.exp_add,add_right_comm,hv,sub_add_eq_add_sub,← ht]; exact he
end Career
end YM.PhysicalNext.Repeat.Mallow
