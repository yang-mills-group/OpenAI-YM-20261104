import YM.LocalLTE.Georges.Wick
/-! Single-leaf transmit on varied τ window anchored at SAME Career, same ξ+ μ. -/
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
local notation "P₀"=>F.porch H W k' tag
local notation "S₀"=>F.school H W k' tag
local notation "g"=>F.index H W k' tag k x
local notation "A'"=>F.barn H W k' tag
local notation "H₁" => F.tongue H W k' tag k x
local notation "Y₁"=> F.Voy H W k' tag k x

-- local secured reserve.T from overburn events. geometry spectra
open Coup Scarf Progress.DirectedRecipe
local notation "sR"=> W.crew H m*radiusB x₀
local notation "RB"=> (raiser B)
local notation "d!"=> F.panelX H W k' tag
local notation "e"=> Coup.freezes (G:=G) (D.L J) (X.p.profile I) H.w (Rain.lint R.target A m) x₀ (3*W.mass H m)
local notation "f3"=> Marlin.tithe (sR) (e) (raiser B) (ballCost (W.crew H m))

variable (M: Lotus.Leaf (Q (F.holds.latch x))) (o: Site (A.B.a.S.side m n))(ho:o∈ M.crest.image (A.B.a.clock.op m n).ratio.parent)
variable (hR:Arrives R.shape A.delay)
-- open YM.Merge // use qualified for compatibility
set_option quotPrecheck false
variable {b v₁ b₁ t q t₁ t₂ L₁ b₂ w : ℝ}{n':ℕ}(TZ: Captain (F.hearth H x) (X.p.profile (A.B.a.clock.J m)).order t q v₁ t₁ L₁ b₂ t₂ b₁ b n' Chi.canonical)
    (h₇:Merchandise R.shape W.footprint W.ψ A.delay)
    (hp:Bikes (R.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (D.L (A.B.a.clock.J (m+1))) (R.shape.μ (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (A.B.a.clock.hatBeta m) (R.expense (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)|>.earn) w b₁ (X.p.profile (A.B.a.clock.J m)|>.order) n')
variable (hκ:Daisy.Herd (F.hearth H x) TZ.conduit L₁ b₁ n')
local notation "R1"=> (Q (F.holds.latch x))
local notation "fU"=> F.cords H x
local notation "m₀"=> canvasZ H F W k' tag x M k
local notation "c₀"=> waxA H F W k' tag x M k
local notation "S"=> A.B.a.clock.op m n
variable (G':G.Simple)(hX: Trail.Keeps H (F.hearth H x) tag p k')
variable {q':Signed}{y':Site (A.B.a.S.side m n)}
variable (π : (Q (F.holds.latch x)).activities.Moves q' ((A.B.a.clock.op m n).ratio.embed y'))
local notation "b₀"=> Merge.dart π (F.hearth H x) F.holds.base (F.cords H x)
-- aim reuse hT.trans hp.early.
lemma tenet : ∃ Y': Progress.DirectedRecipe.Layout d! q' y', Y'.Follows tap' ∧ Y'.hard=b₀:=by
    let W0:= F.folio H k x
    let R' := (P₀).read W0; have hz:R'=Refrain.read F.holds.base (F.cords H x) O (P₀).reg W0.logRead:=rfl
    let a:= W.crew H m*radiusB x₀
    have hk : Nonempty (R'.Moves q' y'):=by
       unfold R' W0; rw [F.menuX H W k' tag x, F.aloft]; exact Trail.beads H W (F.hearth H x) k' tag q' y'
    obtain ⟨hP⟩:= hk; obtain ⟨e',he⟩: (∃ e': R'.Moves q' y',e'.kp=b₀):=by rw [hz]; exact Merge.depart π V₀ O F.holds.base (F.cords H x) _ _ (by apply Nonempty.some; rw [←hz]; exact ⟨hP⟩)
    obtain ⟨J'⟩: Nonempty (((d!).pours tap').Moves q' y'):= Marlin.reeds (P₀) a a W0 (F.dapple H k x) (f) q' y' hP
    obtain ⟨s,hs,hq⟩:=Marlin.gander P₀ a a W0 (F.dapple H k x) (f) q' y' hP
    rw [← he]; exact YM.Merge.courier e' J' rfl rfl s hs hq
include J' hm hx hk hF G' hX
lemma driftV : ∃ ρ:(Y₁).activities.Moves q' y',∀ (M: Lotus.Leaf (R1))(t:ℝ)(i:ℕ) (U), waxA H F W k' tag x (M.route π) k t (ρ.kp i) U= waxA H F W k' tag x M k t i (pull q' y' U):=by
    obtain ⟨f',h,hp⟩:= F.tenet H W k' tag x (k:=k) π
    let m₀':= f'.motion (Marlin.hak (d!)) B h
    have hh:= (F.clockW H W hm k' tag J' hk hF G' x hx hX).1; obtain ⟨p₁,c,hd,he,hF⟩:= hh.pays -- order edit
    let ht:= he -- he is Kiln? inspect
    obtain ⟨Z,hZ,hM⟩: ∃ Z: Progress.DirectedRecipe.Layout A' q' y', Z.Follows H₁ ∧ Z.hard=m₀'.kp :=by
       obtain ⟨q,hQ,hb⟩:= he.carries q' y'
       exact Merge.courier m₀' (he.stamp.moves q' y').some rfl rfl q hQ hb -- edit
    let Y':= Z.inflate; refine ⟨Progress.DirectedRecipe.Layout.motion Y' (Progress.DirectedRecipe.folio G _) (B) (Z.inflates _ hZ),fun M t i U=>?_⟩ -- folio shadow
    have ha(j:ℕ)(V):canvasZ H F W k' tag x (M.route π) k t (Z.hard j) V=canvasZ H F W k' tag x M k t j (pull q' y' V):=by
       rw [hM]; exact Merge.ticket f' h (veranda M V₀ O F.holds.base (F.cords H x) t) (veranda (M.route π) V₀ O F.holds.base (F.cords H x) t) (by intro i U;rw [hp]; exact Merge.egress M π V₀ O U t F.holds.base (F.cords H x) i) (Marlin.hak (d!)) j V
    exact Merge.ticket Y' (Z.inflates _ hZ) _ _ (fun i U=> Merge.inflate_ticket Z _ _ ha i U) (Progress.DirectedRecipe.folio G _) i U
end Career
end YM.PhysicalNext.Repeat.Mallow
