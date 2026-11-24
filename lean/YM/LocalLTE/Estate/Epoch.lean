import YM.LocalLTE.Crafts.Bands
import YM.LocalLTE.Newborn.Contract
import YM.LocalLTE.Estate.Wake
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
variable {p:ℕ}(W:Trail H p)(M:Preview H)(v:Bolt A)(hv:Made H W M v)
open Progress.DirectedRecipe Averaging LocalLTE.FrameBox Price
namespace Career
variable (k':ℕ)(R' R'': Rep G (A.B.a.S.side (m+1) n))
local notation "tag'"=> Mallow.spread A.B.a N p n (m+1)
local notation "t₀"=> F.school H W k' tag'
set_option quotPrecheck false
abbrev powerEntry (a:ℕ)(y:ℕ→ℕ)(G:Gauge){c:Side}(R:Rep G c) := { R with activities:= {R.activities with E:=fun i=> if y i ≤ a then R.activities.E i else 0, K:=0}, v:=0 }
def disc (j:ℕ) := let f:= Mallow.spread A.B.a N p n (m+1); let E':=powerEntry j f G R'; let s:= (F.holds.base); Sum.elim (Song.choir (East.way (W.lease H m j) s f Chi.canonical p H.w.ℓ k' j H.κ E') ∘ Song.pennant s) (Song.choir (Urns.penned (n:=n) H.w F.maps (H.d J I) H.κ (gStep R'.beta) j)) ∘ Marlin.leanU (A₀)
lemma catalog (j:ℕ)(hr:R''.path=R'.path)(hp:R''.beta=R'.beta)(h:∀ i,tag' i ≤ j → R''.activities.E i= R'.activities.E i) : F.disc H W k' R'' j= F.disc H W k' R' j:=by
    let U:=powerEntry j tag' G R'; let Z:=powerEntry j tag' G R''; have h' i (hi:tag' i≤ j):Z.activities.E i= U.activities.E i:=by unfold Z U powerEntry; dsimp only; rw [if_pos hi,if_pos hi]; exact h i hi
    unfold disc; rw [hp]; exact congr_arg (fun M=> Sum.elim (Song.choir M ∘ pennant F.holds.base) _ ∘ Marlin.leanU (A₀)) (East.shield (χ:=Chi.canonical) (F.holds.base) (κ:=H.κ) p H.w.ℓ k' j (W.lease H m j) Z U hp hr _ h')
lemma sav (j:ℕ)(x:ℝ)(hx:x∈s) : F.disc H W k' (Q x) j= F.fruits H W k' tag' x j:=by
   let y:=(F.holds.latch x).1; let Y:=Q y; let D:= (F.hearth H x); let E':= powerEntry j tag' G Y
   have he:y=x:=congr_arg Subtype.val (Embrasure.click F.holds _ hx); have hh:Y.path=(Q a).path:= (F.turns _ (F.holds.latch x).2|>.1.path).trans ((F.turns _ F.holds.he).1.path).symm
   have hz:(Q x).beta=(F.codec H x).val:= (congr_arg (fun i=> (Q i).beta) he).symm
   let f:= F.holds.base; have h':Trail.histogram H W (F.hearth H x) tag' k' j= Song.choir (East.way (W.lease H m j) f tag' Chi.canonical p H.w.ℓ k' j H.κ E') ∘ pennant f:=by
       let A:=F.holds.latch x; have ht:= East.reproduce (K':=F.hearth H x) (κ:=H.κ) (W.lease H m j) f tag' Chi.canonical p H.w.ℓ k' j hh (F.wave.reg _ A.2 _ F.holds.he) (F.wave.forced _ A.2 _ F.holds.he)
       refine ht.trans (congr_arg (fun V=> Song.choir V ∘ pennant f) (East.shield f p _ _ j _ Y E' rfl rfl tag' (fun i hi=> (if_pos hi).symm)))
   unfold disc Career.fruits; rw [hz,h']; dsimp only; rw [show powerEntry j tag' G (Q x)=E' from congr_arg (fun i=> powerEntry j tag' G (Q i)) he.symm]; rfl
end Career
end YM.PhysicalNext.Repeat.Mallow
