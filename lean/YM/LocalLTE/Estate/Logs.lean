import YM.LocalLTE.Crafts.Bands
import YM.LocalLTE.Newborn.Contract
import YM.LocalLTE.Estate.Epoch
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
-- Direct calculator.P.Output Consumer without substitution of actual.V into evaluator; needs input V and Pilot λ etc.
def chipK (j:ℕ):= delta ((F.school H W k' tag').read (Price.emp (F.disc H W k' R' j)))
def forecastV (j:ℕ):= Price.merits (A.B.a.params m) (A.B.kin.path N m) B t₀ (F.disc H W k' R') γ (F.billow H W k' tag') H.κ j
lemma fcast (j:ℕ)(x:ℝ)(hx:x∈s) : F.goals H W k' tag' x j=F.forecastV H W k' (Q x) j:=by
    unfold Career.goals forecastV Price.merits; rw [sav H F W k' j x hx]
local notation "X'"=> F.barn H W k' tag'
local notation "V!" x=>F.Voy H W k' tag' k x
-- calculator *unmarked* interaction.Draw counts.Rearray can zero t.A. β includes true x.W.Price.P projections capture affine/halo deterministic. No future beta! Use for slots. j section.
def proposals (j:ℕ): Config G (A₀)→ ℝ := stuff (Rack.upE X') (fun i=> if Price.pocket (A₀) p i≤p then Song.choir (fun v: Fin (p+2) × EKey (A₀) => if v.1.val=0 then F.forecastV H W k' R' 0 v.2 else F.forecastV H W k' R' v.1.val v.2-F.forecastV H W k' R' (v.1.val-1) v.2) (numbering (Price.Rol p A₀) i) else 0) j
lemma sees (x:ℝ)(hx:x∈s) (i:ℕ)(ht:Price.pocket (A₀) p i ≤ p) :
   (F.proposals H W k' (Q x) (Rack.upE (F.barn H W k' tag') i))=(F.Voy H W k' tag' k x).activities.E (Rack.upE (F.barn H W k' tag') i):=by
   let P:= F.barn H W k' tag'; let u:= Rack.upE (P); let u₁:= numbering (Price.Rol p A₀) i; let s:= u₁.1; let v:= u₁.2; let j:= v.1.val
   have hp:j ≠ p+1:= by change j ≤ p at ht; omega
   unfold proposals; rw [stuffed u, if_pos ht,show (V! x).activities.E (Rack.upE (X') i)=_ from (stuffed u (F.tongue H W k' tag' k x|>.regular) i)] -- edit val
   let f:= F.forecastV H W k' (Q x); change Rim (A₀) • ((if j=0 then f 0 v.2 else f j v.2 - f (j-1) v.2) ∘ s.view)= Rim (A₀) • (Price.stairs p _ (F.goals H W k' tag' x) j v.2 ∘ s.view); unfold stairs; rw [if_neg hp]; split; rw [F.fcast H W k' _ x hx]; rw [F.fcast H W k' j x hx,F.fcast H W k' (j-1) x hx]; rfl
lemma uplink (x:ℝ)(hx:x∈s)(i:ℕ): F.proposals H W k' (Q x) i=if Price.grade (A₀) p i≤ p then (F.Voy H W k' tag' k x).activities.E i else 0:=by
    let t:= Rack.upE X'; by_cases hp:i∈ Set.range t; swap
    · split; unfold proposals; rw [blank _ _ hp]; exact (blank t _ hp).symm; exact blank _ _ hp
    obtain ⟨i,rfl⟩:= hp; rw [show Price.grade (A₀) p (t i)= Price.pocket (A₀) p i from ?_]; swap; · unfold t Rack.upE Price.grade; simp only [Progress.DirectedRecipe.book]
    split
    next h=> exact F.sees H W k' x hx i h
    next h=> unfold proposals; rw [stuffed, if_neg h] -- edit binder
end Career
end YM.PhysicalNext.Repeat.Mallow
