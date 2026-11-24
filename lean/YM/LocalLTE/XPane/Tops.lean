import YM.LocalLTE.XPane.Wings
import YM.LocalLTE.Rendezvous.Wings
import YM.LocalLTE.Album.Arbor
import YM.LocalLTE.Estate.Call

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

-- local secured reserve.T from overburn events. geometry spectra
open Coup Scarf Progress.DirectedRecipe
local notation "sR"=> W.crew H m*radiusB x₀
local notation "RB"=> (raiser B)
local notation "d!"=> F.panelX H W k' tag
local notation "e"=> Coup.freezes (G:=G) (D.L J) (X.p.profile I) H.w (Rain.lint R.target A m) x₀ (3*W.mass H m)
local notation "f3"=> Marlin.tithe (sR) (e) (raiser B) (ballCost (W.crew H m))

variable {ι:Type}[Fintype ι] (M:ι→Lotus.Leaf (Q (F.holds.latch x))) (rA:ι→ℝ)
open YM.Merge
set_option quotPrecheck false
variable {Γ:ℝ} (r:ℕ→ℕ→ℕ)(Z:ConcertZ R.target p Γ)(hM:Merchandise R.shape W.footprint W.ψ A.delay)
    (Gm:ℕ→ℕ→ℕ)(hh:ConcertZ.CalendarX R.shape r Z H.κ Gm A.delay) (hX:Trail.Keeps H (F.hearth H x) tag p k')
open YM.LocalLTE
local notation "A₁"=> A.B.a.S.side (m+1) n
local notation "P!"=> A.B.a.budget m
local notation "Yd"=> (Z.bbase J I)
local notation "dx"=> Z.amp J I
include hh
lemma courtyardX : 4*(Yd * radiusB x₀)< (A₀).val∧ East.stagnate (dx) ((R.target J I).halo) * radiusB x₀ < Yd*radiusB x₀:=by
    let hB:= (A.B.a.budget m); have he:= step_paid A.B.a m
    let a:= Z.bbase J I
    have hc:= hh.shells (J) (I) he
    let y:= (A.B.a.budget (m+1)).B
    have hp:32*(a*hB.B)< (A.B.a.S.side m n).val:=by
       let b:= A.delay; let Dz:= 1+hB.B+y
       refine lt_of_lt_of_le ?_ (A.B.valid.volume m n); change 32*(a*hB.B)< _ * Dz^b.growth J; let t:= A.delay.shells J; rw [← Nat.mul_assoc]; refine lt_of_le_of_lt (Nat.mul_le_mul_right hB.B ((Nat.mul_le_mul_left 32 (show a≤1+a from by omega)).trans hc)) (Nat.mul_lt_mul_of_pos_left ?_ ?_)
       · have hk:1≤b.growth J:= hh.growth _ _ he; have h:t= _:=show t=t from rfl; exact lt_of_lt_of_le (b:=Dz) (by unfold Dz; omega) (le_self_pow₀ (show 1≤ Dz from by unfold Dz; omega) (by omega))
       exact lt_of_lt_of_le (show 0<32*(1+a) from Nat.mul_pos (by norm_num) (by omega)) hc
    exact ⟨lt_of_le_of_lt (Nat.mul_le_mul_right _ (show 4 ≤ 32 by norm_num)) hp,Nat.mul_lt_mul_of_pos_right (Z.bill _ _ he|>.2.2.2.2) hB.B_pos⟩ -- positive
local notation "Yp'"=> betaF G x₀ L
local notation "nζ"=> (Z.kap J I)
local notation "eL"=> (Z.strength J I)
open Merge.Palette Overlay Marker
-- marker willingness.Momentum.Label.Any weights. 
variable (φ:ι→ Config G (A.B.a.S.side (m+1) n)→ℝ)(P':ι→Prop)
abbrev approvedX (m n:ℕ): East.stagnate (Z.amp (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) ((R.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).halo)*radiusB (A.B.a.clock.hatBeta m)<Z.bbase (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)*radiusB (A.B.a.clock.hatBeta m):= (Career.courtyardX H r Z Gm hh (n:=n) (m:=m)).2
-- The courtyard estimate supplies the radius bound in acceptedZ.
lemma acceptedX : 2*(2*(stagnate dx (R.target J I|>.halo)*radiusB x₀)) ≤ (A₀).val:=by
   have hx:= Career.courtyardX H r Z Gm hh (n:=n) (m:=m); omega
end Career
end YM.PhysicalNext.Repeat.Mallow
