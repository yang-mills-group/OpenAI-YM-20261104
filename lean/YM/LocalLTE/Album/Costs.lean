import YM.LocalLTE.Album.Timing
import YM.LocalLTE.Album.Riser
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

-- local secured reserve.T from overburn events. geometry spectra
open Coup Scarf Progress.DirectedRecipe
local notation "sR"=> W.crew H m*radiusB x₀
local notation "RB"=> (raiser B)
local notation "d!"=> F.panelX H W k' tag
local notation "e"=> Coup.freezes (G:=G) (D.L J) (X.p.profile I) H.w (Rain.lint R.target A m) x₀ (3*W.mass H m)
local notation "f3"=> Marlin.tithe (sR) (e) (raiser B) (ballCost (W.crew H m))
include hm hk hF hx
-- Marlin.1.Spending: fanning.
lemma memories : Vapor (F.panelX H W k' tag) tap' (raiser (raiser B)) (f3) ∧ 0≤ f3∧ f3 ≤ Real.exp (ballCost (W.crew H m))* betaF G x₀ L^(-(1/8):ℝ):=by
    let ℓ:= W.crew H m*radiusB x₀; obtain ⟨hz,hB⟩:= hk x hx; let W':=(F.hearth H x)
    let t:= f; let X':= P₀; let g':= F.folio H k x; have hp:=F.turns _ (F.holds.latch x).2
    have he i: Trio.Tidy B (neighbors (sR) i) (F.daily H W k' tag k x i)∧ (∀ V, t i V≠0→¬ Healthy (B).threshold (neighbors ℓ i) V)∧ ∀ V,‖t i V‖ ≤ e:= by
       unfold t; rw [flowDaily]; exact W.hosts H hm hp.1 hp.2 (F.hearth H x) (F.holds.honors _) (hF _ (F.holds.latch x).2) (F.exhibit H x) F.maps hz hB _ _
    have h i:= estateP X' ℓ ℓ g' (F.dapple H k x) (f) (fun i=>(he i).1) i
    have hK:0 ≤ e:= (norm_nonneg _).trans ((he 0).2.2 1)
    have hh: Vapor (F.panelX H W k' tag) tap' (raiser (raiser B)) (f3) := by
       refine ⟨fun i=>(h i).uses,fun i U hx=> ?_,fun i=> (h i).invariant,fun i=>(h i).borel, ?_⟩
       · exact not_not.mp (fun h'=> Marlin.failedP X' ℓ ℓ g' _ t (fun i=> (he i).2.1) i U h' hx)
       refine ⟨_,Marlin.caps _ _ _ _ _ hK (fun i=> ?_),Marlin.softly g' t _ (fun i=> (he i).2.2) (F.dapple H k x)⟩; exact_mod_cast Scarf.standing (ℓ) (B) (W.crew H m) i le_rfl
    have hv:0 ≤ f3:= by obtain ⟨v,hp,-⟩:=hh.funds; exact budget_nonneg (hp.2 0)
    refine ⟨hh,hv,?_⟩
    have hz: Marlin.tithe sR (e) B (ballCost (W.crew H m):ℝ) ≤ betaF G x₀ L^(-(1/8):ℝ):= by unfold Marlin.tithe; rw [Rain.jersey (m:=m) (A:=A)|>.2.2.1]; exact (Trail.earned H W (m:=m)).frost
    apply le_trans _ (mul_le_mul_of_nonneg_left hz (Real.exp_pos _).le)
    unfold Marlin.tithe; rw [show (raiser B).supportExponent+1+1=(B).supportExponent+1+1+1 from rfl,add_mul,one_mul,Real.exp_add]; apply le_of_eq; ring
local notation "α"=> A.B.a.params m
local notation "Δ₀"=>Averaging.delta ((F.school H W k' tag).read (F.index H W k' tag k x))
local notation "fT"=> Merge.Spicy.opens G B L₀ (α).width (α).paths γ (Time.forecastE A.B.a m)+Real.exp (ballCost 2:ℝ)* Price.lofty B G (α).width (α).paths γ Δ₀
variable (G':G.Simple)
include G'
lemma canopied : Vapor (F.barn H W k' tag) H₁ (raiser B) fT :=by
    have ht:=(R.machine.passes hm F.turns)
    exact Price.paladin (A.B.support.cap N m hm.le) ht.1.width G' (Return.enough_room ..) ht.1.decent (F.school H W k' tag) g (F.atLamp H W hm k' tag hk hF x hx) -- edit
include J'
local notation "S1"=> X.p.profile I
local notation "f₀"=> Merge.Spicy.opens G B (X.p.profile I).clip (X.p.profile I).width (X.p.profile I).paths γ (Time.credit G S1*δE x₀)
lemma leafT : 0 ≤ fT∧ fT ≤ (f₀)+Real.exp (ballCost 2:ℝ)*(W.hop H m*betaF G x₀ L^(chip 0)):= by
    have hy:=F.canopied H W hm k' tag x hx hk hF G'; obtain ⟨u,hu,-⟩:= hy.funds
    refine ⟨budget_nonneg (hu.2 0),?_⟩
    have h:=params_eq A.B.valid m; have hp:= Price.Colors.dew (J'.canopy _ _ (step_paid A.B.a m) _ (A.B.valid.pays m)) B (h ▸ (⟨rfl,rfl,rfl⟩:Time.Same (A.B.a.params m) (B))) rfl rfl Δ₀ γ (Averaging.delta_bound G' (F.atEarn H W hm k' tag hk hF x hx).projects) ((Boulevard.coupling A N m hm).trans (le_abs_self _))
    have he:Time.forecastE A.B.a m=Time.credit G S1*δE x₀:=by unfold Time.forecastE; rw [h]; rfl
    rw [h,he]; apply add_le_add_right (mul_le_mul_of_nonneg_left hp (Real.exp_nonneg _)) _ -- edit
end Career
end YM.PhysicalNext.Repeat.Mallow
