import YM.LocalLTE.Fabric.Glass
import YM.LocalLTE.Fabric.Birth
import YM.LocalLTE.Bonnet.Quiet
import YM.LocalLTE.Fabric.Priced
import YM.LocalLTE.Rate.Permit
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
variable {R₁:Rep G (A.B.a.S.side (m+1) n)}
    (hV: Lives A.B.bake N (m+1) n R₁)(hx:R₁.beta∈ band A.B.a (m+1))
    (U: Guide A.B R.shape N m n R₁) (hU:Opera.Price A.B R.shape N m n R₁ U)
-- Career lift. uniform Θ with Horites
variable (k':ℕ) (tag:ℕ→ℕ)
namespace Career
set_option quotPrecheck false
local notation "Ω"=> F.holds.base
local notation "ℒ"=> East.lectures (Ω) p H.w.ℓ tag
local notation "Y"=> F.holds.doors
local notation "d'"=> W.crew H m*radiusB x₀
abbrev pantry (f:ℕ→ℕ) (k':ℕ):= vested where vested:= East.locker (F.holds.base) (East.lectures (F.holds.base) p H.w.ℓ f) k'
abbrev porch := Scarf.diamond (F.holds.doors) (Trail.vested (p:=p) H (F.holds.base) tag k') d'
abbrev panelX := Marlin.lodge (F.porch H W k' tag) d' d'
abbrev school := Marlin.pluck B (F.panelX H W k' tag)
-- X.frost
local notation "He'" x=> F.hearth H x
local notation "c'" x=> F.cords H x

def daily (k:ℕ)(x:ℝ) := Scarf.hesitates B (F.holds.doors) (Trail.vested (p:=p) H (F.holds.base) tag k') d' z (F.folio H k x) (F.wilt H k x) (F.dapple H k x)
def tap (k:ℕ) (x:ℝ):=Marlin.bison (F.folio H k x) (F.dapple H k x) (F.daily H W k' tag k x)
def index (k:ℕ)(x:ℝ):= Marlin.poursP B (F.panelX H W k' tag) (F.tap H W k' tag k x)
lemma tables (x:ℝ) : F.holds.doors = Beam.marquee (He' x) B ∧ F.pantry (p:=p) H tag k'= Trail.vested (p:=p) H (He' x) tag k':= by
    let y:= F.holds.latch x
    have hv := (F.turns a F.holds.he).1.path.trans (F.turns _ y.2).1.path.symm; have hp:= F.wave.reg _ F.holds.he _ y.2; have hk:= F.wave.forced _ F.holds.he _ y.2
    exact ⟨Meadow.signageN (H:=F.holds.base) («I»:= F.hearth H x) hv hp hk (B),(East.literal_cal Ω (c' x) (F.holds.agrees _) k' p H.w.ℓ hv hp hk tag).2⟩
lemma menuX (x:ℝ): F.porch H W k' tag=Trail.lobby H W (He' x) tag k':= by unfold porch; obtain ⟨h,hX⟩:= tables H F k' tag x; rw [h, show Trail.vested (p:=p) H Ω tag k'=Trail.vested (p:=p) H (He' x) tag k' from hX]

lemma tableX (x:ℝ): F.panelX H W k' tag= W.bindZ H (He' x) tag k':= by unfold Career.panelX; rw [F.menuX H W k' tag x]; rfl -- rw menu x arg
lemma aloft (x:ℝ) : F.folio H k x = Meadow.timbresN (Meadow.intern (He' x)) («χ»:= O) γ H.w.ℓ k:= by
    let y:= F.holds.latch x
    exact Meadow.writtenN O (c' x) (F.holds.agrees _) ((F.turns a F.holds.he).1.path.trans (F.turns _ y.2).1.path.symm) (F.wave.reg _ F.holds.he _ y.2) (F.wave.forced _ F.holds.he _ y.2) γ k H.w.ℓ

local notation "R!" x=> (F.exhibit H x)
lemma flowDaily (x:ℝ): F.daily H W k' tag k x=Trail.sense H W (F.hearth H x) (F.exhibit H x) tag k k':= by
    obtain ⟨hz,hK⟩:= F.tables H k' tag x; unfold Career.daily; rw [hz, show Trail.vested (p:=p) H Ω tag k'= Trail.vested (p:=p) H (He' x) tag k' from hK, F.aloft, (F.identity H k x).1]; rfl
lemma indices (x:ℝ) : F.school H W k' tag=Trail.jerseyX H W (F.hearth H x) tag k'∧ F.index H W k' tag k x= W.nations H (He' x) (F.exhibit H x) tag k k':=by
    have he:= F.tableX H W k' tag x
    refine ⟨congr_arg (Marlin.pluck B) he,?_⟩
    unfold Career.index Career.tap; rw [he, flowDaily, F.aloft]; rfl

include hm
lemma curtainX (tag:ℕ→ℕ)(p:ℕ)(hX:IsCompact s): ∀ᶠ i:ℕ in atTop,∀ x∈s, Trail.Keeps H (He' x) tag p i:= by
     have he:= Yearling.hearthcast R.pledging.conducts F.holds F.turns F.wave R.inn.year R.pledging.range hm
     have ht (x:ℝ):= Rain.twined R.pledging hm F.holds F.turns R.inn x
     let w:= betaF G x₀ (D.L J) ^H.w.q; have hy:0<w:= Real.rpow_pos_of_pos (zero_lt_one.trans_le (H.vote.cash _ _ (step_paid A.B.a m)|>.2 _ (A.B.valid.pays m)|>.light.1)) _
     filter_upwards [Meadow.cashier (Z:=posting B Ω) (fun i=>(Beam.rewrite_rule Ω B i).symm) B (East.dicta Ω tag p H.w.ℓ) hX (East.lambent Ω tag p H.w.ℓ) he (fun x hx=> ⟨_,_,ht x⟩) w hy] with i h x hx
     let Y₀:= F.holds.latch x; have h₁:= F.tables (p:=p) H i tag x; have hp := (F.turns a F.holds.he).1.path.trans (F.turns _ Y₀.2).1.path.symm; have hv:=East.renew («γ»:=A.B.kin.alpha N m) Ω O tag p H.w.ℓ i (c' x) (F.holds.agrees _) hp (F.wave.reg _ F.holds.he _ Y₀.2) (F.wave.forced _ F.holds.he _ Y₀.2)
     specialize h x hx; unfold Trail.Keeps; rw [← hv,h₁.1.symm]; exact h
end Career
end YM.PhysicalNext.Repeat.Mallow
