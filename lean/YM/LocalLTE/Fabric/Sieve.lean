import YM.LocalLTE.Fabric.Cloak
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
-- Career lift. uniform Θ with Horites
variable (k':ℕ) (tag:ℕ→ℕ)
namespace Career
set_option quotPrecheck false
local notation "Ω"=> F.holds.base
local notation "ℒ"=> East.lectures (Ω) p H.w.ℓ tag
local notation "Y"=> F.holds.doors
local notation "d'"=> W.crew H m*radiusB x₀
local notation "V"=> F.holds
local notation "L'"=> D.L J
local notation "Z₀"=>Trio.resize H.w.ℓ (Rain.lint R.target A m)
local notation "Q₀"=> (fronts (m:=m) (A:=A) (C:=R.target) H.w)
local notation "p₀"=> (F.plated H k)

-- ORIO clauses individually. Compatible moves on enlarged D.Falls converge on THIS Q.
open Progress.DirectedRecipe
include hm
lemma toneReady : Compared F.holds.doors (B) (F.folio H k) s ∧ (∀ i:Site A₀, Shingle.Mild B (neighbors z i) (fun x=> F.dapple H k x i) s) ∧ ∀ x∈ s,∀ i:Site A₀,Varies (fun y=> F.wilt H k y i) x s:=by

  let P:= B
  let g (x:ℝ):= F.impression H x k; let b x:=F.dapple H k x; let f x:=F.wilt H k x; let t (x:ℝ):=F.folio H k x; let L:= yside (C:=R.target) (m:=m) (A:=A) H.w
  let p:= R.pledging; have he:=step_paid A.B.a m; have hh:=Yearling.hearthcast R.pledging.conducts F.holds F.turns F.wave R.inn.year R.pledging.range hm
  let a (i:ℕ):=(pennant F.holds.base i).2∉Meadow.bouquetN F.holds.base H.w.ℓ k
  have hT:= F.wave.beta.congr (show ∀ x∈s,(F.codec H x).val=(Q x).beta from fun x hx=>by change (Q (V|>.latch x)).beta=_; rw [Embrasure.click _ x hx])
  have hp:=(R.machine.passes hm F.turns).1.decent
  have hc:=p.agenda _ _ he|>.1
  have hz(i:Stars)(j: Site (L i)): Shingle.Mild P univ (fun x=> g x i j) s := Urns.versed H.w hm R.inn p.jewels hp hc p.conducts.full _ i (F.codec H) hT j
  have hY: tent Z₀ (radiusB x₀)+4≤ z:= by unfold Trio.base; omega
  have hf (i:Site A₀):Shingle.Mild P (neighbors z i) (fun x=> b x i) s:= Shingle.rising Q₀ hz hY i
  have ht: Compared F.holds.doors P t s:= Shingle.curtain hh a (fun _ _=>rfl) (fun y hy i=> by
    unfold t Career.folio; rw [Meadow.compassN]; unfold a; split
    all_goals rfl)
  have hx' x (hx:x∈s)(i:Site A₀): Varies (fun y=>f y i) x s:= by
    let D':ℝ→Trio.Offer G _:=fun y=>Meadow.baronyN (F.hearth H y) H.w.ℓ O k γ
    apply Shingle.lightingN k H.w.ℓ (F.holds.base) hh rfl (show ∀ x∈ s, ∀ i,P.Regular _ _ from ?_) Q₀ hz hY i (D:=D') ?_ hx
    · intro y hy j; rw [Beam.rewrite_rule]; exact (Rain.twined R.pledging hm F.holds F.turns R.inn y).smooth j
    intro x hx; let y:= F.holds.latch x; have hx₀: F.holds.base.supportP=(F.hearth H x).supportP:= Match.same_area ((F.turns _ F.holds.he).1.path.trans (F.turns _ y.2).1.path.symm) (F.wave.reg _ F.holds.he _ y.2) (F.wave.forced _ F.holds.he _ y.2)
    exact Meadow.asterN O B (F.cords H x) ((F.turns _ F.holds.he).1.path.trans (F.turns _ y.2).1.path.symm) hx₀ (F.holds.agrees _) γ k i
  exact ⟨ht,hf,hx'⟩
open Coup Scarf Urns Marlin Shingle
variable (hk:F.Accepts H k)(hF:∀ x∈s, Trail.Hired H W (Q x) tag)
-- Across.Ability.career. Move local. payment tags. forecast_price H.ψ. Tag inherited.
local notation "X!"=> (F.school H W k' tag)
local notation "v₀"=> F.index H W k' tag k
local notation "Qa'"=> Coup.bring (G:=G) (D.L J) (X.p.profile I) H.w (Rain.lint R.target A m) (W.crew H m) x₀ (3*W.mass H m)
local notation "PK"=> forecastK (A.B.a) m R.scout
variable (x:ℝ)(hx:x∈s)
include hF x hx hk
lemma atPort : Collection.Local (X!) (B) (v₀ x) (Qa') (PK (Q x).beta) :=by
    let t:=F.holds.latch x; have hT:= F.turns _ t.2; have hu:= F.indices H W k' tag x (k:=k)
    rw [hu.1,hu.2,← show Q t=Q x from (show Q (F.holds.latch x)=Q x from (by rw [Embrasure.click _ _ hx]))]
    obtain ⟨h,hP⟩:=hk x hx; exact Trail.localLaw H W hm hT.1 hT.2 (F.hearth H x) (F.holds.honors t) (hF _ t.2) (F.exhibit H x) F.maps h hP k'
lemma atEarn : Collection.Local (X!) (B) (v₀ x) (W.hop H m* (betaF G x₀ (D.L J))^(Pastel.chip 0)) (PK (Q x).beta) :=by
    have h:= F.atPort H W hm k' tag hk hF _ hx; have hT:= Trail.earned H W (m:=m)
    obtain ⟨v₁,hp,hx⟩:= h.cheap
    exact { h with cheap:= ⟨_,hp,fun x=>budget_loosen (hx x) hT.early⟩ }
lemma atLamp : Collection.Local (X!) (B) (v₀ x) (forecastE A.B.a m) (PK (Q x).beta) := by
    have h:= F.atEarn H W hm k' tag hk hF _ hx; obtain ⟨v,hp,ht⟩:= h.cheap; exact {h with cheap:=⟨_,hp,fun x=>budget_loosen (ht x) (W.budgetGoal H)⟩ }
lemma atAtlas (d:Return.Bookings A.B m n R.walls): Return.atlas A.B N F.forest d O (radiusW R.rider) (Q x) (F.school H W k' tag) (v₀ x) (F.peeled H k x):=by
    let t:= F.holds.latch x; have hv:= F.indices H W k' tag x (k:=k); have hT:= F.turns _ t.2; obtain ⟨h,hP⟩:= hk _ hx; let Y₀:= Q t; let M:=R.machine
    rw [hv.1,hv.2,← show Q t=Q x from (show Q (F.holds.latch x)=Q x from (by rw [Embrasure.click _ _ hx]))]
    exact (Return.earnings A.B N F.forest d O (radiusW R.rider) M.ring M.bill hm Y₀ hT.1 hT.2).2.2.symm.trans (funext fun i=> W.soil H hm hT.1 hT.2 (F.hearth H x) (F.holds.honors t) (hF _ t.2) (F.exhibit H x) F.maps h hP k' F.forest i)
omit x hx
lemma meets : Compared X! (B) (v₀) s := by
    have hr:= Trail.breadth H W (m:=m) (n:=n)
    obtain ⟨hp,hD,hY⟩:= F.toneReady H hm (k:=k)
    let z₀:= (d'); let t:=(F.folio H k); let W':=(F.school H W k' tag); let L:= Trail.vested (p:=p) H (F.holds.base) tag k'; let D':= (F.dapple H k)
    have hP:Scarf.Rooms (Beam.marquee (F.holds.base) B).reg L z₀ (B) (W.crew H m):= Trail.stairV H W Ω k'
    have hV i:Mild (B) (neighbors z₀ i) (fun x=> D' x i) s:= (hD i).mono (fun j hj=> (neighbors_mem ..).2 (((neighbors_mem ..).1 hj).trans (by unfold z₀; omega)))
    let v' := Coup.tune (G:=G) (D.L J) (X.p.profile I) H.w (Rain.lint R.target A m) x₀
    have hG x (hx:x∈s):= (hk x hx)
    let d:= Coup.freezes (G:=G) (D.L J) (X.p.profile I) H.w (Rain.lint R.target A m) x₀ (3*W.mass H m)
    have hf x (hx:x∈s): Meadow.Budget B (leap (c:=A₀) z) (D' x) v':=by
       let y:=F.holds.latch x; have hx':=F.turns _ y.2; exact Trail.oldGold H hm hx'.1 hx'.2 (F.exhibit H x) F.maps ((hG x hx).2)
    have ha' x (hx:x∈s)(i:Site (A₀))(V':Config G (A₀)):‖F.daily H W k' tag k x i V'‖ ≤ d:=by
       let y:=F.holds.latch x; have h:=F.turns _ y.2; obtain ⟨hz,h'⟩:= hG x hx; rw [flowDaily]; exact (Trail.hosts H W hm h.1 h.2 (F.hearth H x) (F.holds.honors y) (hF _ y.2) (F.exhibit H x) F.maps hz h' k' i).2.2 V'
    have hu x (hx:x∈s)(i:Site (A₀)): (B).supBounds i (neighbors z₀ i) (D' x i) v' :=by
       obtain ⟨f,h,hF⟩:= hf x hx; apply VerifiedReset.sup_le (VerifiedReset.sup_larger (hF i|>.2) (?_)); swap
       · intro j hj; exact (neighbors_mem ..).2 (((neighbors_mem ..).1 (show _∈ neighbors z i from hj)).trans (by unfold z₀; omega))
       have hv:= budget_single (Scarf.stanza (leap z) h (fun i=> (hF i).2.1) i) i; rwa [if_pos rfl] at hv
    have hz x (hx:x∈s): ∀ i:ℕ,(B).Regular ((F.holds.doors.reg i).support) ((t x).logRead i):= by
       obtain ⟨hv',ht⟩:= hk x hx
       let y:=F.holds.latch x; have hx':=F.turns _ y.2; have hU:= Trail.oldTol H W hm hx'.1 hx'.2 (F.hearth H x) (hF _ y.2) hv'
       have hu: Meadow.Budget B F.holds.doors.reg (t x|>.logRead) (Coup.lacquer (G:=G) (D.L J) (X.p.profile I) H.w x₀ (3*Trail.mass H W m)):=by unfold t; rw [F.aloft, F.tables H (p:=p) k' tag x |>.1]; exact hU -- edit
       obtain ⟨w,h,hQ⟩:= hu
       exact fun i=> (hQ i).1
    refine Shingle.tune (g:=D') (X:=porch H F W k' tag) z₀ z₀ (fun x hx i=> (hV i).smooth _ hx) hu ha' (Scarf.transfer hp hP) (?_) (fun x hx i=> Scarf.hesitating hp hP (by omega) hD (fun x hx'=> hz x hx') i hx (hY _ hx _)) ?_
    · intro x hx i ε hε; filter_upwards [self_mem_nhdsWithin,(hV i).budget x hx i ε hε] with y hy hg; exact (VerifiedReset.sup_varies (d:=leap _ _) (hV i|>.smooth x hx) (hV i|>.smooth y hy)).2 hg
    intro x hx; have he:=Rain.twined R.pledging hm F.holds F.turns R.inn x; exact ⟨he.expensive.choose,fun i U=>he.expensive.choose_spec.1 i |>.2 U⟩
end Career
end YM.PhysicalNext.Repeat.Mallow
