import YM.LocalLTE.Motion.Pure
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
variable (x:ℝ)(hx:x∈s)(j:ℕ)(hj:j≤p)
local notation "s'"=> (A.B.a.budget (m+1))
local notation "A!"=> (A.B.a.S.side (m+1) n)
def borough(y:ℝ):= Q (F.holds.latch y)
include hx
lemma movesY : Tendsto (fun y=> (F.borough H y|>.beta)) (𝓝[s] x) (𝓝 (F.borough H x).beta):=by
    have hy:= Embrasure.click F.holds x hx; have ht:= F.wave.beta x hx
    unfold borough; rw [hy]; exact ht.congr' (by filter_upwards [self_mem_nhdsWithin] with y he; rw [Embrasure.click _ y he])
lemma flowE (i:ℕ)(V:Config G (A.B.a.S.side (m+1) n))(h:flags (F.borough H x|>.p.threshold) V=∅): Tendsto (fun y=>(F.borough H y).activities.E i V) (𝓝[s] x) (𝓝 ((F.borough H x).activities.E i V)):=by
    let t:= s'; let Z:= F.borough H x; have he := Embrasure.click F.holds x hx; have hr:Z= Q x:=by unfold Z borough; rw [he]
    have hT:t= Z.p:= (F.turns _ (F.holds.latch x).2|>.1.point.symm)
    refine (Metric.tendsto_nhds.mpr ?_); intro ε hε
    filter_upwards [self_mem_nhdsWithin,F.wave.continuous (ε/2) (half_pos hε) x hx] with y hy ht; obtain ⟨c,d,hc,hd,hF,hC⟩:=ht
    have hp : Healthy t.threshold (Q x|>.activities.reg i|>.support) V:=by unfold Healthy; rw [hT,(show flags (Z.p.threshold) V=∅ from h)]; simp
    have h' i:= hc i
    have hK:= (h' i).2 _ hp [] (by simp) (by simp); change dist (F.borough H y|>.activities.E i V) (Z.activities.E i V)<_; unfold borough; rw [hr, Embrasure.click _ y hy,dist_comm,dist_eq_norm]; exact (hK.trans ((t.loMass _ _ (h' i|>.1)).trans (budget_single hF i))).trans_lt (half_lt_self hε)
lemma glowing : 0 < gStep (F.borough H x).beta ∧ Tendsto (fun i=> gStep (F.codec H i).val) (𝓝[s] x) (𝓝 (gStep (F.codec H x).val)) :=by
   have hp:=(F.hearth H x).laws.intake.positive; exact ⟨inv_pos.mpr (Real.sqrt_pos.mpr hp), (F.movesY H x hx|>.sqrt).inv₀ (Real.sqrt_pos.mpr hp|>.ne')⟩
-- unrot price.fetched. both g.Gain. existence references.
local notation "L'"=> D.L J
variable {v:ℝ}(hp:0<v)(hX:∀ x∈s,Trail.Keeps H (F.hearth H x) tag p k')
include hk J' hp hj hm F
omit hx hp in
lemma coating {i:Site A₀}{x:ℝ}(hx:x∈s): (B).Regular (neighbors d' i) (F.glance H x j i)∧∃ v,(B).supBounds i (neighbors d' i) (F.glance H x j i) v:= by
   have hp:= F.fireworks H W hm J' hk x hx j hj; let V:= F.exhibit H x; let b:=F.holds.latch x; have hv:= F.turns _ b.2; have h:= Trail.oldGold H hm hv.1 hv.2 V F.maps (hk x hx|>.2)
   have hi:= Trail.jumpPrice z (W.crew H m*radiusB x₀) (W.crew H m) (F.existZ H W).2.le (le_refl _) (F.dapple H k x) h; obtain ⟨v,h,g'⟩:=hp; obtain ⟨t,ht,hT⟩:=hi
   have hh:(F.glance H x j i)= F.dapple H k x i - ((F.dapple H k x-F.glance H x j) i):= (sub_sub_cancel (F.dapple H k x i) (F.glance H x j i)).symm
   rw [hh]; exact ⟨VerifiedReset.reg_sub (hT i|>.1) (g' i|>.1),_, VerifiedReset.sup_sub (hT i|>.1) (g' i|>.1) (hT i|>.2) (g' i|>.2)⟩

lemma sunR (i:Site (A₀)): ∀ᶠ y in 𝓝[s] x,(B).supBounds i (neighbors d' i) (F.glance H x j i-F.glance H y j i) v:=by
    let u₁:= H.d J I; let X₁(y):=F.exhibit H y
    have h:= J'.spark _ _ (step_paid A.B.a m) _ (A.B.valid.pays m) j hj
    let v₀:=YM.LocalLTE.Inset.cone Urns.clr (betaF G x₀ (D.L J)); let n':= pie j +1+ (P).order
    let f':ℝ → Config G (A₀)→ℝ:=fun y=> Urns.inkO Wf F.maps u₁ (κ:=H.κ) i (gStep (F.codec H y).val)
    have h'(y:ℝ)(z':Directions G (A₀))(hZ:‖z'‖< v₀):= Urns.motU H.w (F.exhibit H y) F.maps i j h hm z' hZ
    have hc:= F.glowing H x hx; let U (y:ℝ):= Hall.bushes (pie j+1) (f' y)
    have hV:Tendsto U (𝓝[s] x) (𝓝 (U x)):= by
        apply tendsto_pi_nhds.mpr; intro y
        have hy:0<v₀:= Real.rpow_pos_of_pos (zero_lt_one.trans_le (H.vote.cash _ _ (step_paid A.B.a m)|>.2 _ (A.B.valid.pays m)|>.light.1)) _
        exact LocalLTE.Cabana.flight hy (fun b' hz=> ((Urns.pointRead H.w F.maps i (gStep (F.codec H x).val) (hc.1.ne') u₁ (LocalLTE.FrameBox.Grove.soloV b')).tendsto.comp hc.2)) (Eventually.of_forall fun y=> h' y) (h' x) (lt_of_lt_of_le y.isLt (Nat.le_add_right ..)) -- edit
    refine Price.tintC (Z:=cane i) (κ:=H.κ) (i:=pie j+1) (m:=z) U (U x) hV ?_ (Career.coating H F W hm J' hk j hj hx) v hp -- edit
    filter_upwards [self_mem_nhdsWithin] with y hy; exact Career.coating H F W hm J' hk j hj hy
end Career
end YM.PhysicalNext.Repeat.Mallow
