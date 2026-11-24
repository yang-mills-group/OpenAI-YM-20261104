import YM.LocalLTE.Bonnet.Career
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
namespace Career
open Urns Slide Sienna Progress.DirectedRecipe
set_option quotPrecheck false
variable (hm:m<N)(h:F.Accepts H k)
local notation "J'"=> (X.p.profile I)
local notation "Z₀"=> Trio.resize H.w.ℓ (Rain.lint R.target A m)
local notation "V"=> F.holds
local notation "L'"=> D.L J
local notation "v"=> F.holds.base
local notation "Q₀"=> (fronts (m:=m) (A:=A) (C:=R.target) H.w)
local notation "p₀"=> (F.plated H k)
include h hm
lemma beats : Compared (F.issue H) (B) (F.plated H k) s:=by
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
  let ℓ:= planks G L' Z₀ J' x₀ * Real.exp (stout (X.p.profile I)* coverTicket Z₀); let Z:= Trio.lossFee G L' (R.expense J I).wanting Z₀ (X.p.profile I) x₀
  have hB x (hx:x∈s)(i:Site A₀):P.supBounds i (neighbors z i) (b x i) ℓ:=by
    obtain ⟨w,hw,hV⟩:= Urns.textile (n:=n) H.w hm R.inn H.vote p.jewels hp hc p.conducts.full (F.exhibit H x) F.maps R.floor (R.settles _ _) (h x hx).2
    apply VerifiedReset.sup_le (hV i).2; refine (le_mul_of_one_le_right (b:=Real.exp (preExponent B * coverNumber (B).B (neighbors z i))) (hV i|>.2.1) ?_).trans ?_
    rotate_left; · exact ((if_pos (show (leap z i).site=i from rfl)).symm.trans_le (budget_single (hw i) i))
    exact Real.one_le_exp (mul_nonneg (headline B|>.exponent_pos.le) (Nat.cast_nonneg _))
  have hF x (hx:x∈s)(i:Site A₀)(U): ‖f x i U‖ ≤ Z:= by
    have hL := F.turns _ (F.holds.latch x).2; unfold f; rw [(F.identity H _ _).1]; exact (Urns.hauls H.w hm R.inn H.vote p.jewels hp hc p.conducts.full p.conducts.income (F.hearth H x) (F.holds.honors _) hL.1 hL.2 _ k i).2.2 _
  refine Shingle.tune (g:=b) z (2*z) (fun x hx i=> (hf i).smooth x hx) hB hF ht ?_ hx' ?_
  · intro x hx i ε hε; filter_upwards [self_mem_nhdsWithin,(hf i).budget x hx i ε hε] with y hy hu; exact (sup_varies ((hf i).smooth x hx) ((hf i).smooth y hy)).2 hu
  intro x hx; obtain ⟨i,hi,h⟩:= (Rain.twined R.pledging hm F.holds F.turns R.inn x).expensive; exact ⟨i,fun _=> (hi _).2⟩

-- drive at the interval. parameter issue arises when using literal `latch x`; hx.
variable (hG:G.Simple)
include hG
abbrev result (k:ℕ)(x:ℝ) := Return.result A.B N Q (F.issue H) (F.plated H k) x
omit h hm hG in
lemma literal (x:ℝ)(hx:x∈s) : F.result H k x = Urns.baked H.w (F.hearth H x) (F.exhibit H x) k:=by
  obtain ⟨-,-,-,hV,hs⟩:= Career.identity H F k x
  let D:=(F.hearth H x); let z':=F.exhibit H x; let T':= Q (F.holds.latch x)
  have he : T'= Q x:= by unfold T'; rw [Embrasure.click _ x hx]
  dsimp only [Career.result,Urns.baked,Return.result,Template.install,Template.trial, UVNext.CouplingReset.scalar,UVNext.CouplingReset.target,predictor,board,Return.ledger,terms]; rw [hV,hs, ← he]
lemma direction : Curve (A.B.a.budget m) (F.result H k) s∧∀ x∈s,A.B.Move N m n (F.result H k x) (Q x) ∧ Accurate A.B R.post N m n (F.result H k x) (Q x) ∧ (F.result H k x|>.v) = Collection.vac (p₀ x) (F.peeled H k x):= by
  let T':= F.holds; let S:=F.issue H; let f:=F.plated H k; let d:=Opera.forum (m:=m) (n:=n) A.B R.shape
  have hz x (hx:x∈s) :Return.atlas A.B N F.forest d O (radiusW R.rider) (Q x) S (f x) (F.peeled H k x) ∧ Collection.Local S (B) (f x) (forecastE A.B.a m) (forecastK A.B.a m R.scout (Q x).beta):=by
    obtain ⟨h',hu,-⟩:=Career.ascend H F hm hG h x hx d
    let Z:=F.hearth H x; obtain ⟨-,-,-,hb,hF⟩:= Career.identity H F k x
    have hl : Q x=Q (F.holds.latch x) := by rw [Embrasure.click _ x hx]
    unfold S f; rw [hb,hF,hl]; exact ⟨h',hu⟩
  obtain ⟨ht,hX⟩:= R.machine.run hm F.turns hG F.forest d O (fun x hx=> (hz x hx).1) (fun x hx=> (hz x hx).2) (Career.beats H F hm h) F.wave
  refine ⟨ht,fun x hx=> ⟨(hX x hx).2.1,?_,(hX _ hx).2.2.2.2⟩⟩; unfold Accurate; rw [← sub_add_eq_sub_sub]; exact (hX _ hx).2.2.1
end Career
end YM.PhysicalNext.Repeat.Mallow
