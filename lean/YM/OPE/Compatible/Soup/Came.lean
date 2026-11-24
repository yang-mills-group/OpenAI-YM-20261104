import YM.OPE.Compatible.Soup.Cabin
/-!
# Epoch growth. Limited trajectory tape. variance observables without spectral cost loss
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.OPE.Owl.HillZ
open Function Filter MeasureTheory Lattice Laurent Wilson Matrix RG Gauge Precision
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ENNReal ContDiff
open Eyrie Push Push.AbsoluteSums Push.Mark Cascade Flume Flume.Page Flume.Script Pilot Finset
open Silt Libra Coin Rill Silt.Float Votive PertExtension Series GaussianScore Radial Next.Foundations
open Merchant Merchant.Aloof Merchant.Sleeve Merchant.SiteL
open Next.Free Next.Scheduling Stroke Spells Lass Lass.Zest Pill CardinalQ
variable {I:Type}{φ:Filter I}{G:Gauge} {K:Sponsor G}{T:Seasons K}
variable {β:I→ℝ}{n:I→Side}{S:Stage}{i j d r k:ℕ}{τ s a B:ℝ}
variable {A:∀ x:I,HillZ (T:=T) S i r d τ (β x) (n x)}{U: Scaffold φ (Counters β) n (Mnd i S A) r}
variable (D:I→ Law (Merchant.Chamber G r))(hs:G.Simple)
open Merchant.SiteL
variable (h:Tendsto β φ atTop) (A U)
open Cinders Metric Set Zeph Jargon
-- center Prop interior domain. chosen after x and uses cut.St
variable {N:ChartRatio G} {s c:ℝ}(H:Sweep N s c) (x:∀ i,Bid.Dir G (n i))
local notation "FW!"=>Merchant.Chamber G r
noncomputable abbrev Odds (j:I):= PinT (r:=r) G (x j) -- no r generated? in A type
noncomputable def ChartS (P:I→ℝ)(s:ℝ)(j:I):Set (Merchant.Chamber G r):={y| y+Odds (r:=r) x j ∈ CapeQ G (fieldP r) (et A j*P j) (et A j) s}
lemma OddsFee (hp:Lyd A φ x): Receipt β φ (Odds (r:=r) x):= hp.brim.under (hp.habit.mono fun i _=> money_pin G (x i))
variable (P:I→ℝ)
lemma ChartC (j:I):MeasurableSet (ChartS A x P s j):= capeMeas.preimage (show Measurable (fun i: Merchant.Chamber G r=> i+Odds (r:=r) x j) by fun_prop)
-- Contains + fees. Record
structure Startup (Q:I→ℝ) (r' b:ℝ) (D:I→ Law (Merchant.Chamber G r)):Prop where
        V : Village A U x Q
        agrees : ∀ᶠ i in φ, 0 < et A i*Q i ∧ et A i*Q i ≤ b∧ (et A i*Q i)/2 ≤ r'
        zero : ∀ᶠ j in φ,(0:Merchant.Chamber G r)∈ ChartS A x Q r' j
        rebate : Wick β φ (fun i=> (ShoreP D i).real (ChartS A x Q r' i)ᶜ)
include H in
private lemma chart_inside (j:I)(u:Merchant.Chamber G r)(ht:0<et A j)(hP:0<et A j*P j)
    (collar:(et A j*P j)/2 ≤ s)(price:‖u‖+‖Odds (r:=r) x j‖ < P j/2):u∈ChartS A x P s j:=by
  have margin:et A j*P j/(2*et A j)=P j/2 := by field_simp
  have in_ball:u+Odds (r:=r) x j∈ball (0:Merchant.Chamber G r) (et A j*P j/(2*et A j)):=by
    rw [mem_ball_zero_iff,margin]
    exact (norm_add_le _ _).trans_lt price
  have inside:=(era (F:=↥(fieldP r)) H ht hP collar).1 in_ball
  change u+Odds (r:=r) x j∈CapeQ G (fieldP r) (et A j*P j) (et A j) s
  match_account_types inside

include H in
private lemma chart_outside (j:I)(u:Merchant.Chamber G r)(ht:0<et A j)(hP:0<et A j*P j)
    (collar:(et A j*P j)/2 ≤ s)(inside:u∈ChartS A x P s j):‖u+Odds (r:=r) x j‖ ≤ 2*P j:=by
  change u+Odds (r:=r) x j∈CapeQ G (fieldP r) (et A j*P j) (et A j) s at inside
  have clipped:=(era (F:=↥(fieldP r)) H ht hP collar).2 inside
  have room:=mem_closedBall_zero_iff.mp clipped
  have margin:2*(et A j*P j)/(et A j)=2*P j:=by field_simp
  rw [margin] at room
  match_account_types room

private lemma shift_price {E:Type*} [NormedAddCommGroup E](u v:E):‖u‖≤‖u+v‖+‖v‖:=by
  calc ‖u‖=‖(u+v)-v‖:=by rw [add_sub_cancel_right]
       _ ≤ _:=norm_sub_le ..

include h hs H
variable {D} (hp:Lyd A φ x)(he:GaugeD A U D)
include hp he
lemma staff : ∃ P:I→ℝ, Startup A U x P s c D:=by
        let v:= Counters β; let g:=carth h; let p:= Odds (r:=r) x; let y(j):= (v j)^2; let W:= maxion (Merchant.Chamber G r); have hf:= OddsFee (A:=A) x hp; have hg:Receipt β φ y:= (sans h).power 2 g; have hx(j':I):0 ≤ y j':=sq_nonneg _; have hv:0<W:= ionPositive (Merchant.Chamber G r); have hm(i):0 ≤ W*y i:=mul_nonneg hv.le (hx i); let Q(i):=2*(W*y i+‖p i‖+1); have hQ : ∀ i, 0<Q i:=fun i=>by unfold Q; have hh:=hm i; positivity
        have hb(c:ℝ): Receipt β φ (fun _=>c):= YM.OPE.Score.steady c g; have hR:Receipt β φ Q:= (hb 2).product ((((hb W).product hg).plus (p':=fun i=> ‖p i‖) (hf.liftp (Eventually.of_forall fun i=> show ‖‖p i‖‖ ≤ _ from (norm_norm _).le)) g).plus (hb _) g); obtain ⟨P,hP,hT⟩:= villageG U hs h x H Q hR hp
        let Sqi(i):=ChartS A x P s i; have hE:= poseS A h hP.hue; have hC:∀ᶠ i in φ, 0 < et A i*P i∧ et A i*P i ≤ c∧(et A i*P i)/2 ≤ s:=by
              filter_upwards [hE.eventually (ge_mem_nhds H.sizes.2),hE.eventually (ge_mem_nhds (by linarith only [H.sizes.1]:0<2*s)),hymn A h] with i hi h hu; refine ⟨mul_pos hu.1 ((hQ i).trans_le (hT _)),hi,?_⟩; change et A i*P i≤ _ at h; linarith only[h]
        have hz :∀ᶠ i in φ,∀ u:Merchant.Chamber G r,‖u‖≤ W*y i → u∈ Sqi i:=by
              filter_upwards [hC,hymn A h] with i hi time
              intro u bound
              apply chart_inside A H x P i u time.1 hi.1 hi.2.2
              have gross:=hT i
              change 2*(W*y i+‖p i‖+1)≤P i at gross
              change ‖u‖+‖p i‖<P i/2
              linarith only [gross,bound]
        refine ⟨P,hP,hC,hz.mono (fun i hi=>hi _ (((norm_zero).trans_le (hm _)))),fun a=>?_⟩
        let L:=D_tail (D:=D) he h (x:=y) (fun a=> (Wick_bill h zero_lt_one a).congr (Eventually.of_forall fun i=>by unfold Burl; rw[neg_one_mul])) (Eventually.of_forall hx) a; apply L.of_norm_le; filter_upwards [hz] with i hi; rw[Real.norm_of_nonneg measureReal_nonneg]; exact measureReal_mono (fun x hx=>lt_of_not_ge fun h=>hx (hi x h)) -- norm r? ok
omit hp he hs
-- points measurements
variable (hX:Lyd A φ x) (S':Startup A U x P s c D)
include hX S'
lemma picks (V:I→ Merchant.Chamber G r)(hh:∀ᶠ i in φ,V i∈ChartS A x P s i): Receipt β φ V:=by
  let p:=Odds (r:=r) x
  have fee:=OddsFee (A:=A) x hX
  have lifted:Receipt β φ (fun i=>‖p i‖):=fee.liftp (Eventually.of_forall fun i=>(norm_norm (p i)).le)
  apply YM.OPE.Score.under (((YM.OPE.Score.steady (2:ℝ) (carth h)).product S'.V.hue).plus lifted (carth h))
  filter_upwards [hh,S'.agrees,hymn A h] with i hi hx hv
  have measured:=chart_outside A H x P i (V i) hv.1 hx.1 hx.2.2 hi
  exact (shift_price (V i) (p i)).trans (add_le_add measured le_rfl)
end YM.OPE.Owl.HillZ
