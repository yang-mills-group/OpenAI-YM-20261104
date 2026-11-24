import YM.OPE.Compatible.Soup.Course
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
variable (h:Tendsto β φ atTop)(hD: GaugeD A U D)
section
variable {V Y:∀ j,Bid.Dir G (n j)}
structure Lyd (A: ∀ x:I,HillZ (T:=T) S i r d τ (β x) (n x)) (φ:Filter I) (V:∀ j,Bid.Dir G (n j)):Prop where
       habit:∀ᶠ j in φ, SerT (V j) (WorkB A j)
       brim: Receipt β φ (fun j=> ‖V j‖)
variable (A U) (x:I→Merchant.Chamber G r)
private lemma stair_habit (j:I) (z:Merchant.Chamber G r) : SerT (Stair A U j z) (WorkB A j) := by
  exact SerT.raise (sparse_s G (Punched A U j) z) (broader A U j)

private lemma stair_fare (j:I) (z:Merchant.Chamber G r) : ‖Stair A U j z‖ ≤ ‖z‖ := by
  have paid := money_s G (Punched A U j) z
  unfold Stair
  match_account_types paid

lemma stanza (hp: Receipt β φ x): Lyd A φ (fun i=> Stair A U i (x i)):=by
  constructor
  · exact Eventually.of_forall (fun j=>stair_habit A U j (x j))
  · apply hp.liftp
    exact Eventually.of_forall (fun j=>(norm_norm _).trans_le (stair_fare A U j (x j)))

lemma Lyd.both (hU:Lyd A φ V)(hV:Lyd A φ Y)(ht:Tendsto β φ atTop): Lyd A φ (fun i=>V i+Y i):=⟨(hU.habit.and hV.habit).mono fun _ hi=> SerT.plus hi.1 hi.2,(hU.brim.plus hV.brim (carth ht)).under (Eventually.of_forall fun i=>(norm_norm _).trans_le (norm_add_le (V i) (Y i)))⟩
lemma Lyd.minus (hU:Lyd A φ V): Lyd A φ (fun i=> -V i):=⟨(hU.habit).mono (fun i hi=> (neg_one_smul ℝ (V i)) ▸ hi.gauge (-1)), hU.brim.congr (Eventually.of_forall fun i=>(norm_neg (V i)).symm)⟩
variable {A U D}
include hs hD h
lemma Lyd.poured (hp:Lyd A φ V): Receipt β φ (fun i=> tapP A U D i (V i)):=by
       obtain ⟨f,g,H⟩:= merit A h; let iG:= Fract S r; have hF:0 < iG:=Fractage ..; let c:= Counters β; have he(x:ℝ): Receipt β φ (fun _=>x):= YM.OPE.Score.steady x (carth h)
       let a(j:I):=‖V j‖; apply YM.OPE.Score.under (((he (2:ℝ)).product ((hp.brim.plus (he 2) (carth h)).power 2 (carth h))).product H.meat|>.product (he iG⁻¹)); filter_upwards [hp.habit] with i hi; have hp : ‖pour (Stair A U i) (chrom (KPole A i)) (D i) (V i)‖ ≤ _ := gustB (Mater A i) hs (Punched A U i) (D i) (broader A U i) (V i) (fun j hh t hv=>(H.ν i j hh t hv).1) hi le_rfl (H.fare i).1 iG hF (hD.rate i); exact hp.trans (le_of_eq (div_eq_mul_inv ..))
omit hs hD h in
private lemma mix_value (j:I) (z:Bid.Dir G (n j)) :
    z + (-(Stair A U j (tapP A U D j z)))=mixT A U D j z := by
  unfold mixT mate tapP
  simp only [_root_.sub_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply]
  have paid := (sub_eq_add_neg z (Stair A U j (tapP A U D j z))).symm
  unfold tapP at paid
  match_account_types paid

lemma Lyd.pinned (hp:Lyd A φ V):Lyd A φ (fun j=> mixT A U D j (V j)):=by
  have negRow:=Lyd.minus A (stanza A U _ (hp.poured hs h hD))
  have rows:=Lyd.both A hp negRow h
  have value (j:I) := mix_value (A:=A) (U:=U) (D:=D) j (V j)
  exact (congrArg (Lyd A φ) (funext value)).mp rows

end
section
variable (A U)
lemma Tango (h':Tendsto β φ atTop) : RateIs φ (Counters β) (et A) (-(1/2)):= by rw[←neg_div]; exact worthP (torν i S A h').Lamp
variable {A U} {V:∀ j,Bid.Dir G (n j)} (hp:Lyd A φ V)
include hs h hp
lemma appeals (hk:1 ≤ k)(hy:k≤ 5): Receipt β φ (fun i=> jet (KPole A i) k (V i)) :=by
       let Cz (i):= ‖V i‖+1; have hx(i):‖V i‖< Cz i:= lt_add_one _; obtain ⟨f,g,H⟩:= merit A h; have hc: Receipt β φ (Cz):= hp.brim.plus (YM.OPE.Score.steady _ (carth h)) (carth h); apply ((hc.power k (carth h)).product H.meat).under; filter_upwards [hp.habit] with i hi; exact Pat_charge (Variance.DuneAt (Mater A i) hs).sm (H.ν i (V i) hi _ (hx i)).1 hk hy ((norm_nonneg _).trans (hx i).le) (H.fare i).1
lemma gloss (hk:1 ≤ k)(hy:k ≤ 5): Wax β φ (fun i=> jet (LPole A i) k (V i)) 0:=by
       obtain ⟨f,g,H⟩:= merit A h; let p(i):=‖V i‖+1; let z(i):=(p i)^k*g i; have he: Wax β φ z 0:=((waitG h (((hp.brim.plus (YM.OPE.Score.steady _ (carth h)) (carth h)).power k (carth h)))).mul H.lite).mono (by norm_num); apply he.of_norm_le; filter_upwards [hp.habit] with i hi; exact Pat_charge (Variance.DuneAt (Mater A i) hs).sg (H.ν i (V i) hi _ (lt_add_one _)).2 hk hy (le_trans (norm_nonneg (V i)) (lt_add_one _).le) (H.fare i).2
end
end YM.OPE.Owl.HillZ
