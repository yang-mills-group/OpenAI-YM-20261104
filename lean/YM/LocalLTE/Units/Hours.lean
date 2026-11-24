import YM.LocalLTE.Units.Fold
import YM.LocalLTE.Units.Arc
/-! Shell to couplings energy. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.FrameBox
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat SliceRows
open AbsoluteSums Animals PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Inset
open Analysis Slide
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c L : Side} {n i p:ℕ} {o:Site c} (X:Grove o) {a b s w κ k:ℝ} {B:BudgetPoint} (hp : Reliable G κ k)
local notation "χ"=>Chi.canonical
local notation "E"=>Directions G c
open Cabana Grove
-- φ height eventwise; no orientation yet
lemma narrow (V:Config G c) (ha: 0≤a) (h:∀ i,G.chord (V i)≤a) (Y:ℕ) (i:Bond c) (hh:fits i o Y) : G.chord (X.fix V i) ≤ ((8:ℝ)*Y+1)*a:= by
  have he (j:Site c)(hx:j∈neighbors Y o) : G.chord (X.uplink V j)≤ 4*Y*a:= by
    refine (Grove.cost_travel V a h _ _).trans (mul_le_mul_of_nonneg_right ?_ ha); exact_mod_cast ((X.term j).2.1.trans ((short _ _).trans (Nat.mul_le_mul_left 4 ((neighbors_mem ..).1 hx))))
  unfold Grove.fix Lattice.gauge; refine (G.chord_triangle _ _).trans ?_; rw [G.chord_inv]; refine ((add_le_add ((G.chord_triangle ..).trans (add_le_add (he _ hh.1) (h i))) (he _ hh.2))).trans ?_; apply le_of_eq; ring
open Frond
lemma likes {A:Type} [NormedAddCommGroup A][NormedSpace ℝ A] (Y:ℕ) {W:A→ Config G c}{x:A}(hx:Mode W x i b)(v:Bond c) (h:fits v o Y): Brush i (Blaze.royalty G) (Frame.expense G Y b) (fun y=> G.mat (X.fix (W y) v)) x:=by
  let r:=Blaze.royalty G
  have hK (o':Site c)(hB:o'∈neighbors Y o): Brush i r (4*Y*(b*r)) (fun y=> G.mat (X.uplink (W y) o')) x:= by
    refine (tour _ o hx.pos hx.atLink).climb le_rfl (mul_le_mul_of_nonneg_right ?_ (mul_nonneg hx.pos (zero_le_one.trans (Blaze.royalty_ge G))))
    exact_mod_cast ((X.term o').2.1.trans ((short ..).trans (Nat.mul_le_mul_left _ ((neighbors_mem ..).1 hB))))
  unfold Grove.fix Lattice.gauge; simp only [G.mat_mul,mul_assoc]
  have he:1≤r:= royalty_ge _
  let u y:= X.uplink (W y) v.1; let u' y:= X.uplink (W y) (v.1+step v.2); apply Blaze.links (f:=u) (hK v.1 h.1) _ r (max_le he le_rfl); exact Blaze.links (f:=fun y=> W y v) (hx.atLink _) (Blaze.reverse (f:=u') (hK _ h.2)) r (max_le he le_rfl)

-- General budget conversion (need not measure thermal chart on F far). U close links off Hull rest arbitrary if Mode there.
variable {E':Type}[NormedAddCommGroup E'][NormedSpace ℝ E']
include hp
lemma climbs (m:ℕ){f:E'→ Config G c} {x:E'} (hf:Mode f x i b) {r J : ℝ} (h: Frond.Suitable G i J w 1) (hV:∀ᶠ y in 𝓝 x,∀ z: Bond c,G.chord (f y z) ≤ r) (h0 : 0 ≤ J) (ha: 0≤r) (he : (8*m+1:ℝ)*r≤κ) (hh:G.colorScale*((8*m+1:ℝ)*r)≤ w) :
    Brush i (i.factorial * J) ((1+Blaze.royalty G)*(Frame.expense G m b)) (X.crook m χ κ ∘ f) x:= by
  have hz : 0≤ (1+Blaze.royalty G)*(Frame.expense G m b):= by unfold Frame.expense; have hx:=hf.pos; have hh:=royalty_ge G; positivity
  refine Brush.fold hz (by positivity) (fun y=>?_); simp_rw [Function.comp_apply,crook, shore_apply]
  split_ifs with hk
  · refine ((FrameBox.likes X _ hf y hk.1).pine (h.sound _ ?_)).shimmy ?_
    · rw [← chord_dist]; exact (mul_le_mul_of_nonneg_left (FrameBox.narrow X _ ha hV.self_of_nhds _ y hk.1) G.colorScale_pos.le).trans hh
    filter_upwards [hV] with v hv; exact hp.kept χ _ ((FrameBox.narrow X _ ha hv _ _ hk.1).trans he)
  exact (Brush.certified hz (0:G.Color)).climb (by simp; positivity) le_rfl

lemma buds (m:ℕ){r:ℝ}(hr:0≤r) (he:(8*m+1:ℝ)*r ≤ κ) (V: Config G c) (hV:∀ i,G.chord (V i)≤r) : ‖X.crook m χ κ V‖≤ k*((8*m+1:ℝ)*r):= by
  have hR:= hp.price; refine (pi_norm_le_iff_of_nonneg (by positivity)).2 (fun i=>?_)
  unfold crook; rw [X.shore_apply]; split
  next hi=>
    have h:=(FrameBox.narrow X V hr hV _ _ hi.1); rw [hp.kept χ _ (h.trans he)]; exact (hp.cap _ ((h.trans he).trans (by have hh:=hp.down; linarith))).trans (mul_le_mul_of_nonneg_left h hR.le)
  rw [norm_zero]; positivity

end YM.LocalLTE.FrameBox
