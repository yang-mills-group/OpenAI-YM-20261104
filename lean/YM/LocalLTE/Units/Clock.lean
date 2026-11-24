import YM.LocalLTE.Units.Edge
import YM.LocalLTE.Units.Hours
/-! Apply Hold and Cost to one curvature parameter pack. No universal dimension costs.
Affine and K reattachment afterwards need purchases. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.FrameBox
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat SliceRows
open AbsoluteSums Animals PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Inset
open Analysis Slide
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c L : Side} {i p:ℕ} {o:Site c} (X:Grove o) {m:ℕ}
open Cabana Grove
local notation "η" => Chi.canonical
local notation "Z" => neighbors m o
local notation "H" => Positions (Uniform.Primary c G)
local notation "ι" => Directions G c
variable {κ k a b w:ℝ}
structure ChargeG (G:Gauge) (i:ℕ)(κ a b:ℝ)(z:ℕ): Prop where
  ok:0<a
  top:0<b
  stake (c:Side)(x:Positions (Uniform.Primary c G))(o:Site c)(X:Grove o) : ‖x‖<a→∀ i:Bond c,X.Spare z i→ G.chord (X.fix (Boulevard.actual x) i)≤κ
  budget (c:Side)(x:Positions (Uniform.Primary c G))(o:Site c)(X:Grove o) : ‖x‖<a→
     ‖X.crook z Chi.canonical κ (Boulevard.actual x)‖< b ∧ Brush i b a⁻¹ (X.crook z Chi.canonical κ ∘ Boulevard.actual) x
include X
variable {B: BudgetPoint} {f:Config G c→ℝ}{Q:Pkt (Directions G c) p} {c':ℝ}
lemma revisit (hs: Reliable G κ k)(h:ChargeG G i κ a b m) (hz:2*(2*m)≤c.val) (hp:B.Regular (neighbors m o) f) (ht:∀ x: Directions G c,‖x‖ < b→ Fold.pullV o m hz (soloV x)∈ sunny B →
    Brush i w b⁻¹ (fun v=> f (soloV v) - Cabana.actual Q v) x) (x:H) (hh:‖x‖<a) (hx: Boulevard.actual x∈ sunny B) :
    Brush i (i.factorial*w) a⁻¹ ((f - realise X m κ (colorP Q)) ∘ Boulevard.actual) x:= by
  let P:=(X.crook (G:=G) m η κ ∘ Boulevard.actual); let W (y:H)(u:G.El):= wheel u (P y); let K:= fun y u=> f (Boulevard.actual y)-Cabana.actual Q (W y u)
  have hΩ (y:H): Continuous (K y):= continuous_const.sub ((Cabana.moves _ (⊤:WithTop ℕ∞)).continuous.comp (wheel_moves _))
  have hV : ∀ᶠ y:H in 𝓝 x,Boulevard.actual y∈ sunny B ∧ ‖y‖<a:= by
    have hc:Continuous (Boulevard.actual (c:=c) (G:=G)):= continuous_pi fun k=> by unfold Boulevard.actual; simp_rw [Work.F03.represent_link]; fun_prop
    exact (hc.continuousAt.eventually (show sunny B∈𝓝 _ from (sky B).mem_nhds hx)).and (continuous_norm.continuousAt.eventually (gt_mem_nhds hh))
  have hF : ∀ᶠ y:H in 𝓝 x,∀ i:G.El, Fold.pullV o m hz (soloV (W y i))∈ sunny B ∧ f (Boulevard.actual y)=f (soloV (W y i)):= by
    filter_upwards [hV] with y hy u
    let v:= Lattice.gauge (X.uplink (Boulevard.actual y)) (Boulevard.actual y); let K:=Lattice.gauge (fun _ => u) v
    have hp' : Agrees (Z:Set (Four (Per c))) (soloV (W y u)) K:=by
      let g:Site c→G.El:=fun _=>u
      let U:=Boulevard.actual y; have hχ : W y u=X.crook m η κ (gauge g U):=(wheel_away X hs g m U).symm
      rw [hχ, show K=X.fix (gauge g U) from (X.painted g U).symm]
      refine X.repairs η hs _ fun j he=> ?_; rw [X.painted]; change G.chord (u*_ * u⁻¹)≤_; rw [G.chord_conj]; exact h.stake c y o X hy.2 j he
    have ht : K∈ sunny B:= by intro j; unfold K v; rw [face_gauge,face_gauge,G.chord_conj,G.chord_conj]; exact hy.1 _
    refine ⟨(Fold.collaborates o m hz _ K hp').symm ▸ Fold.burn o m hz B K ht,?_⟩
    rw [hp.sites _ _ hp']; unfold K v; rw [hp.symmetry,hp.symmetry]
  let C:ℝ:= i.factorial*w
  have hK : ∀ᶠ y:H in 𝓝 x,∀ u:G.El, Brush i C a⁻¹ (fun y=> K y u) y:= by
    -- at ALL close y, not just o: move eventually hF
    filter_upwards [hV,hF, eventually_eventually_nhds.mpr hF] with y hy hty hy' u
    have hvu : ‖W y u‖<b:= (wheel_norm u _).trans_lt ((h.budget _ y _ X hy.2).1)
    have hr : Brush i b a⁻¹ (fun x=> W x u) y:=by
      have he := (h.budget _ y _ X hy.2).2.report (wheel u) (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x=> by rw [one_mul]; exact wheel_norm u x)
      rw [one_mul] at he; exact he
    apply ((Frame.cascade (h:=fun y=> W y u) hr (ht (W y u) hvu (hty u).1) h.top)).shimmy
    filter_upwards [hy'] with i hi; exact congr_arg (fun v=> v-Cabana.actual Q (W i u)) (hi u|>.2)
  obtain ⟨ht,-⟩:= Meristem.points K G.probHaar ⟨fun _=>_,integrable_const _,(by filter_upwards [hK] with y hy using (show ∀ j, Brush i (C * (1+a⁻¹)^i) 1 (fun y=> K y j) y from fun i=> (hy i).trim))⟩ (Eventually.of_forall fun y=> (hΩ y).measurable)
  apply (ht.buds (fun _=>C) (integrable_const _) (inv_nonneg.mpr h.ok.le) (by simp : (∫ _:G.El,C ∂G.probHaar) ≤ C) (ae_of_all _ (hK.self_of_nhds))).shimmy
  apply Eventually.of_forall; intro i; change f _- realise X m _ (colorP _) _ = ∫ u:G.El, f _-Cabana.actual Q _ ∂G.probHaar
  unfold realise; rw [sunwheel, integral_sub (integrable_const _) (show Integrable (fun u=>Cabana.actual Q (W i u)) G.probHaar from ((Cabana.moves Q (⊤:WithTop ℕ∞)).continuous.comp (wheel_moves (P i))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]; simp [W,P]
end YM.LocalLTE.FrameBox
