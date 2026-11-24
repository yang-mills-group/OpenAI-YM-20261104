import YM.LocalLTE.Units.Clock
/-! Frame poly calibration & re-expression.
Input cone E through prescribed stage. After support cost/lipschitz. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.FrameBox
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat SliceRows
open AbsoluteSums Animals PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Inset
open Analysis Slide
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c L : Side} {i p:ℕ} {o:Site c} (X:Grove o) {m:ℕ} {κ a l : ℝ}
open Cabana Grove
local notation "η" => Chi.canonical
local notation "Z" => neighbors m o
local notation "ι" => Directions G c
-- handles eaves by Heat and tissue
section caps
variable (G L){f:ℝ→ℕ}{k v w:ℝ} (hf:Rate G L 0 fun t=>(f t:ℝ))(hp: Reliable G κ k)(hV:w<v)(hw:v<0)
local notation "X'" => (fun t=> cone v (betaF G t L))
local notation "Y" => (fun t=> cone w (betaF G t L))
include hf hp hV hw
set_option maxHeartbeats 530000 in
lemma ticketed (j:ℕ) : ∀ᶠ t in atTop, ∀ m ≤ f t, ChargeG G j κ (Y t) (X' t) m:=by
  obtain ⟨C,R,hC,hR,hL⟩:= chord_chart_cost G
  obtain ⟨C₀,hC₀,hP⟩:=Blaze.expCost G j 1
  let S:= Uniform.shade G; have hS:0<S:= Uniform.shade_pos G
  obtain ⟨J,D,hD⟩:=Frond.cleanly G j _ (zero_lt_one)
  let e:= Frame.shine j C₀ S
  let F:= fun t:ℝ=> 8*(f t:ℝ)+1
  let U t:=C*(S*(Y t))
  let g t:= (1+Blaze.royalty G)*Frame.expense G (f t) e
  let b' t:= j.factorial*J*(1+g t)^j
  have hx : Rate G L 0 g := by
    let z t:= 4*(f t:ℝ)*(e*Blaze.royalty G); have he : Rate G L 0 z:= ((hf.mul_left _).mul_right _); unfold g Frame.expense; exact ((he.mul_right _).add ((Rate.const _).add he)).mul_left _
  have ht' : Rate G L 0 b':= Rate.mul_left (by simpa only [zero_mul] using (((Rate.const 1).add hx).pow j)) _
  have hF: Rate G L 0 F:=(hf.mul_left _).add (Rate.const _)
  have h₀:= Rate.power (G:=G) (L:=L) (a:=w); have h₁:=h₀.mul_left S; have hP':Rate G L w (fun t=>F t*U t):= by
    simpa only [zero_add] using! hF.mul (h₁.mul_left C)
  have hz:= hV.trans hw
  filter_upwards [Delay.shift_pos G L,below' G L hP' hz hp.down, below' G L h₀ hz zero_lt_one,
    below' G L h₁ hz (lt_min hR zero_lt_one), contraction G L (b:=1) (a:=k) zero_lt_one hP' hV,
    contraction G L (b:=1) (a:=1) zero_lt_one (h₀.mul ht') (by rw [add_zero]; exact hV), below' G L (hP'.mul_left G.colorScale) hz hD.pos] with t hx hh hY hΛ hT hΔ hG y hy
  simp only [one_mul] at hT hΔ
  let u:ℝ:=X' t; let l:ℝ:= Y t
  have ha:0<l:=Real.rpow_pos_of_pos hx _; have he:0<u:=Real.rpow_pos_of_pos hx _
  have ht (c:Side)(x:Positions (Uniform.Primary c G))(hx:‖x‖<l) : ∀ i:Bond c,G.chord (Boulevard.actual x i)≤U t:=
      fun i=>Frame.lit_exp i x hL hC.le (mul_le_mul_of_nonneg_left hx.le hS.le) (le_of_lt (lt_min_iff.mp hΛ).1)
  have hr:(8*y+1:ℝ)*U t ≤ F t *U t:= mul_le_mul_of_nonneg_right (by unfold F; gcongr) (show 0≤U t from mul_nonneg hC.le (mul_nonneg hS.le ha.le))
  refine ⟨ha,he,fun c x o X hx i hi=> (FrameBox.narrow X _ (mul_nonneg hC.le (mul_nonneg hS.le ha.le)) (ht c x hx) y i hi.1).trans (hr.trans hh.le), fun c x o X hP' =>?_⟩
  have hg:=Frame.mode_map (lt_min_iff.mp hΛ).2.le hP x hP' hY.le
  have Hv : ∀ᶠ y:Positions (Uniform.Primary c G) in 𝓝 x,∀ z: Bond c,G.chord (Boulevard.actual y z)≤U t:= by filter_upwards [continuous_norm.continuousAt.eventually (gt_mem_nhds hP')] with z hz; exact ht c z hz
  have he0: 0 ≤ J := (hD.sound (1:G.El) (by rw [G.mat_one,sub_self,norm_zero]; exact hD.pos.le)).nonneg
  have hs':=FrameBox.climbs X hp y (b:=e) hg hD Hv he0 (show 0 ≤ U t from mul_nonneg hC.le (mul_nonneg hS.le ha.le)) (hr.trans hh.le) ((mul_le_mul_of_nonneg_left hr G.colorScale_pos.le).trans hG.le)
  have h': ‖X.crook y η κ (Boulevard.actual x)‖<u := (FrameBox.buds X hp y (show 0 ≤ U t from mul_nonneg hC.le (mul_nonneg hS.le ha.le)) (hr.trans hh.le) _ (ht c x hP')).trans_lt (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hr hp.price.le) hT)
  have ht : Brush j (j.factorial*J) (g t) _ _:= hs'.climb le_rfl (by
    unfold g Frame.expense; have hx:0≤e:=hg.pos; have he':= Blaze.royalty_ge G; gcongr)
  exact ⟨h',Frame.currency ht.trim h'.le ha he hΔ.le hY.le⟩
omit hp hV hw
variable (hW : -(1/2:ℝ)<w)
include hW
lemma poll (j:ℕ)(p:ℕ) : ∀ᶠ t in atTop,∀ m z : ℕ, z ≤ f t → m+1≤ z →∀ (P:BudgetPoint), P.power=p → P.order=j → P.threshold≤2*Pressure.fiery G t L →∀ (c:Side) (o:Site c)(_ : 2*z<c.val)(_ : 2*(2*m)≤c.val)(V:Config G c), Healthy P.threshold (neighbors z o) V→
    ∃ g:Site c→G.El,∃ W:Positions (Uniform.Primary c G),flags P.threshold (Boulevard.actual W)=∅∧ ‖W‖+2*furl G L t<Y t∧ Agrees (neighbors m o:Set (Four (Per c))) (Lattice.gauge g V) (Boulevard.actual W):=by
  obtain ⟨A,d,hA,hd,H⟩:= Next.Fluctuations.extend_interior G
  let g x:= 16*(2*(f x:ℝ)+1)^5*(Fintype.card PlaqAxes:ℝ)*(2*Pressure.fiery G x L)
  have hv : Rate G L (-(1/2)) g:= by
    simpa only [g,zero_mul,zero_add] using! (((((hf.mul_left 2|>.add (Rate.const 1)).pow 5).mul_left _).mul_right _).mul ((Rate.flame (G:=G) (L:=L)).mul_left 2))
  filter_upwards [hv.below (by norm_num) d hd, contraction G L (a:=1) (b:=1) zero_lt_one ((hv.mul_left A).add ((Sienna.belt G L|>.mul_left 2).weaken (by norm_num))) hW] with x hv hK m z hz hl P _ _ hr c o h₁ h₂ V hV
  have hj (y:Site c)(hy:separation o y ≤ z)(p:PlaqAxes) : toll V (y,p) ≤ P.threshold:= by by_contra! hv; exact Finset.disjoint_left.mp hV ((neighbors_mem ..).2 hy) ((flags_spec ..).mpr ⟨(y,p),WilsonStartup.anchor_visit _,hv⟩)
  obtain ⟨a,ha⟩:=Work.E08.axial_patch o V m z hl h₁ (2*Pressure.fiery G x L) (P.threshold_pos.trans_le hr).le (fun y hy p=> (hj _ hy p).trans hr)
  let U:=Lattice.gauge a V; let W:= Fold.pullV o m h₂ U
  have ht : 0 < 2*Pressure.fiery G x L:= P.threshold_pos.trans_le hr
  have hf' : 0 ≤ g x := mul_nonneg (by positivity) ht.le
  have he i:G.chord (W i) ≤ g x:= Fold.chord_move o m h₂ _ hf' _ (fun j hj=> (ha j ((neighbors_mem ..).1 hj.1)).trans (by unfold g; gcongr)) i
  obtain ⟨b,hb,hQ⟩:= H (fun _=> (0:Site c)) 0 0 W (g x) hf' ((le_abs_self _).trans hv) (fun i _=>he i)
  let w₁:=(Uniform.tint G _).symm b
  have hh: Boulevard.actual w₁= W:= by unfold w₁ Boulevard.actual; rw [ContinuousLinearEquiv.apply_symm_apply]; exact funext fun i=> (hQ i (by simp)).symm
  refine ⟨a,w₁, hh.symm ▸ Fold.render o m h₂ _ _ P.threshold_pos.le ?_, lt_of_le_of_lt (add_le_add ((Uniform.tint_inv_le _).trans hb) le_rfl) (by simpa only [one_mul] using! hK),fun i he hk =>?_⟩
  · unfold Healthy U; rw [gauge_flags]; exact hV.mono_left fun i he=> (neighbors_mem ..).2 (((neighbors_mem ..).1 he).trans (by omega))
  rw [hh]; exact (Fold.selfV o m h₂ U (by omega) i he hk).symm
end caps
end YM.LocalLTE.FrameBox
