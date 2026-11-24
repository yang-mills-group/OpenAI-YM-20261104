import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.CalibratedStore
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace IssuedMaxwell.PositiveCut
open YM YM.XSpace Function Set Filter MeasureTheory Metric
open YM.XSpace.Trace YM.XSpace.Cirrus YM.XSpace.Photo YM.XSpace.Angle YM.XSpace.Chiral
open YM.XSpace.Normalize YM.XSpace.Graph3 YM.XSpace.Season YM.XSpace.AxesTangent YM.XSpace.Rose
open scoped Topology ContDiff BigOperators
variable {G:Gauge} (W:Initialize G)(g:G.Simple)(V:Store G)
local notation "A"=>YM.Points 3

variable {c:Shade.Cut}(H:Granted V 6 c)(S:Manages c G 6)
private def Y (x:A):ℝ:=(checked1 W V 6 x (tag G)).re
private lemma rebill {x:A}(h:x∈ conf 3): ContinuousAt (Y W V) x:= Complex.continuous_re.continuousAt.comp (((continuously W V 6 (tag G)) x h).continuousAt ((conf_open 3).mem_nhds h))
private def Stove (c:Shade.Cut):Set A:= spot c ∩ {x | Y W V x<0}
private lemma pots (c:Shade.Cut): IsOpen (Stove W V c):=by
  rw [isOpen_iff_mem_nhds]; intro p hp; obtain ⟨hp,hh⟩:= (show p∈spot c∩ {x|Y W V x<0} from hp); exact inter_mem (((beyond_op c.rOut 3).inter (beyond_op (4/5) 3)).mem_nhds hp) ((rebill W V (beyond_conf _ (show p∈Good c 3 from hp.1))).tendsto.eventually (gt_mem_nhds hh))
private lemma sits {a:ℝ}(p:ℝ)(h:16≤p)(u:E4)(hx:‖u‖=1)(ha:a<1) : here p u∈ Beyond a 3:=by
  have ht:(0:ℝ)<θs:=by norm_num [θs]
  have he:θs<p:=by unfold θs; linarith
  let x:=here p u; have hh: x 1 = 0 := rfl; have hz: ‖x 0‖=p:=sphere_len hx (le_trans ht.le he.le); have hy: ‖x 2‖=θs:=sphere_len hx ht.le; have hk:‖x 0-x 2‖=p-θs:= by change ‖p • u-θs • u‖=_; rw [← sub_smul]; exact sphere_len hx (sub_nonneg.mpr he.le)
  intro i j h'; unfold θs at hk hy; change 5*a <‖x i-x j‖; fin_cases i <;> fin_cases j <;> (first | (exfalso; exact h' rfl) | (simp only [Fin.zero_eta,Fin.mk_one, show (⟨2, (by decide:2<3)⟩:Fin 3)=2 from rfl] at *; first | (rw [hh]; simp only [norm_neg,zero_sub,sub_zero]; linarith) | linarith [norm_sub_rev (x 0) (x 2)])) -- indexing tactics
include W g H S in
private lemma via (h:c.rOut<1):∃ R:ℝ,∀ u:E4,‖u‖=1→ here R u∈ Stove W V c:=by
  obtain ⟨u,hu,hh⟩:= ((eventually_ge_atTop (16:ℝ)).and (testable c h g)).exists; refine ⟨u,fun b hb=>?_⟩; set x:=here u b; have ht:= sits u hu b hb h; refine ⟨⟨ht,sits u hu b hb (by norm_num)⟩,?_⟩; change Y W V x<0; rw [Y,on_stage W g V H S ht,Complex.ofReal_re,cheer]; exact mul_neg_of_pos_of_neg (pow_pos pos _) (hh b hb)

-- camera ready witness fixed along W,V and at order six relative schemes, shapes can then vary on tests & arities

include W g in
theorem original : ∃K:Rose.Pick V,∀x,0≤K.image x:=by
  obtain ⟨c,hc,h,H⟩:= budgeting g (show 4≤6 by decide) V 1 one_pos; obtain ⟨u,hu⟩:= via W g V h H hc; obtain ⟨φ,hφ,H',a,b,v,p⟩:= imaging u (pots W V c) hu; let γ:A→ℝ:= Y W V; have hx: tsupport φ ⊆ Good c 3 := fun x hx=> (show x∈Stove W V c from p hx).1.1; refine ⟨⟨c,h,H,⟨φ,a,b,hx.trans (beyond_conf c)⟩,v, (fun x hx=>(show x∈spot c ∩ _ from p hx).1) ,?_⟩,hφ⟩
  let F(x:A):= φ x * (-γ x); have he : Continuous F:=by
    rw [continuous_iff_continuousAt]; intro x; by_cases Hx:x∈tsupport φ; exact a.continuous.continuousAt.mul (rebill W V (beyond_conf _ (hx Hx))).neg
    refine (continuousAt_const (y := (0:ℝ))).congr (g:=F) ?_ -- test
    filter_upwards [(isClosed_tsupport _).isOpen_compl.mem_nhds (show x∈(tsupport φ)ᶜ from Hx)] with y hy; exact (mul_eq_zero_of_left (image_eq_zero_of_notMem_tsupport hy) _).symm
  have hp(x:A)(he: φ x≠0): 0<F x:= mul_pos ((hφ x).lt_of_ne he.symm) (neg_pos.mpr (p (show x∈ tsupport φ from subset_closure he)).2); have ht: 0<∫ x:A,F x:= he.integral_pos_of_hasCompactSupport_nonneg_nonzero (show HasCompactSupport F from b.mul_right) (fun x=>by by_cases h:φ x=0; change 0≤φ x *_; rw [h,zero_mul]; exact (hp x h).le) ((hp _ (by rw [H']; exact one_ne_zero)).ne'); change cT c G φ <0; rw [cT]; apply neg_pos.mp; rw [← integral_neg]; simp_rw [numeric_pays g V W h H φ hx,← mul_neg]; exact ht -- arguments order
end IssuedMaxwell.PositiveCut
end
