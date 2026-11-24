import YM.LocalLTE.Hall.Mint
import YM.LocalLTE.Furnace.Glow
/-! # Re-box in curved coordinates, maintaining ambient jets -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.FrameBox.Hall
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat SliceRows
open AbsoluteSums Animals PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Inset
open Analysis Slide
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {L : Side} {j n : ℕ} {a Y d₀ d v k B : ℝ} {f : ℝ → ℝ} {χ:Chi}
open Frame Sienna
lemma composed (G:Gauge)(j:ℕ)(hk : Reliable G k B)(v:ℝ)(hb:v<0)(hf: Rate G L 0 f) : ∃ g:ℝ→ℝ,Rate G L 0 g∧∀ᶠ p in atTop,
    let X':= cone v (betaF G p L)
    ∀ c : Side, (c.val:ℝ) ≤ f p → 1≤g p ∧ ∀ (V:Positions (Uniform.Primary c G)), ‖V‖ < X'→∀ u:G.El, Brush j (g p) 1 (Frame.convertLinks χ k u ∘ actual) V :=by
  obtain ⟨C,R,hC,hR,hL⟩:= chord_chart_cost G
  obtain ⟨C₀,hC₀,hP⟩:=Blaze.expCost G j 1
  let S:= Uniform.shade G; have hS:0<S:= Uniform.shade_pos G
  obtain ⟨J,D,hD⟩:=Frond.cleanly G j _ zero_lt_one
  let Y p:= cone v (betaF G p L)
  let M p:= (8*f p+1)*(C*(S*Y p)); have hK : Rate G L v M := by
    have hh := ((hf.mul_left 8).add (Rate.const 1)).mul (((Rate.power (G:=G) (L:=L) (a:=v)).mul_left S).mul_left C); rwa [zero_add] at hh
  let e:= Frame.shine j C₀ S
  let b p:= (1+Blaze.royalty G)*expense G (f p) e; let b' p:= j.factorial*J*(1+b p)^j
  have hx : Rate G L 0 b := by
    let Z_ p:= 4*f p*(e*Blaze.royalty G); have h : Rate G L 0 Z_:= ((hf.mul_left _).mul_right _)
    unfold b expense; exact ((h.mul_right _).add ((Rate.const _).add h)).mul_left _
  have he : Rate G L 0 b':= by
    refine Rate.mul_left (by simpa only [zero_mul] using (((Rate.const 1).add hx).pow j)) _
  let g p:=1+|b' p|; refine ⟨g,(Rate.const 1).add (Brim.absolut he),?_⟩
  have h₀:= Rate.power (G:=G) (L:=L) (a:=v)
  have h₁:= h₀.mul_left S
  filter_upwards [Delay.shift_pos G L, below' G L hK hb hk.down, below' G L h₀ hb zero_lt_one,
    below' G L h₁ hb (lt_min hR zero_lt_one), below' G L (hK.mul_left G.colorScale) hb hD.pos] with p hp hh hY hΛ hG d c hv
  have ha:0<Y p:=Real.rpow_pos_of_pos hp _; have hs := le_of_lt (lt_min_iff.mp hΛ).2; have he := le_of_lt (lt_min_iff.mp hΛ).1
  have hf : 0 ≤ f p := (Nat.cast_nonneg _).trans hv
  let X:=Positions (Uniform.Primary c G)
  have ht (x:X) (hx: ‖x‖ < Y p) (u:G.El) i : G.chord (chainT u (actual x) i) ≤ M p := by
    apply minorChord hv
    · positivity
    intro i; exact lit_exp i _ hL hC.le (mul_le_mul_of_nonneg_left hx.le hS.le) he
  have hd x (hx : ‖x‖ < Y p)(u:G.El): ∀ᶠ y:X in 𝓝 x,∀ i,G.chord (chainT u (actual y) i)≤ k:= by
    filter_upwards [continuous_norm.continuousAt.eventually (gt_mem_nhds hx)] with y hy; exact fun i=> (ht _ hy u i).trans hh.le
  refine ⟨le_add_of_nonneg_right (abs_nonneg _),fun V hv' i=>?_⟩
  have hu: Brush j _ (b p) (Frame.convertLinks χ k i ∘ actual) V:= germPrice (a:=expense G (f p) e) hD hk V i (modeBasis V (mode_map hs hP V hv' hY.le) hv i) (fun j=> ?_) (hd V hv' i)
  · exact hu.trim.climb ((le_abs_self (b' p)).trans (le_add_of_nonneg_left zero_le_one)) le_rfl
  rw [← chord_dist]; exact (mul_le_mul_of_nonneg_left (ht V hv' i j) G.colorScale_pos.le).trans hG.le
open Grove
variable {c C:Side} (T:Slide.Track C)(o:Site c)
def pixel (i:Bond C): Directions G c→L[ℝ] G.Color := if Slide.grade T i =1 then ContinuousLinearMap.proj (i:=(Slide.sites T o i.1,i.2)) else if Slide.grade T i= -1 then -ContinuousLinearMap.proj (i:=(Slide.sites T o (i.1+step i.2),i.2)) else 0

def lumen : Directions G c→L[ℝ] Positions (Uniform.Primary C G) := (Uniform.tint G (Exterior.Body 1 C)).symm.toContinuousLinearMap.comp (ContinuousLinearMap.pi (fun i=> pixel T o ((Work.E03.poleEquiv C).symm i)))
lemma focus : ‖lumen (G:=G) T o‖ ≤ 1:= by
   refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x=>?_); unfold lumen; rw [one_mul]; apply le_trans (tint_inv_le _); apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2; intro i; change ‖pixel T o _ x‖≤ _; unfold pixel; split
   · exact norm_le_pi_norm x _
   split
   · simp only [_root_.neg_apply,norm_neg]; exact norm_le_pi_norm x _
   simp
lemma sweep (x: Directions G c) : actual (lumen T o x)= Slide.shape T o (soloV x):=by
    funext i; unfold lumen Boulevard.actual; rw [Work.F03.represent_link]; simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply,ContinuousLinearMap.pi_apply]; rw [show (Work.E03.poleEquiv C).symm (i.1, Exterior.coord i.2)=i from (Work.E03.poleEquiv C).symm_apply_apply _]; unfold Slide.shape pixel; split; rfl
    split
    · rw [_root_.neg_apply,Work.F03.exp_neg_color]; rfl
    simp
-- Center at any given flat. convert flat.0
lemma boundFlat {χ:Chi}{B:ℝ} (hk:Reliable G k B) (u:G.El) : Frame.convertLinks (c:=c) χ k u 1=0:= by
   apply (Uniform.tint G _).injective; unfold convertLinks; rw [ContinuousLinearEquiv.apply_symm_apply,map_zero]; funext i
   obtain ⟨j,rfl⟩:= (Work.E03.poleEquiv c).surjective i;
   let V:= Frame.chainT u (1:Config G c); change SliceRows.toLog (fun i=>cutLog χ k (V i)) (pole _)= _; rw [SliceRows.at_pole]; have he:Frame.root (1:Config G c)=1:= by ext l; unfold Frame.root Lattice.gauge carrier; simp [allTrip]
   rw [show V j=1 from (by unfold V Frame.chainT; rw [he]; simp [Lattice.gauge]),hk.kept _ _ (G.chord_one.trans_le hk.down.le), G.mat_one,G.plog_one] -- edit
   rfl
end YM.LocalLTE.FrameBox.Hall
