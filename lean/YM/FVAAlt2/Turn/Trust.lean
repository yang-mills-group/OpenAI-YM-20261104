import YM.FVAAlt2.Turn.Gallery
import YM.FVAAlt2.Turn.Horizon
/-! Rotation on the high Taylor sector (curtailed angular H only).
 `frame` charts: transfer supplies SAME radii by *within-address chart adjustment*. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.FVA.Town
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color Book _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train Dock Emit
open Signal Book Convolve High Detect Domain Tone Tone.Frame Momentum Outlook
open _root_.YM.MS.Wind _root_.YM.MS.City Native Native.Wilsonian
open Motions
open scoped Topology BigOperators ContDiff Interval
set_option linter.unusedSectionVars false
variable {G:Gauge} {I E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E]{h x:ℝ}
variable (s:Signed){m n k:ℕ}
lemma left_bundle (a b:BH G): (flagS (m:=0) (hand s) G).fieldC a ( passN s b ) =if a=b then tick s a else 0:= by
  rcases a with ⟨⟨_|i,c⟩,d⟩ <;> rcases b with ⟨⟨_|j,p⟩,q⟩ <;> simp [ passN,flagS,leggo,Spin.prop, rayS,Spin.shadow,tick,negateField ] <;> try (solve|split_ifs <;> first | rfl | tauto) 
  all_goals try ( rw [hand_s]; simp only [EmbeddingLike.apply_eq_iff_eq])
  all_goals split_ifs <;> first| rfl| grind -- perf
lemma sk_transport (t:ℝ): Transport (flagS (m:=0) (hand s) G) (Cpu G t) (Cpu G t):= by
  intro p a b; obtain ⟨a,rfl⟩:= ( passN s ).surjective a; obtain ⟨b,rfl⟩:= ( passN s ).surjective b; rw [show (flagS (m:=0) _ G ).volp p=s.act p from rfl,turn_p]; simp_rw [left_bundle]; simp [mul_ite]; ring
variable {F H:Law G}
local notation "K"=> flagS (m:=0) (hand s⁻¹) G
local notation "S"=> turnW G s
lemma certA (s:Signed) (w:List (Lane4 G)): turnW G s F w= SideS s⁻¹ w * F (w.map (permute s⁻¹)):= hand_index s⁻¹ w F -- beware notation shadow
lemma lower_cyc (t:ℝ)(F:Law G)(h:Pass (Cpu G t) F μzone): S (Ccy (Cpu G t) F μzone) = Ccy (Cpu G t) (S F) μzone:= (K).leadC (μ:=μzone) (measureVeh s⁻¹) (( _root_.YM.MS.City.seat s⁻¹).measurableEmbedding) (sk_transport s⁻¹ t) F h
lemma woods (t:ℝ)(F H:Law G)(h:SignedScope true F): S (tree Landau.parity (Cpu G t) F H)= tree Landau.parity (Cpu G t) F (S H):= by
   let V:=Cpu G t; rw [show S=beam K from rfl, (sk_transport s⁻¹ t).gatherR _ _ ( X_even G t ) (X_even G t) ]; exact tree_agrees _ _ _ _ _ fun w hw=> (hand_index ..).trans (h s⁻¹ w (fun _=>hw)) -- scope type

lemma anti_cube (F:Law G) : turnW G s⁻¹ ( S F )=F:= by
   unfold turnW Γx; funext v; rw [inv_inv]; refine Eq.trans (move_comp (C:=G.ColorIndex) (hand s) (hand s⁻¹) v F).symm ?_; rw [trail_s,inv_mul_cancel, identity_motor]; exact turnZ v F
lemma poseXY (f: Dot G Lattice.Cover) : run (Orient.pose s f)=S (run f):=by
   apply (show Injective (turnW G s⁻¹) from LeftInverse.injective (g:=turnW G s) (fun v=> by simpa only [inv_inv] using! anti_cube s⁻¹ v)); rw [anti_cube]
   ext v; rw [certA,inv_inv, Tone.by_shift]; rw [← mul_assoc, show SideS s v*(v.map _).prod=1 from twice_S s v, one_mul]
abbrev deck (s:Signed)(w:Wire (BH G) E QP) : Wire (BH G) E QP := w.map fun i=> (passN s i.1,(hand s).turn.toContinuousLinearMap.comp i.2)
lemma slideP (w:Wire (BH G) E QP) (x:E): (sail w x).map (permute s)=sail (deck s w) x := by induction w with| nil=>rfl| cons i l ih=> rw [sail_cons,List.map_cons,passenger,ih];rfl
lemma slide_dim (w:Wire (BH G) E QP): fieldDim wfield (deck s w)=fieldDim wfield w:= by induction w with| nil=>rfl| cons i l ih=> unfold deck; rw [List.map_cons,field_cons,field_cons]; unfold deck at ih; rw [ih];rfl
lemma slide_fee(w:Wire (BH G) E QP)(x:E): SideS s (sail w x)=(w.map (tick s ∘ Prod.fst)).prod:= by induction w with| nil=>rfl| cons i w ih=> simp_rw [sail_cons, SideS, List.map_cons,List.prod_cons]; exact congr_arg (tick s i.1 * ·) ih -- metav placeholder
lemma tagC {T:I→Law G}(w:Wire (BH G) E QP): Plane.Chart ((turnW G s) ∘ T) w=(fun i x=>(w.map (tick s⁻¹ ∘ Prod.fst)).prod * Plane.Chart T (deck s⁻¹ w) i x):= by funext i x; unfold Plane.Chart Function.comp; rw [certA, slide_fee, slideP]; rfl -- check parser
-- For space budgets at all weights.T
variable {t:ℤ} {A C:Reading G} {D:Recount G}
lemma tri_m (hx:Trust false t A C k): Trust false t (( S ) ∘ A) (( S ) ∘ C) k := by
   intro E _ _ w hw hh
   let u:=deck s⁻¹ w; obtain H := hx E u (fun e=> Bool.noConfusion e) (by simpa only [u,deck,List.length_map] using hh); unfold Light at *
   let L:=(w.map (tick s⁻¹ ∘ Prod.fst)).prod; let bW:=High.meet.primary
   change Like bW.full bW _ (Plane.Chart _ w) (Plane.Chart _ w) _; rw [show Plane.lane High.meet (⇑S ∘ A)= (S)∘ Plane.lane High.meet A from rfl, show Plane.lane High.meet (⇑S ∘ C)=(S) ∘ Plane.lane High.meet C from rfl, tagC, tagC, ← slide_dim s⁻¹ w ]; exact Like.L H (ContinuousLinearMap.mul ℝ ℂ L)
end YM.MS.FVA.Town
