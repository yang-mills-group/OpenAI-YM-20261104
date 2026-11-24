import YM.SchemeConversionRG11.FirstW.Ore.Re
/-! Point port convergence for the correction. Any external mark stencil on any converging sequence. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function MeasureTheory Filter Set Metric Topology Lattice Pert Align Laurent Position Deck SchemeConversionRG11
open scoped BigOperators Classical ContDiff
variable {G:Gauge}{T:Itinerary}{F:Labels.Frames G}{c:ℕ→Side}{Q:Wash}{R:ℝ} {P:Age G} {W A B:ℕ→Field4 G} {Z:ℕ→Pack F}
def Coal (T:Itinerary)(Q:Wash)(r:ℝ)(A:ℕ→Field4 G) : Prop:= Deaf T ((Metric.closedBall 0 Q.rOut)\{0}) (-1) A ∧ ∃ B:Age G, (∀ i≤4,Book (B i)) ∧ Messed T (4*r) 4 (A-composeR T 4 B)
lemma timbre (p:ℕ→Field4 G)(hQ:Q.rOut<R)(H:Coal T Q R p) (a: Labels.Key G): Helen (fun i=>T.gap i ^ (-2:ℤ) * native a (0:Cover) (p i)) := by
 obtain ⟨_,B,H,h⟩:=H; obtain ⟨v,hv⟩:=poly_tapes (T:=T) a H; have hp:= lingering (p-composeR T 4 B) (show 4*R>0 from mul_pos (by norm_num) (Q.rOut_pos.trans hQ)) h a; simp only [Pi.sub_apply, map_sub,mul_sub] at hp; refine ⟨v,?_⟩; simpa only [sub_add_cancel,zero_add] using hp.add hv
lemma coal_neg {b:ℤ}{K:Set E4}(h: Deaf T K b A) (p:Deaf T K b B): Deaf T K b (A-B) := by
 have he: A-B=fun i=>A i+(fun _:ℕ=>(-1:ℝ)) i • B i:= by funext i; rw [Pi.sub_apply]; simp only [neg_smul,one_smul, sub_eq_add_neg]
 rw [he]; exact deaf_plus h (deaf_mul p _ (⟨_,tendsto_const_nhds⟩))
lemma merge_e {p:E F 6} (h: Helen (fun i=>T.gap i ^(-6:ℤ) • saleF T i Q p (A i) (B i)))(hp:Helen (fun i=>T.gap i ^(-6:ℤ) • saleF T i Q p (B i) (A i))) (hz:Tendsto (fun i=>T.gap i^(-6:ℤ) • chord (A i) (B i) (Full.sections 6 F ((Z i).val p))) atTop (𝓝 0)) :
 Helen (fun i=> T.gap i ^(-6:ℤ) • bleach T Q (Z i) i p (A i) (B i)) := by
 obtain ⟨v,h⟩:=h; obtain ⟨u,hp⟩:=hp; refine ⟨_, ((((h.add hp).const_mul (2:ℂ)⁻¹).sub hz)).congr fun i=>?_⟩; rw [smear,dew_val]; simp only [Complex.real_smul]; ring
private lemma merges (Q:Wash)(p:E F 6)(hc:MarkGrid T c)(h:stampB F Z T Q)(hQ:Q.rOut<R)(v:∀ i≤4,Book (P i))(H:Messed T (4*R) 4 A)(hf:Deaf T ((closedBall (0:E4) Q.rOut)\{0}) (-1) A): Helen (fun k=> T.gap k ^(-6:ℤ) • bleach T Q (Z k) k p (A k) (composeR T 4 P k)) := by
 have ht(k): Helen (fun i=>T.gap i ^(-2:ℤ)*native k (0:Cover) (composeR T 4 P i)):=poly_tapes k v
 have hm: 0<4*R:=mul_pos (by norm_num) (Q.rOut_pos.trans hQ)
 apply merge_e (B:=composeR T 4 P)
 · exact grows_sell hc hQ p H hf ht
 · exact ⟨0,subsist hc hm p H Q v⟩
 exact matW hm p Z h.2 H ht
lemma burn_paid (A B:ℕ→Field4 G)(hQ: Q.rOut<R)(hi:Coal T Q R A)(hp:Coal T Q R B)(p:E F 6)(h:stampB F Z T Q)(hc:MarkGrid T c):
 Helen (fun i=> T.gap i ^(-6:ℤ) • bleach T Q (Z i) i p (A i) (B i)):=by
 obtain ⟨hv,X,hx,Xi⟩:=hi; obtain ⟨hr,Y,hy,Yi⟩:=hp
 let U:= composeR T 4 X; let V:=composeR T 4 Y; let f:=A-U; let g:=B-V; let D:= ((Metric.closedBall (0:E4) Q.rOut)\{0})
 have hf : Deaf T D (-1) f:= coal_neg hv (arms X hx); have hg: Deaf T D (-1) g:= coal_neg hr (arms Y hy)
 have hm : 0< 4*R := mul_pos (by norm_num) (Q.rOut_pos.trans hQ)
 let Φ(x y:ℕ→Field4 G)(k:ℕ):= T.gap k ^(-6:ℤ) • bleach T Q (Z k) k p (x k) (y k)
 have hz(k:ℕ) : Φ A B k=Φ f g k+Φ f V k+Φ g U k+Φ U V k:= by
    let H:= (T.gap k)^(-6:ℤ) • bleach T Q (Z k) k p
    unfold Φ; rw [bleach_sym T Q (Z k) _ _ (g k) (U k)]; change H (A k) (B k)=H (f k) (g k) + H (f k) (V k) +H (U k) (g k)+H (U k) (V k)
    simp only [f,g,Pi.sub_apply,map_sub,LinearMap.sub_apply]; abel
 have h1(k): Helen (fun i=> T.gap i ^(-2:ℤ) * native k (0:Cover) (f i)):=⟨0,lingering f hm Xi k⟩
 have h2(k): Helen (fun i=> T.gap i ^(-2:ℤ) * native k (0:Cover) (g i)):=⟨0,lingering g hm Yi k⟩
 obtain ⟨a,H⟩:= (show Helen (Φ f g) from merge_e (grows_sell hc hQ p Xi hf h2) (grows_sell hc hQ p Yi hg h1) (matW hm p Z h.2 Xi h2))
 have ht (z:Age G)(v:∀ i≤4,Book (z i))(k:Labels.Key G): Helen (fun i=>T.gap i ^(-2:ℤ)*native k (0:Cover) (composeR T 4 z i)):= poly_tapes k v
 obtain ⟨b,F⟩:= merges Q p hc h hQ hy Xi hf (Z:=Z)
 obtain ⟨u,G⟩:= merges Q p hc h hQ hx Yi hg (Z:=Z)
 obtain ⟨z,D⟩:= candles hc X Y hx hy Z h p; exact ⟨_, ((((H.add F).add G).add D)).congr fun i=> (hz i).symm⟩
-- Score anchors suffice for open field movement
lemma cover_east (W : Sight T G) (a:Axis) (Y:Sheets G.Color) {S:Set E4}(H:Score T S (fun i x=> (T.gap i)⁻¹ • W i (x,a)) Y)(D:List Axis):
 Melody T S (-((D.length+1:ℕ):ℤ)) (fun i x=>combine D (field4 a (terms 0 (W i))) x) := by
 refine ⟨Y D,fun σ hs v hv p hp=>?_⟩
 have hh:= H D σ hs v hv (fun i=> wrap (T.period (σ i)) (p i)) (sails_wrap (T:=Rig.path T σ hs) hp)
 have he{i:ℕ}(w:Cover)(D:List Axis): combine D (field4 a (W i)) (wrap (T.period i) w) = combine D (field4 a (terms 0 (W i))) w := by
    induction D generalizing w with
    | nil=>simp [combine, terms,field4]
    | cons b D ih=> rw [combine,up,combine,up]; rw [← ih,← ih]; rw [map_add,wrap_step] -- debug
 apply hh.congr; intro i; simp only [surface,Pi.smul_apply]; rw [show (fun x=> (T.gap (σ i))⁻¹ • W (σ i) (x,a))=(T.gap (σ i))⁻¹ • field4 a (W (σ i)) from rfl, combine_smul,Pi.smul_apply,he];simp only [ped,zpow_neg,zpow_natCast,pow_add,pow_one,smul_smul, mul_inv]
lemma cab (k : Labels.Key G)(x:StepPath T){v:E4}(hx:sails T x v){Q:Wash}(hq:Q.rOut < R)(hp:8*R < ‖v‖): Coal T Q R (fun i=> terms (0:Site (T.period i)) (river (T.gap i) k (x i))) := by
 obtain ⟨u,hU,H⟩:= arrived_poly k x hx (show 4*R>0 from mul_pos (by norm_num) (Q.rOut_pos.trans hq)) (by linarith : 2*(4*R)<‖v‖) 4 -- specify k
 let A i:= river (T.gap i) k (x i); let S:= ((Metric.closedBall (0:E4) Q.rOut)\{0}); have hr : S⊆{a:E4|a≠v}:=fun z hz ht=> hp.not_ge (by rw [←ht]; linarith only [mem_closedBall_zero_iff.mp hz.1,hq,Q.rOut_pos])
 refine ⟨⟨fun i=> (cover_east (T:=T) A i _ (Score.restrict hr (arrived k x hx i)) []),fun i j=>?_⟩,u,hU,H⟩
 exact cover_east (T:=T) A _ _ (Score.restrict hr (arrived k x hx i)) [j]
end YM.RG11.FirstW
