import YM.LocalLTE.Hall.Books
import YM.LocalLTE.Hall.Twirl
/-! Budget handoff, oxidizing pre+post affines. No receptive assumptions on stencil prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Collection.Price
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf
open LocalLTE.FrameBox LocalLTE.FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable (G : Gauge) {n : Side} {j:ℕ} {C V: ℝ}
attribute [local instance] Gauge.frobInner
-- uniform over all low rows. weights only station 
lemma picks (j:ℕ) : ∃ p:ℝ,0≤p∧∀ (n:Side)(o:Site n)(i:PlaqAxes)(v: Directions G n),‖v‖ ≤ 1 → Brush j p 1 (fun u=>petals (soloV u) o i) v:=by
    obtain ⟨c,hc,H⟩:=LocalLTE.Cabana.thick G j
    let V:=royalty G
    let P:ℝ:=4*(c*V)
    let M:= 1*(1+P)^j
    have hv:0 ≤ royalty G:=zero_le_one.trans (royalty_ge _); have hp:0≤M:=by unfold M P V; positivity
    refine ⟨M,hp,fun n o i v h=>?_⟩
    have h:= H n v h
    have hh (a b:Lattice.Step): Brush j M 1 (fun u=> plate (soloV u) o a b) v:=by
       have he : Brush j V P (fun u=> G.mat (Lattice.travel (soloV u) o (Lattice.oriented a b))) v:= by convert (Blaze.tour (Lattice.oriented a b) o h.pos h.atLink) using 1; rw [show (Lattice.oriented a b).length=4 from rfl]; norm_num [P,V]
       exact (Blaze.sculpt (g:=fun v=>Lattice.travel (soloV v) o (Lattice.oriented a b)) he).trim
    let a:= i.val.1; let b:=i.val.2
    have he x:= (hh x (posDir b)).separating (hh x (negDir b))
    have hx:= ((he (posDir a)).separating (he (negDir a))).smul (4:ℝ)⁻¹
    apply hx.climb _ le_rfl
    rw [norm_inv,Real.norm_of_nonneg (by norm_num : 0 ≤ (4:ℝ))]; linarith
lemma priceF (j:ℕ) : ∃ p:ℝ,0≤p∧∀ (n:Side)(o:Site n)(i:PlaqAxes)(v:Directions G n), ‖v‖≤1→Brush j p 1 (fun x=> G.price (faceValue (soloV x) (o,i))) v:=by
    obtain ⟨c,hc,H⟩:=LocalLTE.Cabana.thick G j
    let V:=royalty G; let P:=4*(c*V); let M:= (V + ‖(1:G.Mat)‖)*(1+P)^j
    let F':=(innerSL ℝ (E:=G.Mat)); let s:=(G.colorScale^2*2)⁻¹
    have hv:0≤royalty G:=zero_le_one.trans (royalty_ge _); have hP:0≤P:=by unfold P V; positivity
    refine ⟨‖s‖ * ((‖F'‖*(M*M))*(1+(1+1))^j),?_,fun n o i v hv=>?_⟩; · positivity
    let l:= square i.val.1 i.val.2; let t u:= G.mat (faceValue (soloV u) (o,i)); have h:=H n v hv
    let w (x:Directions G n):= t x-1
    have he:Brush j V P t v := by
       convert (Blaze.tour l o h.pos h.atLink) using 1; rw [show l.length=4 from rfl]; norm_num [P,V]
       rfl
    have hz := (he.separating (Brush.certified hP 1)).trim; apply ((hz.twins hz F').trim.smul s).shimmy
    filter_upwards with i'; let u:= faceValue (soloV i') (o,i); change G.price u = s * inner ℝ (G.mat u-1) (G.mat u-1); rw [real_inner_self_eq_norm_sq]; have hf:= G.chord_price u; change (‖G.mat u-1‖/ G.colorScale)^2 = _ at hf; unfold s; have he:= G.colorScale_pos; field_simp at hf ⊢; linarith
lemma stretch (j:ℕ) : ∃ c:ℝ,0 ≤ c ∧ ∀ (n:Side)(o:Site n) (i:PlaqAxes)(b:PlaqAxes) (x:Directions G n),‖x‖≤1 → Brush j c 1 (fun v=> inner ℝ (petals (soloV v) o i) (petals (soloV v) o b)) x:=by
    obtain ⟨c,hc,h⟩:= picks G j; refine ⟨‖innerSL ℝ (E:=G.Color)‖*(c*c)*(1+(1+1))^j,by positivity, fun n o i b x hx=> ?_⟩; exact ((h n o i x hx).twins (h n o b x hx) (innerSL ℝ)).trim
lemma vial (j:ℕ):∃ c:ℝ,0≤c∧∀ (n:Side)(o:Site n)(q:PlaqAxes→PlaqAxes→ℝ)(t:ℝ), (∀ i j,|q i j| ≤ t) → ∀ x:Directions G n,‖x‖≤ 1 → Brush j (t*c) 1 (counter q o ∘ soloV) x:= by
   obtain ⟨d,hd,h⟩:= stretch G j
   let f:= Fintype.card PlaqAxes; let a := ‖(2:ℝ)⁻¹‖*(f*(f*d)); refine ⟨a,by unfold a; positivity,fun n o q t hv x hx=>?_⟩
   have hg i b (_h:b∈(Finset.univ:Finset PlaqAxes)):= ((h n o i b x hx).smul (q i b)).climb (mul_le_mul_of_nonneg_right (hv _ _) hd) le_rfl
   have hu:=(Brush.spree Finset.univ _ _ zero_le_one (fun i _=> Brush.spree Finset.univ _ _ zero_le_one (hg i))).smul (2:ℝ)⁻¹
   apply (hu.climb ?_ le_rfl).shimmy
   · filter_upwards with i; simp only [counter,Function.comp_apply,quad,smul_eq_mul,div_eq_inv_mul]
   apply le_of_eq; simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; unfold a f; ring
end YM.AnalyticBridge.VerifiedReset.Collection.Price
