import YM.MSbar.Rolling.Herd
import YM.Progress.DIRECTED_RECIPE.Normalization
import YM.MSbar.Sage.Sailing
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Rolling
open Matrix Function Filter MeasureTheory Set
open Lattice Wilson RG Precision Tree Push
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{c f:Side}{S:StepData c f}
open Progress.DirectedRecipe
-- operator allows scalar ∝ Z. Ratio result.
noncomputable def nut (S:StepData c f)(β:ℝ)(G:Gauge) := (S.penaltyZ β G) ^ Fintype.card (Edge (Site c))
lemma nut_pos (G:Gauge)(S:StepData c f)(b:ℝ) :0<nut S b G:=pow_pos (S.penaltyZ_pos _) _ -- b implicit? 
noncomputable def hut (S:StepData c f)(β:ℝ)(F:Config G f→ℝ)(U:Config G f)(V:Config G c):= nut S β G*S.density β U V *F U
noncomputable def hutfee (S:StepData c f)(β:ℝ)(F:Config G f→ℝ) := fun V:Config G c=> ∫ U:Config G f,hut S β F U V∂prior G f
structure Touch (F:Config G f→ℝ) :Prop where
   shield : GaugeInvariant F
   even_ : ∀ (U:Config G f)(s:Signed)(b:Site f),F (pull s b U)=F U
   stage : RG.Envelope F
   pos U:0< F U
-- *positive* only for correctness over finite period
structure Serves (S:StepData c f)(G:Gauge): Prop where
    branches : S.patch.Branches S.kernel G
    buys : ∀ β (U:Config G f)(V:Config G c)s b,S.density β (pull s (S.ratio.embed b) U) (pull s b V)=S.density β U V
    gauge : ∀ β (U:Config G f) (V:Config G c)t,S.density β (gauge t U) (gauge (t ∘ S.ratio.embed) V)=S.density β U V -- gauge ambiguous
    thick : Bid.Larger (G:=G) S
variable {a b x:ℝ}(F:Config G f→ℝ)(h:Serves S G)(hd:Touch F)
local notation "M"=>nut S b G
lemma earnsH (V:Config G c) : hutfee S b F V=M*S.push b F V:=by unfold hutfee hut StepData.push; simp_rw [mul_assoc,integral_const_mul]; rfl
include hd h
lemma safePush : Touch (S.push b F) :=by
    let H:= prior G f; let K:= S.push b F; have ht:Integrable F H:=hd.stage.integrable _; have hK:= S.isKernel h.branches b; have hp(V:Config G c) : Integrable (fun w=> S.density b w V*F w) H:= StepData.push_slice hK V F ht
    have hh (V:Config G c)(W:Config G c)(P:Config G f→ Config G f) (hz:MeasurePreserving P H H) (hx:∀ i,F (P i)=F i ∧ S.density b (P i) V= S.density b i W): K V=K W:=by
        let f₀:=(fun y=> S.density b y V*F y); have hs:=integral_map (φ:=P) (μ:=H) (f:=f₀) hz.aemeasurable (by rw [hz.map_eq]; exact (hp V).aestronglyMeasurable); rw [hz.map_eq] at hs; apply hs.trans; apply integral_congr_ae; filter_upwards with i; unfold f₀; rw [(hx i).1,(hx i).2];rfl
    have hi(V:Config G c):0<K V:=push_strict S b h.branches hd.pos ht _
    refine ⟨fun t U=>?_, fun U s w=>hh _ _ (pull s (S.ratio.embed w)) (prior_pull ..) (fun i=> ⟨hd.even_ i s _,h.buys ..⟩),?_,hi⟩
    · let u:= t ∘ S.ratio.parent; apply hh (gauge t U) U (gauge u) (prior_gauge u); intro i
      have hv: t= u ∘ S.ratio.embed:=funext fun x=> (congr_arg t (S.ratio.embed_parent x)).symm
      exact ⟨hd.shield u _,by nth_rw 1 [hv]; exact h.gauge ..⟩
    · obtain ⟨C,hC⟩:= hK.bound; obtain ⟨A,hA⟩:= hd.stage.cost; refine ⟨?_,C*A,fun x=> ?_⟩
      · let q(y:Config G f × Config G c):= S.density b y.1 y.2*F y.1; have hf:Measurable q:= hK.meas.mul (hd.stage.meas.comp measurable_fst); exact hf.stronglyMeasurable.integral_prod_left'.measurable -- inspect right
      rw [Real.norm_of_nonneg (hi x|>.le)]; let C' := C*A; suffices h: K x≤∫ _:Config G f,C'∂H by simpa using h -- H univ prob
      have hc(U:Config G f):0 ≤ S.density b U x:= S.density_positive ..; exact integral_mono (hp x) (integrable_const _) (fun i=>mul_le_mul (hC i x) ((le_abs_self _).trans (hA i)) (hd.pos i|>.le) ((hc i).trans (hC ..)))
lemma hut_rep (B:Forest S.ratio)(V:Config G c) : hutfee S b F V = ∫ i,hut S b F (B.drape i) V∂ B.order G :=by
    rw [earnsH,B.pushing (S.isKernel h.branches b) F V hd.shield (hd.stage.integrable _) (fun t i=> h.gauge ..)]; unfold hut; simp_rw [mul_assoc]; rw [integral_const_mul];rfl
lemma hutD (V:Config G c)(B: ℝ) (h:Serves S G) : Envelope (fun U: Config G f=> S.density B U V):=by
    let hk:=S.isKernel h.branches B
    let g(p:Config G f × Config G c):=S.density B p.1 p.2; have hf:Measurable g:=hk.meas
    let x:Config G f→ Config G f × Config G c:= fun i=> (i,V); have hp : Measurable x:=measurable_id.prodMk measurable_const
    obtain ⟨C₀,h₀⟩:=hk.bound; refine ⟨(show Measurable (g ∘ x) from hf.comp hp),C₀,fun i=>?_⟩; rw [Real.norm_of_nonneg (hk.positive _ _)]; exact h₀ i V
lemma hutEnv (V:Config G c) : Envelope (fun U=> hut S b F U V):=by
    have he:Envelope (fun U:Config G f=> S.density b U V):=hutD F h hd V b h -- signature
    let q:Config G f→ℝ:=fun U=>S.density b U V; let k:Config G f→ℝ:=fun _=>nut S b G
    exact (Envelope.mul (f:=fun i=> k i*q i) (g:=F) ((show Envelope k from Envelope.const _) |>.mul he) hd.stage)
lemma hutAlive (V:Config G c)(U:Config G f) :0< hut S b F U V:=mul_pos (mul_pos (nut_pos ..) (density_strict S b h.branches ..)) (hd.pos U)
lemma tipT : Touch (hutfee S b F):=by
    have he : hutfee S b F=(fun x=>M * S.push b F x):=funext (fun x=> earnsH F x); rw [he]; let k:=S.push b F; obtain ⟨h₁,h₂,h₃,h₄⟩:=safePush (b:=b) F h hd; exact ⟨fun t v=>congr_arg (M*·) (h₁ t v),fun U s b=>congr_arg _ (h₂ U s b), (Envelope.const M).mul h₃,fun U=>mul_pos (nut_pos ..) (h₄ U)⟩ -- earns .. check
lemma pointed (x: Config G c)(U:Config G f) :hut S b F U x=∑ t,S.likelihood U t*(Real.exp (-b*noiseTaylor S x U t)*F U):=by
    unfold hut StepData.density; simp_rw [Heath.toward]; rw [Finset.mul_sum,Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; unfold nut; have he:S.penaltyZ b G≠0:=(S.penaltyZ_pos _).ne'; rw [inv_pow]; field_simp
variable (ha:0<a)
include ha
lemma husk {p:ℕ}(hx:0<x)(hg:∀ i:Config G f,F i≤ Real.exp (-a*Wilson.energy i /x^2)/x^p)
    (V:Config G c)(U:Config G f)(u:ℝ)(hz:∀ t,0<S.likelihood U t→ -(quota S U V t a ^2)/x^2 ≤ u): hut S (x⁻¹^2) F U V ≤ Real.exp u /x^p:=by
    let y:= Real.exp u /x^p; rw [pointed F h hd]; refine (Finset.sum_le_sum (g:=fun t=> S.likelihood U t*y) (fun i _=>?_)).trans_eq (by rw [← Finset.sum_mul,S.chosen h.branches,one_mul])
    by_cases hz':0 < S.likelihood U i
    swap
    · rw [show S.likelihood U i=0 from le_antisymm (not_lt.mp hz') (S.likelihood_pos ..),zero_mul,zero_mul]
    apply mul_le_mul_of_nonneg_left _ hz'.le; apply (mul_le_mul_of_nonneg_left (hg U) (Real.exp_pos _).le).trans; rw [← mul_div_assoc, ← Real.exp_add]; apply div_le_div_of_nonneg_right (Real.exp_monotone _) (pow_nonneg hx.le p)
    apply le_trans _ (hz i hz'); rw [quarrel a ha]; apply le_of_eq; ring
-- Energy cap payment
lemma rises (x:ℝ)(hx:0<x)(κ:ℝ)(hk:0<κ)(L:ℝ)(hQ:κ*L≤1)(p:ℕ) (hc:∀ i:Config G f,F i≤Real.exp (-a*Wilson.energy i/x^2)/x^p)
    (hL:∀ U:Config G f,∀ V:Config G c,∀ t,0<S.likelihood U t→ Wilson.energy V ≤ L*quota S U V t a ^2)(V: Config G c): hutfee S (x⁻¹^2) F V ≤ Real.exp (-κ*Wilson.energy V/x^2)/x^p:=by
    let w:= Real.exp (-κ*Wilson.energy V/x^2)/x^p; unfold hutfee; change _ ≤ w; rw [show w=∫ _:Config G f,w∂prior G f from (by simp)]; apply integral_mono ((hutEnv F h hd V).integrable _) (integrable_const _); intro i; refine husk F h hd ha hx hc V i _ (fun t he=> ?_); apply div_le_div_of_nonneg_right _ (pow_nonneg hx.le 2); rw [neg_mul,neg_le_neg_iff]; refine (mul_le_mul_of_nonneg_left (hL i V t he) hk.le).trans ?_; rw [←mul_assoc]; exact mul_le_of_le_one_left (sq_nonneg _) hQ
end YM.MSbar.Rolling
