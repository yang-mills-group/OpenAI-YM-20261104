import YM.MS.Vista.Dice
/-!
# Estimates for image defect contribution from a bulk vertex; solve half-root branches with no deterioration on momentum derivatives. Uniform smooth costs.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Vista
open Set Function Filter Finset Metric MeasureTheory Real High
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit
open scoped Topology ContDiff Interval
variable {I E:Type}{G:Gauge}[NormedAddCommGroup E][NormedSpace ℝ E]{S:Scale I}
 {K L:I→Latch.Edge G}{X Y:I→Law G}{h x y:I→ℝ}{P:Belt I}
 local notation "Γ"=> field (parity ( C:=G.ColorIndex ) (A:=Axis))
abbrev Price (S:Scale I) (K:I→Latch.Edge G)(A:I→ℝ): Prop:= CourseK S A K ∧ ∀ i j, Fiddle.Zone S (fun q=>K q i j) (fun q=> S.length q ^ ( (4:ℤ)-wfield i-wfield j )* A q )
def PerK (K:I→Latch.Edge G) := ∀ p,SpeaksK ( K p )
def Voiced (F:I→Law G): Prop:= ∀ i, Speaks (F i)
lemma veiled (h:PerK K)(i j:BH G)(p:I): Veiled ( K p i j ):= fun q=> ⟨1,norm_one,funext (fun u=>by rw [ pin_C (h p i j) q u, one_smul ]) ⟩
lemma carrot (hv:PerK K)(hp:Price S K x)(i j:BH G){r:ℝ}(z:Half)(P:E→L[ℝ] QP)(he:∀ v:E,v∈Metric.closedBall 0 r→ 1≤‖P v+Coord z‖ ∧ ‖P v+Coord z‖≤wide)(n:ℕ): Costs ( Slice S (cave r) ) S (fun i' v=> K i' i j ( P v+Coord z )) (fun i' _=> S.length i' ^ ((4:ℤ)-wfield i-wfield j) * x i' / S.length i'^n):= by
    let D:=fun i':I=>cave ( E:= E ) r i'; let a(i':I):=S.length i' ^ ((4:ℤ)-wfield i-wfield j) * x i'; -- remove
    refine Costs.raise ( tilted P (Coord z) ( ( Fiddle.ride ( hp.2 i j ) ( veiled hv i j ) ) n ) ( Q:=Slice S D ) (fun i x hp=>Metric.mem_closedBall.mpr (by simpa using ( he x hp ).2)) ?_ ) ( Cost.of_le ?_ ); · refine ⟨1,zero_lt_one,1,fun i p h=>?_⟩; simp only [pow_one,one_mul,mul_one,Scale.strict,Slice]; exact le_mul_of_one_le_right ( S.basic_pos i |>.le ) ( S.one_le_weight i p ) -- Belt only, use weight inequality
    intro i' p h; have hi: S.length i' ≤ S.weight i' ( P p+Coord z ):= by obtain hx:= ( he p h|>.1 ); unfold Scale.weight; nlinarith [ S.pos i' ]; -- positivity of a(i')
    exact div_le_div_of_nonneg_left ( noPole ( hp.2 i j ) _ ) (pow_pos ( S.pos i') _) ( pow_le_pow_left₀ ( S.pos _|>.le) hi n )
-- d−momentum evaluation unrestricted.T.L. use variable ±q.
abbrev siteL (x:Wire (BH G) E QP): E→L[ℝ] QP:= -( (2:ℝ)⁻¹ • net x ) -- net x requires CL.norm. ones
lemma siteL_pp (x:Wire (BH G) E QP)(u:E): siteL x u= -( decap ( net (sail x u)) ):= by rw [sail_net]; rfl -- ∘ notation minus.Real.scalar
abbrev spectrumP (x:Wire (BH G) E QP) (i j:BH G): Wire (BH G) ( E × QP ) QP:=
    let P:=(ContinuousLinearMap.fst ℝ E QP); let T:=ContinuousLinearMap.snd ℝ E QP; (i,siteL x∘L P + T)::(j, siteL x ∘L P - T):: Wire.lift x P
lemma cycl_Net (x:Wire ( BH G ) E QP) (i j:BH G): Course true ( spectrumP x i j ):= by
    intro v; let N:=net x; let V:=siteL x; have he : V+(V+N)=0:= by unfold V siteL N; rw [← add_assoc, ← neg_add, ← two_smul ℝ, smul_smul, mul_inv_cancel₀ (by norm_num : (2:ℝ)≠0), one_smul ]; abel
    unfold spectrumP; rw [ net_cons, net_cons, lift_net ]; let L:=ContinuousLinearMap.fst ℝ E QP; let T:=ContinuousLinearMap.snd ℝ E QP; change ( V ∘L L + T ) + ( ( V ∘L L - T ) + _ )=0; calc 
                _ = ( V + ( V+N ) ) ∘L L:= by rw [ContinuousLinearMap.add_comp,ContinuousLinearMap.add_comp]; abel -- def.
                _ = _:= by rw [he]; simp
lemma costSpec (x:Wire (BH G) E QP)(i j:BH G) : pitch ( spectrumP x i j )= wfield i+wfield j+pitch x:= by simp only [ field_cons, spectrumP, pitch, field_lift,add_assoc ]
lemma order_spec (x:Wire (BH G) E QP)(i j:BH G)(p:E×QP): sail (spectrumP x i j) p = ((i,siteL x p.1+p.2)::( j,siteL x p.1-p.2)::sail x p.1):= by simp [spectrumP]
lemma topic (w:Half): Coord w+Coord w = rep (Lattice.lift w):= by rw [← two_smul ℝ]; exact ( Orbit.ℝwalk (2:Side) (Lattice.lift w) ) -- cast
lemma dualZ (x:Wire (BH G) E QP)(i j:BH G)(v:Half)(F:Law G)(h: Speaks F)(p:E):
    F ( (i,siteL x p + Coord v):: (j,siteL x p+Coord v)::sail x p )= F (sail (spectrumP x i j) (p,Coord v)):= by rw [order_spec]; apply h; refine .cons ⟨rfl, congrQ.normal _⟩ (.cons ⟨rfl,?_⟩ (asc _)); refine ⟨ Lattice.lift v,?_⟩; dsimp only; rw [← topic ]; abel
lemma image_X (h:∀ i,1≤ S.length i)(hf:Price S K x)(he: PerK K)(hp: Lease true true S X y) (hx:Voiced X)(w:Wire ( BH G ) E QP)(i j:BH G)(v:Half) : Bound S (fun t p=> K t i j (root_q ( net (sail w p)) v ) * X t ( (i,root_q (net (sail w p)) v)::(j,root_q (net (sail w p)) v)::sail w p )) (fun t=> S.length t ^ pitch w * positive S 4 x y t ) := by
    let Q:= siteL w; let G':=spectrumP w i j; let U t:= S.length t^((4:ℤ)-wfield i-wfield j)*x t; let V t:= S.length t ^ pitch G'*y t; have Hζ : (fun t=> S.length t ^ pitch w * positive S 4 x y t )= U* V:= by funext t; unfold U V G'; rw [Pi.mul_apply,costSpec]; unfold positive; have he: pitch w+4=(4-wfield i-wfield j)+(wfield i+wfield j+ pitch w) :=(by omega); rw [show S.length t^(4:ℕ)=S.length t^(4:ℤ) from rfl, ← mul_assoc, ← zpow_add₀ ( S.pos t ).ne', he, zpow_add₀ ( S.pos t ).ne' ]; ring; -- bad tactic
    let L:E→L[ℝ] ( E× QP):= ContinuousLinearMap.inl ℝ E QP; have hs (u:E)(q:QP): L u+(0,q)=(u,q):= Prod.ext (by simp [L]) (by simp [L]); obtain hX: Bound S (Plane.Chart X G') V:= hp (E×QP) _ (cycl_Net w i j) (fun _=> by simp [spectrumP,G']);
    rw [Hζ]; simp_rw [root_q, ← siteL_pp, dualZ w i j v _ (hx _)]; have hu (p:E)(t:I): X t (sail (spectrumP w i j) (p,Coord v))= Plane.Chart X (spectrumP w i j) t (L p+(0,Coord v)):= by rw [ hs ]; rfl
    simp_rw [ hu ]
    by_cases hz:v=0; · subst v; simp_rw [ ξ_zero,add_zero, show (0,0)= (0:E×QP) from rfl, add_zero ]; apply Costs.mul (Bound.linear Q ( hf.1 i j ) ) (Bound.linear L hX) -- rewrite L u+(0,0) 
    obtain ⟨r,hr,hv'⟩:= pin_cave Q hz; let D:=cave (E:=E) ( I:=I ) r; let F':I→E→ℂ:=fun i p=> Plane.Chart X G' i (L p+(0,Coord v)); apply blendC (B:=D) ( C:=(fun i=> (D i)ᶜ)) (fun i p=> em _) ?_ ?_ _;
    · apply shoulder S.length h ( S_late L (0,Coord v) h hX ) (fun k=> carrot he hf i j v Q hv' k )
    · have hm(i:I)(p:E) (h:p∈(D i)ᶜ): r≤‖p‖:= le_of_lt ( lt_of_not_ge (fun hz=> h (Metric.mem_closedBall.mpr (by simpa using hz))) ); -- no i
      exact Costs.mul ( S_front Q (Coord v) r hr (fun i p hp=>hm i p hp) (hf.1 i j) ) ( S_front L (0,Coord v) r hr (fun i p hp=> hm i p hp ) hX )
    exact fun t=>mul_nonneg ( noPole (hf.2 i j) _ ) ( hX.nonneg t 0 trivial )
lemma pocket (h:∀ i,1≤S.length i)(hv:Price S K x)(hf:PerK K)(hx:Voiced X)(hm:Lease true true S X y)( hp:nn x)( hu:nn y): Lease false false S (fun i=> birth ( K i ) ( X i )) ( positive S 4 x y ):= by
    intro E _ _ w _ hT; unfold Cape Plane.Chart birth Hβ detach; apply Costs.L (ContinuousLinearMap.mul ℝ ℂ (1/16:ℂ)); refine Costs.sum _ (fun i _=> Costs.sum _ (fun j _=>Costs.sum _ (fun k _=> image_X h hv hf hm hx w j k i) ?h) ?h ) ?h; exact fun i p _=> pos_nn _ ( np _ hu hp _ ) _ i
end YM.MS.Vista
