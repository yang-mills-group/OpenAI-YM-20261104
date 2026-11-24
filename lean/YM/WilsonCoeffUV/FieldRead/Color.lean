import YM.WilsonCoeffUV.FieldRead.LeadingPart
/-!
# Action of colors and H on Snap evaluations (unintegrated tests at origin)
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 45000
noncomputable section
namespace YM.WilsonCoeffUV.Fountain
open Filter Function Set Laurent Lattice RG Exterior Precision Next.Free Gauge Power Bloch Metric Matrix Work.F08
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Blue FreeResolvent Bank
open Embroider
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{r h D l m p:ℕ}{A C s t :ℝ}

def rock (v:Fin r→Edge Cover)(u:Fin r→G.ColorIndex):Fin r→ YForest G:=fun i=>stone (v i) (u i)

-- diagonal equality before CLM extensions
lemma lost (u:Fin r→YForest G)(X:Snap G h): Tensor.diagonal (latent (skyline h u l)) X = leading l (fun t:ℝ=> mite u (t•X)):=
    (windface u (fun _: Fin l=>X)).trans (leading_tensor _ _ ((mite_smooth _).of_le le_top)).symm

lemma lead_sc {u:ℝ→ℝ}(h:ContDiffAt ℝ (↑l) u 0)(c:ℝ): leading l (fun x=> c • u x)= c • leading l u:=by
    unfold leading; rw [iteratedDeriv_fun_const_smul h,smul_comm]

lemma donated (v:Fin r→Edge Cover)(u:Fin r→ G.ColorIndex)(X:Snap G h)(H:Hol G)(g:G.El):
    Tensor.diagonal (latent (skyline h (rock v u) l)) (Cast g X)=∑ j:Fin r→G.ColorIndex,(∏ i,gammaC g (u i) (j i)) • Tensor.diagonal (latent (skyline h (rock v j) l)) X:=by
   let f (j:Fin r→G.ColorIndex)(x:ℝ):= mite (rock v j) (x•X)
   let p (j:Fin r→G.ColorIndex):ℝ:=∏ i,gammaC g (u i) (j i)
   let L : ℝ→L[ℝ]Snap G h:= (ContinuousLinearMap.id ℝ ℝ).smulRight X
   have hx : Tendsto L (𝓝 0) (𝓝 0):=by rw [←map_zero L]; exact L.continuous.tendsto _
   have hf j : ContDiffAt ℝ (↑l) (f j) 0:= by
      have hz : ContDiffAt ℝ (↑l) (mite (rock v j)) (L 0):=by rw [map_zero]; exact (mite_smooth ..).of_le le_top
      exact hz.comp _ L.contDiff.contDiffAt
   simp_rw [lost]; trans leading l (fun t=>∑ j,p j • f j t)
   · unfold leading; apply congr_arg ((l.factorial:ℝ)⁻¹ • ·); apply Filter.EventuallyEq.iteratedDeriv_eq
     filter_upwards [hx.eventually (mural_dot H v u g)] with t ht; rw [show t • Cast g X= Film.colorIn G h g (L t) from Eq.symm (map_smul (Film.colorIn G h g) t X)]; exact ht
   rw [lead_sum _ (fun j t => p j • f j t) (fun j _=> ContDiffAt.const_smul _ (hf j))]
   exact Finset.sum_congr rfl (fun i _=> lead_sc (hf i) (p i))

lemma borne {R:Type*}[AddCommGroup R][UniformSpace R][IsUniformAddGroup R][T2Space R][CompleteSpace R]{F:(Fin r→YForest G)→ R}(h:Summable F): (∑' x,F x)=∑' v,∑ u,F (rock v u):=by
    let b : ((Fin r→Edge Cover)×(Fin r→G.ColorIndex))≃ (Fin r→ YForest G):={
       toFun x:= rock x.1 x.2
       invFun x:= (fun i=>feather (x i),fun i=>(x i).2.2)
       left_inv x:=Prod.ext (funext fun _=>feather_at ..) rfl
       right_inv x:= by funext i; change stone (feather (x i)) _=_; obtain ⟨v,j,h⟩:=every_stone (x i); change stone _ (x i).2.2=_; rw [←h,feather_at]; rfl }
    rw [← b.tsum_eq F]; change tsum (F ∘ b)=_; rw [((b.summable_iff).mpr h).tsum_prod]; simp_rw [tsum_fintype]; rfl

lemma lat_sum (c:Volume D)(F:ChamberTen G (Vote D) r) (h l:ℕ)(hc:Twig 0 s A F)(he:0<s)(X:Snap G h):
    Tensor.diagonal (latent (arret c F h l)) X=∑' v, F v c * Tensor.diagonal (latent (skyline h v l)) X:= arret_pays c F h l hc he (fun _=> casing G h X)
lemma lat_income (c:Volume D)(F:ChamberTen G (Vote D) r)(hc:Twig 0 s A F)(he:0<s)(X:Snap G h): Summable (fun v=> F v c * Tensor.diagonal (latent (skyline h v l)) X):=
    (((arret_bill c F h l hc he).2.1.of_norm.hasSum.map (ContinuousMultilinearMap.apply ℝ (fun _:Fin l=> Lawn (Cart G h)) ℝ (fun _=> casing G h X)) (ContinuousMultilinearMap.apply ℝ (fun _:Fin l=> Lawn (Cart G h)) ℝ (fun _=> casing G h X)).continuous)).summable
lemma arret_mural (c:Volume D)(H:Hol G){F:ChamberTen G (Vote D) r}(hc:Twig 0 s A F)(he:0<s)(g:mural F)(u:G.El)(X:Snap G h): Tensor.diagonal (latent (arret c F h l)) (Cast u X)=Tensor.diagonal (latent (arret c F h l)) X:=by
    rw [lat_sum _ _ _ _ hc he, lat_sum _ _ _ _ hc he, borne (lat_income c F hc he (Cast u X)),borne (lat_income c F hc he X)]
    apply tsum_congr; intro v
    let V (i:Fin r→ G.ColorIndex):= F (rock v i)
    let M (i j:Fin r→ G.ColorIndex):=∏ k,gammaC u (i k) (j k)
    let W (i:Fin r→G.ColorIndex):= Tensor.diagonal (latent (skyline h (rock v i) l)) X
    have ht i : V i c= ∑ j,M j i • V j c:= by
       rw [show V i= _ from (show V i=∑ j,M j i • V j from g u v i),_root_.sum_apply]; exact Finset.sum_congr rfl (fun _ _=> rfl)
    have hu i: Tensor.diagonal (latent (skyline h (rock v i) l)) (Cast u X)=∑ j,M i j • W j:= donated v i X H u
    change (∑ i, V i c * _)= ∑ i,V i c* W i
    conv_rhs=> arg 2; intro i; arg 1; rw [ht]
    simp_rw [hu, Finset.mul_sum,Finset.sum_mul]; rw [Finset.sum_comm]; exact Finset.sum_congr rfl (fun i _=>Finset.sum_congr rfl fun j hj=>by simp only [smul_eq_mul]; ring)

-- signed groups on roots. map convention composition.
def pumped (s:Signed)(x:Fin r→ YForest G):= ∏ i,rimSign s (x i).2

def alliance {r D}(s:Signed)(F T: ChamberTen G (Vote D) r): Prop:= ∀ x c, T (tickW s 0 ∘ x) c=pumped s x*F x (spinV s D c)
lemma tundra (s:Signed)(i:Edge Cover): ringS s 0 i=Film.up s i:= by
     unfold ringS Film.up Step.used Step.rotate; rw [going_spec]; cases he:s.flip i.2 <;> simp [he,delay,posDir, sub_eq_add_neg,affine]
lemma tickets (s:Signed): Bijective (tickW (G:=G) s 0) :=by
     have he (v:Edge Cover)(i:G.ColorIndex): tickW s 0 (stone v i)=stone (Film.up s v) i:= by rw [tick_stone,tundra]
     have hp {v w}: Film.up s v=Film.up s w → v=w:= by intro h; obtain hv:=s.perm.injective (congr_arg Prod.snd h); cases v; cases w; dsimp only at hv; subst_vars; exact Prod.ext ((goingUp s _).injective (congr_arg Prod.fst h)) rfl
     constructor
     · intro a b; obtain ⟨v,i,rfl⟩:=every_stone a; obtain ⟨w,j,rfl⟩:= every_stone b; intro h; rw [he,he] at h
       rw [hp (v:=v) (w:=w) (by have hv:= congr_arg feather h; simpa [feather_at] using hv), show i=j from congr_arg (fun x:YForest G=> x.2.2) h]
     intro b; obtain ⟨⟨y,i⟩,v,rfl⟩:= every_stone b; obtain ⟨j,rfl⟩:= s.perm.surjective i; obtain ⟨p,rfl⟩:= (goingUp s j).surjective y
     exact ⟨stone (p,j) v, he _ _⟩

private lemma dice (s:Signed)(X:Snap G h)(x:Fin r→ YForest G)(H:Hol G): Tensor.diagonal (latent (skyline h x l)) (Film.turnIn G h s X)=
     pumped s x * Tensor.diagonal (latent (skyline h (tickW s 0 ∘ x) l)) X:=by
   let u:= tickW s 0 ∘ x
   have he (i:YForest G): (fun Z:Snap G h=>flex i (Film.turnIn G h s Z)) =ᶠ[𝓝 0] fun Z=> rimSign s i.2 • flex (tickW s 0 i) Z:=by
       obtain ⟨v,j,rfl⟩:=every_stone i
       filter_upwards [Film.shade H (d:=h) s v] with Z hZ; unfold flex; rw [feather_at,tick_stone,tundra,rim_stone,feather_at]; change (Film.lane (Place.seat v.1) _ _ j)= _; rw [hZ]; rfl
   let L : ℝ→L[ℝ]Snap G h:=(ContinuousLinearMap.id ℝ ℝ).smulRight X
   have hx : Tendsto L (𝓝 0) (𝓝 0):= by rw [←map_zero L]; exact L.continuous.tendsto _
   rw [lost,lost]; change leading l _= pumped s x • leading l (mite u ∘ L)
   rw [← lead_sc]
   · unfold leading; apply congr_arg ((l.factorial:ℝ)⁻¹ • ·); apply Filter.EventuallyEq.iteratedDeriv_eq
     filter_upwards [hx.eventually (eventually_all.mpr fun i=>he (x i))] with t h; rw [show t • Film.turnIn G _ s X = Film.turnIn G _ s (L t) from (map_smul (Film.turnIn ..) t _).symm]; unfold mite pumped; simp_rw [h,smul_eq_mul, Finset.prod_mul_distrib]; rfl
   exact (show ContDiffAt ℝ (↑l) (mite u) (L 0) from by rw [map_zero]; exact (mite_smooth ..).of_le le_top).comp _ L.contDiff.contDiffAt

lemma follows (H:Hol G)(σ:Signed)(F T:ChamberTen G (Vote D) r)(a:alliance σ F T)(c:Volume D)(X:Snap G h)(p:Twig 0 s A F)(q: Twig 0 t C T)(hs:0<s)(ht:0<t) :
     Tensor.diagonal (latent (arret c T h l)) X=Tensor.diagonal (latent (arret (spinV σ D c) F h l)) (Film.turnIn G h σ X):=by
    let b : Equiv.Perm (Fin r→ YForest G):= Equiv.piCongrRight (fun _=> Equiv.ofBijective (tickW (G:=G) σ 0) (tickets (G:=G) σ))
    rw [lat_sum c T _ _ q ht, lat_sum _ _ _ _ p hs,← b.tsum_eq]
    refine tsum_congr fun v=>?_; change T (tickW _ _ ∘ _) _ *_= _
    rw [a v, dice σ X v H]; rw [mul_assoc,mul_left_comm]; rfl

end YM.WilsonCoeffUV.Fountain
