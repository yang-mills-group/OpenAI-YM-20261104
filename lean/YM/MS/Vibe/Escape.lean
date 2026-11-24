import YM.MS.Vibe.Powers
/-!
# Vanishing across sectors if constant, assuming bare error pure

 No projecting to ℓ=0 before sense. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Emit
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train Dock
open Signal Book Convolve Garment.Wave Garment.Wick
open scoped Topology ContDiff Interval
variable {I:Type}{G:Gauge}{X:Mob G}{V W:Flats G}{f:Coat G}{t r:ℤ}{a h n m k ℓ:ℕ}{i:ℂ}{s y:ℝ}{b:Bool}
-- δ length. tags.
abbrev Calm (h:ℕ)(b:Bool)(F:Flats G)(u:ℤ): Prop:=∀ᶠ i in dotty,∀ m l,(l.length:ℤ)=u → Course (P:=SectorP m) b l→∀ s y,HasDerivAt (fun t=> Parade F h y t i m l) 0 s
def pointLap (b:Bool)(r:ℤ)(V:Mob G)(x:ℂ): Prop:=∀ m (l:Legs (Shore G m)), (l.length:ℤ)=r→ Course b l→∀ s, plow x s V m l= V m l
lemma patient (hp:Calm h b V r) : ∀ᶠ i in dotty,∀ n, pointLap b r (V n i) (vamp i h n):= by
   filter_upwards [dotty_non,hp] with i hi hp n m l hl hx s; apply settle V hi l s _ n; intro y; exact is_const_of_deriv_eq_zero (fun s=> (hp m l hl hx s y).differentiableAt) (fun s=>(hp m l hl hx s y).deriv) s 0
lemma lucid (hV:Calm h b V r)(ht:Host V h): ∀ᶠ i in dotty,∀ ℓ,0<ℓ→ zeroTest b ( V ℓ i) r:= by
   refine facade V (fun x ℓ F=>0<ℓ→ zeroTest b F r) id dotty (fun x ℓ _=>⟨fun n w hx hu=>rfl⟩) (fun ℓ=>?_); by_cases hy:0<ℓ; swap; · exact Eventually.of_forall fun i h=> (hy h).elim
   filter_upwards [ vamp_room h ℓ hy,vamp_up h ℓ,patient hV,(sunny (ht.bill ℓ))] with i hi hx hu hF; intro hz; obtain hp := spotM r hF; let F:= V ℓ i; let x:= vamp i h ℓ; have he: Steady0 b x (spot r F):= by
       intro s m l hC; by_cases he:(l.length:ℤ)=r; · rw [spotted he]; unfold plow; rw [spotted (by unfold sr; simpa using he)]; exact hu ℓ m l he hC s
       simp only [plow, spotsOff he,spotsOff (show ((sr s l).length:ℤ)≠r by unfold sr; simpa using he), mul_zero]
   constructor; intro n l ht h; obtain ht':= decide0 he hp.price hx (fun i hl=> resonance he hp.price (hi i hl)) n l h; rw [spotted ht] at ht'; exact ht'
-- High orbit begets exact bare anomaly zero.F(rank)
variable (hp:Host V h)(ht: Return V f h)(hx: Scorched f b)
variable (he:Calm h b V r)
include he ht
lemma countercheck : ∀ᶠ z in dotty,∀ n (l:Legs (Shore G n)),(l.length:ℤ)=r→ Course b l→ V 0 z n l=f z n l:= by
    filter_upwards [patient he,ht] with z hz hM n l hl hp; let G:= fun t:ℝ=> plow (vamp z h 0) t (V 0 z) n l; refine tendsto_nhds_unique (l:=atBot) (tendsto_const_nhds.congr (f₂:=G) (fun x=> Eq.symm (hz 0 n l hl hp _))) ?_; unfold G; rw [vampV]; exact hM n l
include hx hp
lemma zeroTest_of_calm_return : ∀ z, zeroTest b (f z) r := by
    obtain hv:= lucid he hp; obtain hK:= countercheck ht he; obtain ⟨T,hT⟩:=Live.tends (hp.tall 0 0); obtain ⟨H,h,Y⟩:=hx; intro z; constructor; intro m l hm hl; rw [← Y z m l hl]; refine coolEdge l h (Tendsto.congr' ?_ (hT m l)) z -- EventuallyEq orientation
    filter_upwards [hv,hK] with i hi hK; rw [Y i m l hl,← hK m l hm hl]; let S:=insert 0 V.support; have hx:V.support ⊆ S:= Finset.subset_insert _ _ ; rw [Page S hx,Finset.sum_apply, Finset.sum_apply, Finset.sum_apply, Finset.sum_eq_single 0];
    · simp [hikeP,Pearl.weight,amount]
    · intro j hj hp; simp only [hikeP,Pi.smul_apply,posing]; rw [(hi j (by omega)).passes m l hm hl,smul_zero]
    simp [S]
abbrev Blink (b:Bool)(V:Flats G)(r:ℤ): Prop:=∀ᶠ i in dotty,∀ n, zeroTest b (V n i) r
lemma beyond : Blink b V r:= by
    filter_upwards [lucid he hp, countercheck ht he] with i hi hz n; by_cases h: n=0; · subst n; exact ⟨ fun t w hw hu=> (hz t w hw hu).trans ((zeroTest_of_calm_return hp ht hx he i).passes t w hw hu) ⟩
    exact hi n (Nat.pos_of_ne_zero h)
end YM.MS.Emit
