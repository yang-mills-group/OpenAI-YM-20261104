import YM.LocalTaylorR2.Exponent.Auric

/-!
 # The extra Sales lease through full AUTH paths. Enough for all derivatives & support. On physical eligible ticket any volume & period.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Exponent
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {W s μ C : ℝ} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R}
open Channel Gas Ursell Trees Animals Census Itinerary Port Reserves
variable {j k n l p m:ℕ} {g v d A D x y β:ℝ} {χ:Chi}
open Canvas Axial Kiln Work.G05
variable {i:Trans f}{X:Coat T F}{K:ℕ→Atom G p} {b:ℝ} {w:Air f G}{U:Support c}

lemma protege (P:Teller G)(L:Side)(o:Target.Order G W)(p j k:ℕ) (χ:Chi)(D:Patch)(hD:D.Branches P.bind G)(v d:ℝ→ℝ)(hv:Rate G L (-(1/2)) v)(hV:∀ᶠ x in atTop, 0≤ v x)(hd:Rate G L (-(1/2)) d):∃ b, Rate G L 0 b ∧ ∀ᶠ x in atTop, ∀ c f (S:StepData c f)(T:Tube G S)(R:Rep G f)(Q:YM.ConnectedActivityE6.Target G P) μ C (H:Cash W x μ L Q o C T R), S.patch=D → Stamp T → ∀ (K: ℕ→ Atom G k)(a:ℝ) (i:Trans f), (K i.2.2).Invariant → Kept H (atomFoot S.ratio Q.halo (radiusB x) K i) (Kiln.flame H a K i p) → Astonish H (atomFoot S.ratio Q.halo (radiusB x) K i) j (p+j) (v x) (d x) χ (Kiln.bill (b x) 0 a x K i) (seating Q.halo x S K i) (demesne R a o.a K i p-Kiln.flame H a K i p):=by
 obtain ⟨b,hb,hY⟩:= Basecamp.tenant G L P (J G) j hv hV; obtain ⟨B,hB,hN,hX⟩:= Clutch.central G L χ j hd (2*o.a); obtain ⟨r,M,hr,_,hM,hq⟩:= latentRate G P L D hD k p
 let e x:=4*(radiusB x:ℝ)*(v x*royalty G); let a x:= d x + o.cap*Pressure.fiery G x L+2*Fintype.card G.ColorIndex; let g:= royalty G
 let u x:= g*(a x*g)*(1+(e x+1+e x))^j; let s x:= 1+(b x+u x)
 have h₁ : Rate G L 0 e:= by simpa only [zero_add] using! ((Rate.radius_price.mul_left 4).mul ((hv.weaken (b:=0) (by norm_num)).mul_right (royalty G)))
 have h₂:Rate G L 0 u:= by
    have h:Rate G L 0 (fun x=> (1+(e x+1+e x))^j):= by simpa only [zero_mul] using! (((Rate.const 1).add ((h₁.add (Rate.const 1)).add h₁)).pow j)
    have ha:Rate G L 0 a:= ((hd.add (Rate.flame.mul_left _)).weaken (by norm_num)).add (Rate.const (G:=G) _)
    simpa only [add_zero] using ((ha.mul_right g).mul_left g).mul h
 let B' x:=2*(1+B x)^j; have h₃:Rate G L 0 B':=by simpa only [zero_mul] using (((Rate.const 1).add hB).pow j).mul_left 2
 have hZ:Rate G L 0 s:= (Rate.const 1).add ((hb.weaken (by norm_num)).add h₂)
 have hh {g :ℝ→ℝ}(h:Rate G L 0 g):= h.compare (v:=fun x=> |g x|) (Eventually.of_forall fun i=>(abs_abs _).le)
 refine ⟨fun x=> |stamp j p 1 (s x+s x)| *B' x * |M x|, (( (hh (rateStamp _ _ (hZ.add hZ))).mul h₃|>.weaken (b:=0) (by norm_num)).mul (hh hM)).weaken (b:=0) (by norm_num),?_⟩
 filter_upwards [hX,hY] with x hf hh c f S T R Q μ C H hz ht K a' i hv hp
 refine ⟨(marqueeKept H K i D hD hz hv hp).sub (Port.Burst.fat hp), ?_⟩
 intro E _ _ _ F X V z U w u' hY hW hΨ hχ hv hy Y hY₀; subst x; let hP:= H.laws.data
 have ht':0<X.t:= hP.room.fiery; have hd:= hP.funds.length_eq
 let t := seating Q.halo X.x S K i; have he := sit_ge Q.halo X.x S K i; have hvX:= hv.pos; have hv':=hy.price; have hg := royalty_ge G
 have hΛ:0 ≤ a X.x:=by unfold a; rw [← hd]; change 0≤ d X.x+o.cap*X.t+_; have h0:= hP.safety.1; positivity
 have hK : light X K i→ Brush p ((K i.2.2).magnitude*|M X.x|) 1 (latent K S i) 0:=fun hi=> (hq X.x _ _ S T 0 _ _ hz hP.room.accepted (by simpa using hr.le) X.k hi).climb (mul_le_mul_of_nonneg_left (le_abs_self _) (munch ..)) le_rfl
 have hYZ : 1≤ s X.x:= by unfold s; apply le_add_of_nonneg_right (add_nonneg hh.1.le _); unfold u e g; positivity
 apply barley H hW hΨ hy hY₀ (hN _) hYZ he (abs_nonneg _) ht _ _ hK a' -- exact eventual hK; possibly projections
 · let Y := atomFoot S.ratio Q.halo X.B K i; have hp:homeFoot X K i ⊆ Y:= image_subset_image (Corona.halo_mono (by rw [zero_mul]; exact Nat.zero_le _) (Subset.refl _))
   apply (hf _ _ S T F X rfl hχ hd (mul_pos (by have hp:= o.large; positivity) hP.room.fiery) E u' _ _ w V z U hy _ _ hp).climb le_rfl
   apply mul_le_mul_of_nonneg_left _ (hN _); exact (le_add_of_nonneg_right (Nat.cast_nonneg _)).trans (le_add_of_nonneg_left zero_le_one)
 intro he' hy'; let t:= axis S i; have hx : Clean (V w) X.x t (40*radiusB X.x+1) :=by rw [hy.atV]; refine (clean_far X.seeds X.V hΨ hy').shrink ?_; change separation t t+_ ≤ _; rw [separation_self]; have hx:100≤ X.B:= hP.room.sight.1; change _ ≤ 200*(radiusB X.x); unfold Coat.B at hx; omega
 have hh':=ranged H hv hW hΨ hy hY₀ hy' (hh.2 _ _ S T hd hP.room (bed X) (by unfold bed Coat.B; omega) E V w X.χ t hv hx).1
 unfold Coat.t at hh'; rw [hd] at hh'; exact hh'
-- normalize all bill papers from Phase. easiest pTaylor=0 at K=β^-2. removes denominator. exact multiplicative cost
lemma weighs (k:ℕ) {A:ℕ→ Atom G k}{p:Trans f}(b a u:ℝ)(h:0<u) : Kiln.bill b 0 a x A p=Kiln.bill (u ^(-(2:ℝ))) 0 a x A p * (u^2*|b|):=by
  unfold Kiln.bill; rw [abs_of_nonneg (Real.rpow_nonneg h.le _),Real.rpow_neg h.le, Real.rpow_two]; split
  next hp=> field
  next hp=> rw [abs_zero,mul_zero,zero_mul,zero_mul]
end YM.LocalTaylorR2.Exponent
