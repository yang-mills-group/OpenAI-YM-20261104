import YM.RG01Estimate.E6Supply

/-! The `takeoff` argument of E6 lifts ANY `Utopia` with these prices to an
order-j derivative budget. Use the corresponding `Canary`, glass and Brush
comparisons, so that we can use the new weighted radii. Expose that lemma
with the universal quantifier for a future pricing (another kind of vertex).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Passport
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03 ConnectedActivityE6
open Shell Channel Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {W μ : ℝ}

-- shift A BEFORE purchasing a Utopia; r includes all charges. Adapt `launch`
theorem ballast (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P) (L:Side)
    (D:Patch) (hD:D.Branches P.bind G) (i:ℕ) (χ:Chi) (W μ:ℝ) (o:Target.Order G W)
    (A f : ℝ) (hA: Canary G A f) (V : ℝ→ℝ) (hV: Rate G L (-(1/2)) V) (hv: ∀ᶠ x in atTop,0≤V x) :
    ∃ (q:ℝ→ℝ), Rate G L (-(1/2)) q ∧
    ∀ (C:ℝ) (r:ℝ→ℝ), Rate G L 0 r → ∃ (p:ℝ→ℝ) (l:ℕ), Rate G L 0 p ∧
    ∀ᶠ x in atTop, ∀ (c f':Side) (S : StepData c f') (T: Tube G S), S.patch=D →
        ∀ (R:Rep G f') (C':ℝ) (H:Cash W x μ L Q o C' T R),
        ∀ Ξ : Utopia H i (V x) (q x) (r x) C χ, Oboe H i (V x) (|p x|) l A f Ξ := by
  obtain ⟨B,Z,hB,hZ,hX⟩:= Silica.clips hA P L i χ hV
  have hb:= hB.compare (v:=fun x=>|B x|) (Eventually.of_forall fun x=>(abs_abs _).le)
  refine ⟨fun x=>|B x|,hb,fun C r hr=>?_⟩
  obtain ⟨k,U,hU,hΓ⟩:= rump P L D hD o.K o.γ W o.a χ i hV hB hv hZ o.indexPay o.f A
  let s:= payE o.eta o.gap o.ample (tubularPrice G L)
  obtain ⟨F,K,hF,hΨ⟩:= walksW G L s (k*i*2)
  let e x:= 1+|F x|; let v x:=(1+|U x|+2*r x)^i; let p x:=e x*v x
  have hh {V:ℝ→ℝ} (h:Rate G L 0 V):= h.compare (v:=fun x=> |V x|) (Eventually.of_forall fun z=> (abs_abs _).le)
  have he:= Rate.const (G:=G) (L:=L) 1
  refine ⟨p,K+i,by unfold p; simpa only [zero_mul,zero_add] using! ((he.add (hh hF)).mul (((he.add
    (hh hU)).add (hr.mul_left 2)).pow i)),?_⟩
  filter_upwards [Glass.portal P D L hD i χ hV hv o.K o.γ W o.indexPay o.f,hΓ,hX, ((Rate.flame (G:=G) (L:=L)).mul_left (8*o.a)).below (by norm_num) _ (half_pos hA.warm)] with
    x hyP h hx hp c f S T hS R C' H Ξ
  have hθ:=H.laws.data; have hh:=hθ.funds; have hy := H.laws.intake
  have hp := (le_abs_self _).trans hp
  refine ⟨hA,hp,⟨?_⟩,fun F X hX hF hv hm=> hyP c f S T hS hh hθ.access F X hv hF hX (hθ.localP F X hX hv hm)⟩
  intro E _ _ _ F' X Y y p' hζ hM ht hK hr hu he hf hy' m
  let I:= edgesM S (H.unionP p') (radiusB x); let J:= X.catastrophe (o.ξ/2) R.beta (blaze p')
  let f(z : Air f G):= facescale I z^(k*i); let S':=1+H.shapeW p'; let X' z:= J.indicator f z
  let a:=(∏ i∈p', Ξ.tag i)*v x*S'^i
  have hR:= hθ.localP F' X ht hK hM
  have hx':(1:ℝ)≤S':= le_add_of_nonneg_right (H.positive_volume p')
  have ha:a≥0 := mul_nonneg (mul_nonneg (prod_nonneg fun _ _=> Ξ.tagged _) (pow_nonneg (by have hq:= Ξ.active; positivity) _)) (pow_nonneg (zero_le_one.trans hx') _)
  have hQ:MeasurableSet J := Poll.sounded ..
  have hm:=globes I hR.sails (k*i*2)
  have hV := (globes I hR.sails (k*i)).1
  have hTax : Integrable (X': Air _ G→ℝ) X.dice := hV.indicator hQ
  have hE: ∫ x,X' x ∂X.dice ≤ (e x*S'^K)*Ξ.rad^(blaze p').card := by
    let i':ℝ:= I.card; let V:ℝ:= (lensS I G).card
    have hI: i'≤ S'*ballCost (radiusB x)* (Itinerary.density L:ℝ) := by
      have h:= crewsC H p'; rw [hh.length_eq] at h; apply h.trans; unfold S'; gcongr; linarith
    have he: 1≤e x:= le_add_of_nonneg_right (abs_nonneg _)
    have hV' : V=i'*Fintype.card G.ColorIndex := by simp [V,i',lensS]
    have hp := hm.2.trans (hΨ x i' V S' hx' (Nat.cast_nonneg _) hI hV')
    have hc : ∫ x,f x^2 ∂X.dice ≤ (e x*S'^K)^2 := by
      unfold f; simp_rw [← pow_mul]; apply hp.trans
      exact (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (pow_nonneg (zero_le_one.trans hx') _)).trans
        (le_self_pow₀ (one_le_mul_of_one_le_of_one_le he (one_le_pow₀ hx')) (by omega))
    refine divideC _ f hV _ (by positivity) _ hQ (by rw [← pow_mul, Nat.mul_comm]; rw [pow_mul]; exact Ξ.ship _ X ht hK hζ hM (blaze p')) (pow_nonneg Ξ.awake _) ?_ hc
    unfold f; simp_rw [← pow_mul]; exact hm.1
  have hhP: Integrable (fun z:F'.Slice G × Air _ G=> a*X' z.snd) m := (hTax.const_mul a).comp_snd _
  refine ⟨fun z=> a*X' z.2,hhP,?_,?_⟩
  · rw [integral_prod _ hhP]
    dsimp only; simp_rw [integral_const_mul]; rw [ integral_const]; simp only [probReal_univ,one_smul]; rw [Utopia.meant,if_pos ((H.attends _).2 he),Ξ.remixes]
    apply (mul_le_mul_of_nonneg_left hE ha).trans
    unfold a S' p; rw [abs_of_nonneg (by unfold e v; have h:=Ξ.active; positivity : 0 ≤ e x*v x)]; apply le_of_eq; ring
  intro ⟨v',z⟩
  let X:= X.wrapY v'; have hZ:= hθ.localP F' X ht hK hM
  obtain ⟨hw,hD⟩:= hx _ _ S T F' X ht hh hζ R.beta hy.positive z E Y y hy' hf
  have hp := hD o.a (mul_pos o.large hZ.sails.room.fiery) (by unfold Coat.t; rw [show X.x=_ from ht,hh.length_eq]; exact hp)
  have hq := h c _ S T hh hS hθ.access E y Y F' X z R ht hK hζ hZ hy hf hp hw I
  apply (accent Ξ X hf _ hu hM hr ht hζ hK hp hq (abs_nonneg _)).climb _ le_rfl
  by_cases h:z∈J
  · change J.indicator _ z≤ a * X' z; unfold a X'; rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
  change J.indicator _ z≤a * X' z; unfold X'; rw [Set.indicator_of_notMem h,Set.indicator_of_notMem h,mul_zero]

open March Expense Reprice
lemma passport (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P) :
    ∃ n : ℕ, ∀ L : Side, n ≤ L.val → ∀ D : Patch, D.Branches P.bind G →
    ∀ (u v w : ℝ), u+v<Q.rate → 0≤w → ∀ (X E K : ℝ→ℝ), Rate G L u X → Rate G L v E → Rate G L w K →
      (∀ᶠ x in atTop,1 ≤ E x) → (∀ᶠ x in atTop,1 ≤ K x) →
    ∀ (χ : Chi) (i : ℕ) (W μ : ℝ), 0 < W → 0 < μ → ∀ o:Target.Order G W,
    ∃ (A a C : ℝ) (d v t r B q : ℝ→ℝ) (k:ℕ), Rate G L 0 B ∧ ∀ᶠ x in atTop,
      ∀ (c f:Side) (S:StepData c f) (T:Tube G S), S.patch=D→Stamp T→∀ (R:Rep G f) (C':ℝ) (H:Cash W x μ L Q o C' T R)
        (J : Set ℕ), Inherit.Debits R J (X x) →
        ∃ N: Captain H i C (d x) (v x) (t x) A a (r x) (B x) (q x) k χ, Supports (weigh c f J (E x) (K x)) N.conduit := by
  obtain ⟨n,h⟩:= Reprice.supplied P Q; refine ⟨n, fun L hL D hD u v w hp hw X E K hX hE hK h₁ h₂ χ i W μ hW hm o=>?_⟩
  obtain ⟨A,a,hA⟩:= Eider.weave G; obtain ⟨Z,hZ,hq⟩:= March.oar G i
  let t x := 2*Pressure.fiery G x L
  have he : Rate G L (-(1/2)) t:= Rate.flame.mul_left 2
  let v x := ((i:ℝ)+1)*Z*t x
  have hh : Rate G L (-(1/2)) v:= he.mul_left _
  have hP : ∀ᶠ x : ℝ in atTop, 0<t x := ((YM.Work.E09.betaF_growth G L).eventually_gt_atTop 0).mono fun x h=> mul_pos (by norm_num) (YM.Work.E09.temp_pos h)
  have hy : ∀ᶠ x in atTop, 0 ≤ v x := hP.mono fun x hh=> by unfold v; positivity
  obtain ⟨p,hp',hP'⟩:= ballast P Q L D hD i χ W μ o A a hA v hh hy
  obtain ⟨C,r,hr,Ht⟩:= h L hL D hD _ _ _ hp hw X E K v p hX hE hK h₁ h₂ hh hy hp' χ i W μ hW hm o
  obtain ⟨B,k,hB,hF⟩:= hP' C r hr
  let B' x:= |B x|; have hb' : Rate G L 0 B':= hB.compare (Eventually.of_forall fun x=> by simp [B'])
  refine ⟨A,a,C,p,v,t,r,B',fun x=> Z*t x,k,hb',?_⟩
  filter_upwards [hP,Ht,hF] with x hx hD' hF c f S T hS hT R B' H J he'
  obtain ⟨Ξ,hΞ⟩:=hD' c f S T hS hT R _ H J he'; have hv := H.laws.data
  exact ⟨⟨Ξ,hF _ _ S T hS _ _ H Ξ,mul_nonneg hZ.le hx.le,hx.le,(by have he:= hv.room.temperatures; rw [hv.funds.length_eq] at he; exact he),
    (by unfold v; positivity),abs_nonneg _, ⟨fun c=> hq c _ hx.le⟩,(by unfold v; nlinarith [mul_nonneg hZ.le hx.le])⟩,hΞ⟩

end YM.RG01Estimate.Passport
