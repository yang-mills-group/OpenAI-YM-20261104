import YM.Juniper.Bright.NewHire
/-!
 # Making Flux.FlareW available on any tuned stalk

 Important quantitative strengthening of Census.Mettle takeoff & Blaze.Flux.launch;
      not existential Ξ. Needed for non-routine post-power budget on selected heads
 (else Desirable on DIFFERENT Ξ). Divergence so not inferable simply from those with Ξ
 already picked; restore actual occupancy income for ANY later application of extra
 weights. Proof payment using `accent`, Yah.scale and tilt after the slope choice: body of that range ported from
      AnalyticalNext.CONNECTED_ACTIVITY_JETS_E6/March.launch,
      reversing the quantifiers enables reuse of this on all later
      strengthened hierarchies.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Bright
open ConnectedActivityE6 ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Flux
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G: Gauge}

lemma slope (P : Teller G) (Q : ConnectedActivityE6.Target G P) (L:Side) (D:Patch) (hD:D.Branches P.bind G)
     (i:ℕ) (χ:Chi) {W :ℝ} (o : Target.Order G W) (A f : ℝ) (hA: Canary G A f) {V :ℝ→ℝ}
     (hV:Rate G L (-(1/2)) V) (hv:∀ᶠ x in atTop,0≤V x) : ∃ q:ℝ→ℝ, Rate G L (-(1/2)) q ∧
     ∀ (r :ℝ→ℝ), Rate G L 0 r → ∃ (l:ℕ) (p :ℝ→ℝ), Rate G L 0 p ∧ ∀ᶠ x in atTop, ∀ (c f':Side) (S : StepData c f') (T: Tube G S), S.patch=D →
        ∀ (C C' μ:ℝ) (R:Rep G f') (H:Cash W x μ L Q o C' T R) (Ξ: Utopia H i (V x) (q x) (r x) C χ), 8*o.a* Pressure.fiery G x L ≤ A/2 ∧ FlareW H Ξ A (|p x|) l := by
  obtain ⟨B,Z,hB,hZ,hX⟩:= Silica.clips hA P L i χ hV
  have hb:= hB.compare (v:=fun x=>|B x|) (Eventually.of_forall fun x=>(abs_abs _).le)
  refine ⟨_,hb,fun r hr=>?_⟩
  obtain ⟨k,U,hU,hΓ⟩:= Flux.rump P L D hD o.K o.γ W o.a χ i hV hB hv hZ o.indexPay o.f A
  let s:= payE o.eta o.gap o.ample (tubularPrice G L)
  obtain ⟨F,K,hF,hΨ⟩:= walksW G L s (k*i*2)
  let e x:= 1+|F x|; let v x:=(1+|U x|+2*r x)^i; let p x:=e x*v x
  have hh {V:ℝ→ℝ} (h:Rate G L 0 V):= h.compare (v:=fun x=> |V x|) (Eventually.of_forall fun z=> (abs_abs _).le)
  have he:= Rate.const (G:=G) (L:=L) 1
  refine ⟨K+i,p,by unfold p; simpa only [zero_mul,zero_add] using! ((he.add (hh hF)).mul (((he.add
    (hh hU)).add (hr.mul_left 2)).pow i)),?_⟩ -- subsequent proof body adapted unchanged other than hH names from Mettle. Pointwise not ex and no Stamp.
  filter_upwards [hΓ,hX, ((Rate.flame (G:=G) (L:=L)).mul_left (8*o.a)).below (by norm_num) _ (half_pos hA.warm)] with
    x h hx hp c f S T hS C C' μ R H Ξ
  have hθ:=H.laws.data; have hh:=hθ.funds; have hy := H.laws.intake
  have hp := (le_abs_self _).trans hp
  refine ⟨hp,⟨?_⟩⟩
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

open March Next.Foundations
set_option linter.unusedVariables false in
lemma assemble (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P) : ∃ n:ℕ, ∀ (L:Side), n≤L.val →
    ∀ (D:Patch), D.Branches P.bind G → ∀ (k i:ℕ) (χ:Chi) (W:ℝ), 0<W → ∀ (μ:ℝ), 0<μ → ∀ (o:Target.Order G W),
    ∃ (A a C : ℝ) (d v t r B q : ℝ→ℝ) (l:ℕ), Rate G L 0 B ∧ ∀ᶠ x in atTop,
      ∀ (c f:Side) (S:StepData c f) (T:Tube G S), S.patch=D→Stamp T→∀ (R:RG.Rep G f) (C':ℝ) (H:Cash W x μ L Q o C' T R),
        ∃ N: Captain H i C (d x) (v x) (t x) A a (r x) (B x) (q x) l χ, Desirable k N.conduit := by
  obtain ⟨m,hM⟩:= shop P Q; refine ⟨m, fun L hL D hD k i χ W hW μ hm o=>?_⟩
  obtain ⟨A,a,hA⟩:= Eider.weave G; obtain ⟨Z,hZ,hq⟩:= March.oar G i
  let t x := 2*Pressure.fiery G x L; have he : Rate G L (-(1/2)) t:= Rate.flame.mul_left 2
  let v x := ((i:ℝ)+1)*Z*t x; have hh : Rate G L (-(1/2)) v:= he.mul_left _
  have hp : ∀ᶠ x : ℝ in atTop, 0<t x := ((Work.E09.betaF_growth G L).eventually_gt_atTop 0).mono fun x h=> mul_pos (by norm_num) (Work.E09.temp_pos h)
  have h₁:∀ᶠ x in atTop,0 ≤ v x:= hp.mono (fun x hh=> by unfold v; positivity)
  obtain ⟨B,hB,hT⟩:= Bright.slope P Q L D hD i χ o A a hA hh h₁
  obtain ⟨C,r,hC,hr,F⟩:= hM L hL D hD k i χ W hW μ hm o v B hh h₁ hB
  obtain ⟨l,Q₁,hQ,h⟩:= hT r hr
  let B' x:= |Q₁ x|; have hb' : Rate G L 0 B':= hQ.compare (Eventually.of_forall fun x=> by simp [B'])
  refine ⟨A,a,C,B,v,t,r,B',fun x=> Z*t x,l,hb',?_⟩
  filter_upwards [hp,F,h, Glass.portal P D L hD i χ hh h₁ o.K o.γ W o.indexPay o.f] with x hx hD' hΦ hg c f S T hS hT R U H
  obtain ⟨Ξ,hΞ⟩:= hD' c f S T hS hT R _ H; obtain ⟨hy,hv⟩:= hΦ c f S T hS C _ _ R H Ξ; have h:= H.laws.data
  refine ⟨⟨Ξ,⟨hA, hy,hv,?_⟩,mul_nonneg hZ.le hx.le,hx.le,(by have he:= h.room.temperatures; rw [h.funds.length_eq] at he; exact he),
    (by unfold v; positivity),abs_nonneg _, ⟨fun c=> hq c _ hx.le⟩,(by unfold v; nlinarith [mul_nonneg hZ.le hx.le])⟩,hΞ⟩
  intro F X hX he hu hm
  exact hg _ _ S T hS h.funds h.access F X hu he hX (h.localP F X hX hu hm)
end YM.Juniper.Bright
