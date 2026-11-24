import YM.LocalLTE.Marked.Post

/-! Preserve three numerical witnesses of the original HostQ and Height
selection on the same Cash. The witnessing guard is the absolute Silica
bound. Its measured multiplicity is at least one, and the native degree
covers the requested field order. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ManuscriptQLocalHeightPaidRows

structure Ready (j:ℕ) (guard mass:ℝ) (order:ℕ) : Prop where
  guard_nonnegative : 0 ≤ guard
  mass_one : 1 ≤ mass
  degree : j ≤ order

end YM.Integration.ManuscriptQLocalHeightPaidRows

namespace YM.PhysicalNext.Repeat.Daisy
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond Mixed Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Itinerary Animals
variable {G : Gauge}

lemma timingFundedRows (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P) : ∃ n:ℕ, ∀ (L:Side), n≤L.val →
    ∀ (D:Patch), D.Branches P.bind G → ∀ (i n₀:ℕ) (χ:Chi) (c₁ W:ℝ), 0<W → ∀ (μ:ℝ), 0<μ → ∀ (o:Target.Order G W)
      (A f : ℝ), Canary G A f → ∀ (V : ℝ→ℝ), Rate G L (-(1/2)) V → (∀ᶠ x in atTop,0≤V x) →
    ∃ (C : ℝ) (q r p : ℝ→ℝ) (l:ℕ), Rate G L (-(1/2)) q ∧ Rate G L 0 p ∧ ∀ᶠ x in atTop, ∀ (c f:Side) (S : StepData c f) (T: Tube G S), S.patch=D → Stamp T →
      ∀ (R:Rep G f) (C':ℝ) (H:Cash W x μ L Q o C' T R),∀ (W':ℕ→ℝ), Raw.Pumps R W' (c₁*incomingE G L x) →8*o.a* Pressure.fiery G x L ≤ A/2 ∧
      ∃ Ξ : Utopia H i (V x) (q x) (r x) C χ, YM.Integration.ManuscriptQLocalHeightPaidRows.Ready i (q x) (|p x|) l ∧
        HeavyT W' n₀ Ξ ∧ HostQ H Ξ A (|p x|) l := by
  obtain ⟨n,hN⟩:= Utopia.hornedT P Q
  refine ⟨n,fun L hL D hD i n₀ χ c₁ W hW μ hm o A f hA V hV hv=>?_⟩
  obtain ⟨B,Z,hB,hZ,hX⟩:= Silica.clips hA P L i χ hV
  have hb:= hB.compare (v:=fun x=>|B x|) (Eventually.of_forall fun x=>(abs_abs _).le)
  obtain ⟨C,r,hC,hr,hχ⟩:= hN L hL D hD i n₀ χ c₁ W hW μ hm o V (fun x=>|B x|) hV hv hb
  obtain ⟨k,U,hU,hΓ⟩:= rump P L D hD o.K o.γ W o.a χ i hV hB hv hZ o.indexPay o.f A
  let s:= payE o.eta o.gap o.ample (tubularPrice G L)
  obtain ⟨F,K,hF,hΨ⟩:= walksW G L s (k*i*2)
  obtain ⟨J',hJ',hP',hX'⟩:= Clutch.central G L χ i hb (2*o.a)
  let e x:= 1+|F x|; let v x:=(1+|U x|+2*(r x+J' x))^i; let p x:=e x*v x
  have hh {V:ℝ→ℝ} (h:Rate G L 0 V):= h.compare (v:=fun x=> |V x|) (Eventually.of_forall fun z=> (abs_abs _).le)
  have he:= Rate.const (G:=G) (L:=L) 1
  refine ⟨C,(fun x=> |B x|),r,p,K+i,hb,by unfold p; simpa only [zero_mul,zero_add] using! ((he.add (hh hF)).mul (((he.add
    (hh hU)).add ((hr.add hJ').mul_left 2)).pow i)),?_⟩
  filter_upwards [hχ,hΓ,hX,hX', ((Rate.flame (G:=G) (L:=L)).mul_left (8*o.a)).below (by norm_num) _ (half_pos hA.warm)] with
    x Hx h hx hW hp c f S T hS hT R C' H W' hRv
  obtain ⟨Ξ,hΞ⟩:= Hx _ _ S T hS hT R C' H W' hRv
  have hθ:=H.laws.data; have hh:=hθ.funds; have hy := H.laws.intake
  have hp := (le_abs_self _).trans hp
  have hbase:1≤1+|U x|+2*(r x+J' x):=by
    have h₁:=Ξ.active
    have h₂:=hP' x
    linarith [abs_nonneg (U x)]
  have hprice:1≤|p x|:=by
    have hfirst:1≤e x:=by dsimp [e]; linarith [abs_nonneg (F x)]
    exact (one_le_mul_of_one_le_of_one_le hfirst (one_le_pow₀ hbase)).trans (le_abs_self (p x))
  refine ⟨hp,Ξ,⟨abs_nonneg _,hprice,by omega⟩,hΞ,⟨⟨?_⟩,?_⟩⟩
  · intro E _ _ _ F' X Y y p' hζ hη ht hK hr hu he hf hy' m
    let I:= edgesM S (H.unionP p') (radiusB x); let J:= X.catastrophe (o.ξ/2) R.beta (blaze p')
    let f(z : Air f G):= facescale I z^(k*i); let S':=1+H.shapeW p'; let X' z:= J.indicator f z
    let a:=(∏ i∈p', Ξ.tag i)*v x*S'^i
    have hR:= hθ.localP F' X ht hK hη
    have hx':(1:ℝ)≤S':= le_add_of_nonneg_right (H.positive_volume p')
    have ha:a≥0 := mul_nonneg (mul_nonneg (prod_nonneg fun _ _=> Ξ.tagged _) (pow_nonneg (by have hq:= Ξ.active; have h:= hP' x; positivity) _)) (pow_nonneg (zero_le_one.trans hx') _)
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
      refine divideC _ f hV _ (by positivity) _ hQ (by rw [← pow_mul, Nat.mul_comm]; rw [pow_mul]; exact Ξ.ship _ X ht hK hζ hη (blaze p')) (pow_nonneg Ξ.awake _) ?_ hc
      unfold f; simp_rw [← pow_mul]; exact hm.1
    have hhP: Integrable (fun z:F'.Slice G × Air _ G=> a*X' z.snd) m := (hTax.const_mul a).comp_snd _
    refine ⟨fun z=> a*X' z.2,hhP,?_,?_⟩
    · rw [integral_prod _ hhP]
      dsimp only; simp_rw [integral_const_mul]; rw [ integral_const]; simp only [probReal_univ,one_smul]; rw [Utopia.meant,if_pos ((H.attends _).2 he),Ξ.remixes]
      apply (mul_le_mul_of_nonneg_left hE ha).trans
      unfold a S' p; rw [abs_of_nonneg (by unfold e v; have h:=Ξ.active; have hp:=hP' x; positivity : 0 ≤ e x*v x)]; apply le_of_eq; ring
    intro ⟨v',z⟩
    let X:= X.wrapY v'; have hZ:= hθ.localP F' X ht hK hη
    obtain ⟨hw,hD⟩:= hx _ _ S T F' X ht hh hζ R.beta hy.positive z E Y y hy' hf
    have hp := hD o.a (mul_pos o.large hZ.sails.room.fiery) (by unfold Coat.t; rw [show X.x=_ from ht,hh.length_eq]; exact hp)
    have hq := h c _ S T hh hS hθ.access E y Y F' X z R ht hK hζ hZ hy hf hp hw I
    apply (accent Ξ X hf _ hu hη hr ht hζ hK hp hq (abs_nonneg _)).climb _ le_rfl
    by_cases h:z∈J
    · change J.indicator _ z≤a * X' z; unfold a X'
      rw [Set.indicator_of_mem h,Set.indicator_of_mem h]
      have hq : (∏ i∈p', Ξ.tag i)*(1+|U x|+2*r x)^i≤(∏ i∈ p', Ξ.tag i)*v x:=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by have hv:=Ξ.active; positivity) (by have he':= hP' x; linarith) _ ) (prod_nonneg fun _ _=>Ξ.tagged _)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hq (pow_nonneg (zero_le_one.trans hx') _)) (pow_nonneg (zero_le_one.trans (Flux.expenses ..).1) _)
    change J.indicator _ z≤a * X' z; unfold X'; rw [Set.indicator_of_notMem h,Set.indicator_of_notMem h,mul_zero]
  intro M E _ _ _ F' X Y y p' hζ hη ht hK hr hu he htM hf hy' m
  let I:= edgesM S (H.unionP p') (radiusB x); let J:= X.catastrophe (o.ξ/2) R.beta (blaze p')
  let f(z : Air f G):= facescale I z^(k*i); let S':=1+H.shapeW p'; let X' z:= J.indicator f z
  let Y' := p' \ M.signs S
  let a:=(M.weight*(∏ i∈Y', Ξ.tag i))*v x*S'^i
  have hR:= hθ.localP F' X ht hK hη
  have hx':(1:ℝ)≤S':= le_add_of_nonneg_right (H.positive_volume p')
  have ha:a≥0 := mul_nonneg (mul_nonneg (mul_nonneg M.profit (prod_nonneg fun _ _=> Ξ.tagged _)) (pow_nonneg (by have hq:= Ξ.active; have h:= hP' x; positivity) _)) (pow_nonneg (zero_le_one.trans hx') _)
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
    refine divideC _ f hV _ (by positivity) _ hQ (by rw [← pow_mul, Nat.mul_comm]; rw [pow_mul]; exact Ξ.ship _ X ht hK hζ hη (blaze p')) (pow_nonneg Ξ.awake _) ?_ hc
    unfold f; simp_rw [← pow_mul]; exact hm.1
  have hhP: Integrable (fun z:F'.Slice G × Air _ G=> a*X' z.snd) m := (hTax.const_mul a).comp_snd _
  refine ⟨fun z=> a*X' z.2,hhP,?_,?_⟩
  · rw [integral_prod _ hhP]
    dsimp only; simp_rw [integral_const_mul]; rw [ integral_const]; simp only [probReal_univ,one_smul]; 
    apply (mul_le_mul_of_nonneg_left hE ha).trans
    unfold a S' p; rw [abs_of_nonneg (by unfold e v; have h:=Ξ.active; have hq:=hP' x; positivity : 0 ≤ e x*v x)]; apply le_of_eq
    unfold Y'; ring
  intro ⟨v',z⟩
  let X:= X.wrapY v'; have hZ:= hθ.localP F' X ht hK hη
  obtain ⟨hw,hD⟩:= hx _ _ S T F' X ht hh hζ R.beta hy.positive z E Y y hy' hf
  have hp := hD o.a (mul_pos o.large hZ.sails.room.fiery) (by unfold Coat.t; rw [show X.x=_ from ht,hh.length_eq]; exact hp)
  have hq := h c _ S T hh hS hθ.access E y Y F' X z R ht hK hζ hZ hy hf hp hw I
  have hArc (M:Leaf R) : Brush i M.weight (J' x*spanW T R X.B Q.halo (M.turn.badge S)) (fun x=> M.fond (vary X (Y x)) o.a (steer X A (worldZ X R.beta z) (Y x)) (X.input (worldZ X R.beta z))) y:=by
    have hA': areas R T 0 X.B (M.turn.badge S) ⊆ H.supportP (M.turn.badge S):=by
      change _⊆ areas R T Q.halo (radiusB x) _
      simp_rw [M.turn.badge_area]; exact Corona.halo_mono (by simp) (Subset.refl _)
    have he' :0<o.a*X.t:= hp.pulse
    have hM:= hW c _ S T F' X ht hζ hh.length_eq (show 0<(2*o.a)*X.t from by rw [mul_assoc]; positivity) E z o.a R.beta y Y _ _ hp _ _ hA'
    have hR' : Brush i M.weight (J' x*spanW T R X.B Q.halo (M.turn.badge S)) (fun x=> M.fond (vary X (Y x)) o.a (steer X A (worldZ X R.beta z) (Y x)) (X.input (worldZ X R.beta z))) y:= by
      have hh := (Brush.certified (d:=0) (x:=y) (k:=i) (le_refl 0) (M.ingredient (X.input (worldZ X R.beta z)))|>.climb (M.earn _) (le_refl _)).paints hM
      rw [mul_one,zero_add] at hh; apply hh.climb le_rfl
      apply mul_le_mul_of_nonneg_left _ (hP' _); rw [← sparkPath]
      change (coverNumber X.B (footprints T R _ (radiusB x) _):ℝ) ≤ 1+(_ + _)
      rw [← show X.B=radiusB x from congr_arg radiusB ht]
      apply le_trans _ (le_add_of_nonneg_left zero_le_one); exact le_add_of_nonneg_right (Nat.cast_nonneg _)
    exact hR'
  apply (scoreT (z':=z) M X H Ξ hu htM ht hK hζ (show X.manifest from hη) hr hf hp (hP' _) (fun M _=>hArc M) hq (abs_nonneg _)).climb _ le_rfl
  by_cases h:z∈J
  · change J.indicator _ z≤ a * X' z; unfold a X'; rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
  change J.indicator _ z≤a * X' z; unfold X'; rw [Set.indicator_of_notMem h,Set.indicator_of_notMem h,mul_zero]

end YM.PhysicalNext.Repeat.Daisy

namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {j n l k : ℕ} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {R : Rep G f}
variable {X : Coat T F} {I : Finset (Tubular f G)} {η r q Y W A B A' a β b p v d t γ C s C' μ g : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {Ñ : ChartRatio G}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {V : E → Config G c} {x : E}
variable {z : Air f G} {H : Cash W s μ L Q o C T R}


namespace Oboe
lemma invoiceFundedRows (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P) : ∃ n:ℕ, ∀ (L:Side), n≤L.val →
    ∀ (D:Patch), D.Branches P.bind G → ∀ (i n₀:ℕ) (χ:Chi) (c₁ W:ℝ), 0<W → ∀ (μ:ℝ), 0<μ → ∀ (o:Target.Order G W)
      (A f : ℝ), Canary G A f → ∀ (V : ℝ→ℝ), Rate G L (-(1/2)) V → (∀ᶠ x in atTop,0≤V x) →
    ∃ (C : ℝ) (q r p : ℝ→ℝ) (l:ℕ), Rate G L 0 p ∧ ∀ᶠ x in atTop, ∀ (c f':Side) (S : StepData c f') (T: Tube G S), S.patch=D → Stamp T →
      ∀ (R:Rep G f') (C':ℝ) (H:Cash W x μ L Q o C' T R), ∀ (W':ℕ→ℝ), Raw.Pumps R W' (c₁*incomingE G L x) → ∃ Ξ : Utopia H i (V x) (q x) (r x) C χ, YM.Integration.ManuscriptQLocalHeightPaidRows.Ready i (q x) (|p x|) l ∧ HeavyT W' n₀ Ξ ∧ PhysicalNext.Repeat.Daisy.HostQ H Ξ A (|p x|) l ∧ Oboe H i (V x) (|p x|) l A f Ξ := by
  obtain ⟨n,hN⟩:= YM.PhysicalNext.Repeat.Daisy.timingFundedRows P Q
  refine ⟨n,fun L hL D hD i n₀ χ c₁ W hW μ hm o A f hA V hV hv=>?_⟩
  obtain ⟨C,q,r,p,l,-,hp,hX⟩:= hN L hL D hD i n₀ χ c₁ W hW μ hm o A f hA V hV hv
  have hG:= Glass.portal P D L hD i χ hV hv o.K o.γ W o.indexPay o.f
  refine ⟨C,q,r,p,l,hp,?_⟩
  filter_upwards [hX,hG] with x hx hy c f' S T hS hT R C' H W' hRv
  obtain ⟨hz,Ξ,grade,hΞ,hq⟩:= hx c f' S T hS hT R _ H W' hRv
  have hg:= H.laws.data
  exact ⟨Ξ,grade,hΞ,hq,hA,hz,hq.unmarked,fun F X hX hF hv hm=> hy c f' S T hS hg.funds hg.access F X hv hF hX (hg.localP F X hX hv hm)⟩
end Oboe
end YM.ConnectedActivityE6.Blaze
namespace YM.ConnectedActivityE6.Blaze.March
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {I : Finset (Tubular f G)} {η r q a Y W d C' A b s μ C v B: ℝ} {Ñ : ChartRatio G}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R} {Ξ : Utopia H j v d r C' χ}
open Next.Foundations

lemma adjudicateFundedRows (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P) : ∃ n:ℕ, ∀ (L:Side), n≤L.val →
    ∀ (D:Patch), D.Branches P.bind G → ∀ (i n₀:ℕ) (χ:Chi) (c₁ W:ℝ), 0<W → ∀ (μ:ℝ), 0<μ → ∀ (o:Target.Order G W),
    ∃ (A a C : ℝ) (d v t r B q : ℝ→ℝ) (k:ℕ), Rate G L (1/2) (fun x=> (v x)⁻¹) ∧ Rate G L 0 B ∧
      (∀ m z:ℕ, Rate G L Q.rate (fun x=>shiftG x^(m*i)* B x * Q.overture L μ x (k+m*i+z))) ∧ ∀ᶠ x in atTop,
      ∀ (c f:Side) (S:StepData c f) (T:Tube G S), S.patch=D→Stamp T→∀ (R:Rep G f) (C':ℝ) (H:Cash W x μ L Q o C' T R), ∀ (W':ℕ→ℝ), Raw.Pumps R W' (c₁*incomingE G L x) →
        ∃ N: Captain H i C (d x) (v x) (t x) A a (r x) (B x) (q x) k χ, YM.Integration.ManuscriptQLocalHeightPaidRows.Ready i (d x) (B x) k ∧ HeavyT W' n₀ N.conduit∧ PhysicalNext.Repeat.Daisy.HostQ H N.conduit A (B x) k := by
  obtain ⟨n,h⟩:= Oboe.invoiceFundedRows P Q; refine ⟨n, fun L hL D hD i n₀ χ c₁ W hW μ hm o=>?_⟩
  obtain ⟨A,a,hA⟩:= Eider.weave G; obtain ⟨Z,hZ,hq⟩:= March.oar G i
  let t x := 2*Pressure.fiery G x L
  have he : Rate G L (-(1/2)) t:= Rate.flame.mul_left 2
  let v x := ((i:ℝ)+1)*Z*t x
  have hh : Rate G L (-(1/2)) v:= he.mul_left _
  have hp : ∀ᶠ x : ℝ in atTop, 0<t x := ((Work.E09.betaF_growth G L).eventually_gt_atTop 0).mono fun x h=> mul_pos (by norm_num) (Work.E09.temp_pos h)
  obtain ⟨C,d,r,B,k,hB,ht⟩:= h L hL D hD i n₀ χ c₁ W hW μ hm o A a hA v hh (hp.mono (fun x hh=> by unfold v; positivity))
  let B' x:= |B x|; have hb' : Rate G L 0 B':= hB.compare (Eventually.of_forall fun x=> by simp [B'])
  refine ⟨A,a,C,d,v,t,r,B',fun x=> Z*t x,k,?_,hb',?_,?_⟩
  · unfold v t; simpa only [_root_.mul_inv_rev] using! (((inverse_mist G L).mul_right (2:ℝ)⁻¹).mul_right (Z⁻¹*((i:ℝ)+1)⁻¹))
  · intro m z
    have he : Rate G L 0 shiftG := (((Rate.radius_price).mul_left 2).add (Rate.const 1)).mul_left 4
    have hh := ((he.pow (m*i)).mul hb').mul (Q.rate_none L hm 0 (k+m*i+z) 0)
    rw [zero_mul,zero_add, zero_add] at hh; exact hh
  filter_upwards [hp,ht] with x hx hD' c f S T hS hT R B' H W' hRv
  obtain ⟨Ξ,grade,hΞ,hH,hF⟩:=hD' c f S T hS hT R _ H W' hRv; have hZ := hZ; have h:= H.laws.data
  exact ⟨⟨Ξ,hF,mul_nonneg hZ.le hx.le,hx.le,(by have he:= h.room.temperatures; rw [h.funds.length_eq] at he; exact he),
    (by unfold v; positivity),abs_nonneg _, ⟨fun c=> hq c _ hx.le⟩,(by unfold v; nlinarith [mul_nonneg hZ.le hx.le])⟩,grade,hΞ,hH⟩
end YM.ConnectedActivityE6.Blaze.March

namespace YM.PhysicalNext.Repeat.Height
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration Time Supply Input Testing
open ConnectedActivityE6.Blaze Blaze.March Captain PriceCompiler Silica
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge}
section thresholds
variable {μ W:ℝ} {P : Teller G} {Q : YM.ConnectedActivityE6.Target G P}


open Daisy Reserves
private lemma paidRowsFalls (Q: YM.ConnectedActivityE6.Target G P) (L:Side)(hμ:0 < μ)(i:ℕ): Rate G L (3/8+Q.rate) (fun t=> shortfall Q L μ t i):=by
   have hp:Rate G L Q.rate (fun t => (swing Q L μ 0 t 0).rootHit):=(Q.rate_root (C:=0) (β:=0) L hμ).add (Rate.power.mul_right _)
   unfold shortfall treeYield; exact (((((Rate.power (a:=3/8)).mul hp).mul_right _).mul_right _).mul_left _) -- order
-- Post-lattice for a prescribed derivative billing level
variable (P)
def BorrowFundedRows (p:Q.Expense) (j n ℓ:ℕ)(χ:Chi)(o: Target.Order G W)(L:Side)(μ t v a:ℝ): Prop:=
    ∀ (c f:Side)(S:StepData c f)(T:Tube G S), Works P L t S T → Stamp T → ∀(R:Rep G f)(C':ℝ)(H:Cash W t μ L Q o C' T R),∀(D:ℕ→ℝ), Raw.Pumps R D (1*incomingE G L t) →
       ∃ (A b C d r s z B e q:ℝ)(k:ℕ)(N: Captain H j C d r s A b z B e k χ), YM.Integration.ManuscriptQLocalHeightPaidRows.Ready j d B k ∧ r=v ∧ HostQ H N.conduit A B k ∧ Bikes Q L μ t p.earn q B j k ∧ ∀ (ι:Type)(_:Fintype ι) (M:ι→Lotus.Leaf R)(rA:ι→ℝ), (∀ i,0≤rA i) → (∑ i,mcount (S:=S) (G:=G) (L:=L) (s:=t) M rA D ℓ i*R.p.mass (M i).crest (M i).weight) ≤ Q.goal L t →
         Ac.Hit (Captain.reachability (H:=H)) (radiusB t) (fun z=> beaconN H ℓ z*rocket H D z* markU N M rA z n) p.earn a
-- Different Captain fits.B.looms uniform across stages. n,j arbitrary even bought afterwards.
lemma canariesFundedRows (Q:YM.ConnectedActivityE6.Target G P) (p:Q.Expense) (hQ:Q.rate< -(3/8:ℝ)) : ∃ m:ℕ,∀ L:Side,m≤L.val→∀ W μ:ℝ,∀ o:ConnectedActivityE6.Target.Order G W, 0<W→0<μ→∀ j n ℓ χ,∃ v a:ℝ→ℝ,Rate G L (1/2) (fun x=>(v x)⁻¹)∧ Rate G L (3/8+Q.rate) a ∧ ∀ᶠ x in atTop, BorrowFundedRows P p j n ℓ χ o L μ x (v x) (a x):=by
    obtain ⟨m,hm⟩:= adjudicateFundedRows P Q; obtain ⟨b,hb⟩:= Daisy.early Q
    refine ⟨max m b,fun L hL W μ o hW hμ j n ℓ χ=>?_⟩
    by_cases hh : ∃ D : Patch,D.Branches P.bind G ∧ D.L=L ∧ D.J=P.j
    swap; · exact ⟨fun _=>0,fun _=>0,(Rate.const (0:ℝ)⁻¹).weaken (by norm_num), fun e _=> (Delay.shift_pos G L).mono (fun x hx=> by rw [abs_zero]; exact Real.rpow_nonneg hx.le _),Eventually.of_forall fun x c f S T h=> (hh ⟨S.patch,h.funds.kernel,h.length_eq,h.funds.atStep⟩).elim⟩ -- zero fun
    obtain ⟨D,hd,hF,hX⟩:=hh
    obtain ⟨A,a,C,d,v,t,r,B,u,k,hv,hB,hq,H⟩:= hm L ((le_max_left ..).trans hL) D hd j ℓ χ 1 W hW μ hμ o
    let i:= (Q.exp-p.earn)/2; have hi:0 < i:= by unfold i; linarith [p.price,p.worth,p.first,p.second]
    have ht: p.earn+i+i≤Q.exp:=by unfold i; linarith
    let Y s:= Height.allotQ k j (B s) s Q L μ; let E' x:= collars G i x j n*(Y x *(1-1/2:ℝ)⁻¹)
    have h := Height.paidRowsFalls Q L hμ k
    let f x:=grow G L x*(Daisy.swing Q L μ 0 x 0).rootHit
    have hf:Rate G L (3/8+Q.rate) f:= (Rate.power).mul ((Q.rate_root (C:=0) (β:=0) L hμ).add (Rate.power.mul_right _))
    have hY:Rate G L (3/8+Q.rate) Y:= by
       have he := ((hB.mul_left ((2:ℝ)^j)).mul h); rw [zero_add] at he; exact he.add h
    have hη : Rate G L 0 shiftG := (((Rate.radius_price).mul_left 2).add (Rate.const 1)).mul_left 4
    have hU:Rate G L (3/8+Q.rate) E' := by simpa only [zero_add,zero_mul] using! (((hη.pow (n*j)).mul_right (Reserves.polyPrice i (n*j))).mul (hY.mul_right ((1-1/2:ℝ)⁻¹)))
    have hX0 (F:ℝ→ℝ)(i:ℝ)(h:Rate G L (3/8+Q.rate) F):∀ᶠ s in atTop,degreePrice (radiusB s) (F s) i≤1/2:=by
       have he:Rate G L 0 (fun x=>(Animals.ballCost (radiusB x):ℝ)):=by simpa only [one_mul,add_zero] using! (Census.width_rate G L 1 0)
       have hr:Rate G L (3/8+Q.rate) (fun s=> degreePrice (radiusB s) (F s) i):=by
          unfold degreePrice Trees.stretch; simp_rw [div_eq_mul_inv]; simpa only [zero_add] using! ((((he.mul h).mul_right i⁻¹).mul_left 4))
       exact (hr.below (by linarith) (1/2) (by norm_num)).mono fun x hx=> (le_abs_self _).trans hx
    refine ⟨v,E',hv,hU,?_⟩
    filter_upwards [(YM.Work.E09.betaF_growth G L).eventually_ge_atTop 1,H,hX0 f Q.δ hf, hX0 Y i hY,Daisy.stables L Q hμ B hi ht p.price hB j k n] with x hx h hh he hb'
    intro c f S T hp hT R C' H W₀ h'
    obtain ⟨N,grade,hN,hH⟩:= h _ _ S T (hp.patch hF hX) hT R _ H W₀ h'
    have hg:1≤grow G L x := Real.one_le_rpow hx (by norm_num)
    let Z:= swing Q L μ R.beta x C; have ht' : Z.Buy S.patch.L Q.halo (radiusB x):= hp.length_eq.symm ▸ (hb'.1.rev _ _ (hp.length_eq ▸ N.conduit.lives))
    refine ⟨_,_,_,_,_,_,_,_,_,_,k,N,grade,rfl,hH,hb'.1,fun ι H0 M rA hv hw=> extensionQ N hg h'.1 hN M rA hv (hb _ ((le_max_right ..).trans hL)) (by rw [H.laws.intake.sizes,hp.length_eq]; exact hb'.1.covers) hw ht' hh n i p.earn p.price hi ht (?_) he⟩
    unfold shortfall treeYield Reserves.extract Reserves.polyPrice; have hG:0 < (swing Q L μ 0 x 0).rootHit:=ht'.γ; have hx:= Q.usable; positivity
end thresholds
end YM.PhysicalNext.Repeat.Height

end
