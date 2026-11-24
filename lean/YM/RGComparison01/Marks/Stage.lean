import YM.RGComparison01.Marks.Field
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lotus
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ Λ μ s κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
open Bloch Laurent Progress.StationaryScenes Green Census Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Shield Eider Flux Hues Rotation
open Packets Art Silica Poll Pond
open YM.RGComparison01
namespace Team
variable (M : Team R) (X : Coat T F) {U : Cash W s μ L Q o C T R}
variable {E:Type} {d C' D A B Y v :ℝ} {j k ℓ:ℕ} {χ:Chi} {Ω : Utopia U j v d r C' χ}
variable {Ψ : ℕ→Prop} {b:ℕ→ℝ} {e:ℝ}
-- require *only* prices on selected part
structure Casing (R : Rep G f) (b : ℕ→ℝ) (Ψ : ℕ→Prop) : Prop where
  value : ∀ i, Ψ i→ ∀ U, |R.activities.regularOccurrence R.p i U| ≤ b i
  paid : ∀ i, Ψ i → b i ≤ 1
lemma Casing.nonneg (h:Casing R b Ψ) : ∀ i,Ψ i→0≤b i := fun i hp=> (abs_nonneg _).trans (h.value i hp 1)

abbrev whole (Ω:Utopia U j v d r C' χ) (n : ℕ) (B : ℝ) (w : Head S→ℝ) (p:Molecule S):=
    if U.ticketsP 0 0 0 p ∧ M.signs S ⊆ p then B*(M.weight*∏ i∈p\M.signs S, w i) * Ω.rad^(blaze p).card *(1+U.shapeW p)^n else 0
lemma whole_nn {F:Head S→ℝ}(h : 0≤B)(he: ∀ i,0≤F i)(p:Molecule S):0 ≤ M.whole Ω k B F p:=by
  unfold whole; split
  next => exact mul_nonneg (mul_nonneg (mul_nonneg h (mul_nonneg M.profit (Finset.prod_nonneg fun i _=> he _))) (pow_nonneg Ω.awake _)) (pow_nonneg (add_nonneg zero_le_one (U.positive_volume _)) _)
  next=> exact le_rfl

structure Range (Ω:Utopia U j v d r C' χ) (e B A Y : ℝ) (l:ℕ):Prop where
  unmarked : Lane U j v A Y χ
  paidE : 0 ≤ e
  paidB : 0 ≤ B
  stall : ∀ (M:Team R) (b:ℕ→ℝ) (Ψ : ℕ→Prop), Casing R b Ψ → ∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] (F : Forest S.ratio) (X : Coat T F)
    (P:E → Config G c) (x:E) (p:Molecule S), X.χ=χ → X.manifest → X.x=s → X.width=o.K → Healthy (Pressure.temp X.x) (U.unionP p) X.V →
    troupe T R Q.halo (radiusB s) p → Ac.Spark U.supportP p → M.signs S ⊆ p → Mode P x j v → P x=X.V →
    let m:=(F.order G).prod X.dice
    ∃ f, Integrable f m ∧ (∫ y,f y ∂m) ≤ M.whole Ω l B (maskRaise Ω Ψ b e) p ∧
      ∀ z, Brush j (f z) 1 (fun t=> M.crop (edgesM S (U.unionP p) (radiusB s)) X (P t) A Q.table p W o.a Q.halo z) x

lemma cloak_team (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P) : ∃ n:ℕ, ∀ (L:Side), n≤L.val →
    ∀ (D:RG.Patch), D.Branches P.bind G → ∀ (i:ℕ) (χ:Chi) (W:ℝ), 0<W → ∀ (μ:ℝ), 0<μ → ∀ (o:Target.Order G W)
      (A f : ℝ), Canary G A f → ∀ (V : ℝ→ℝ) (bB:ℕ), Fine G L V → (∀ᶠ x in atTop,0≤V x) →
    ∃ (e C : ℝ) (q r p : ℝ→ℝ) (l:ℕ), Fine G L q ∧ Rate G L 0 r ∧ Geo G L p ∧ ∀ᶠ x in atTop, ∀ (c f':Side) (S : StepData c f') (T: Tube G S), S.patch=D → Stamp T →
      ∀ (R:Rep G f') (C':ℝ) (H:Cash W x μ L Q o C' T R),
      ∃ Ξ : Utopia H i (V x) (q x) (r x) C χ, Worthy Ξ (fun _=>1) (Height.grow G L x^bB) ∧ Range Ξ e (p x) A f l := by
  obtain ⟨n,hN⟩:= Utopia.abundant P Q
  refine ⟨n,fun L hL D hD i χ W hW μ hm o A f hA V bB hV hv=>?_⟩
  obtain ⟨B,Z,hB,hZ,hX⟩:= Silica.franks hA P L i χ hV
  obtain ⟨C,r,hC,hr,hχ⟩:= hN L hL D hD i χ W hW μ hm o V (fun x=>|B x|) bB hV.dividend hv hB.higher.dividend
  obtain ⟨k,U,hU,hΓ⟩:= Flux.premium P L D hD o.K o.γ W o.a χ i hV hB hv hZ o.indexPay o.f A
  obtain ⟨z,hz,hΨ⟩:= Brush.expands i
  have hG:= Glass.portal P D L hD i χ hV.dividend hv o.K o.γ W o.indexPay o.f
  let s:= payE o.eta o.gap o.ample (tubularPrice G L)
  obtain ⟨F,K,hF,hΘ⟩:= Flux.dread G L s (k*i*2)
  obtain ⟨J,hJ,hP,hX'⟩:= Clutch.coronet G L χ i hB.higher (2*o.a)
  let t x:= 1+ J x; have h x:1 ≤ t x:= le_add_of_nonneg_right (hP _)
  let e x:= 1+|F x|; let v x:=(1+|U x|+2*t x)^i; let p x:= e x*v x
  have he:= Geo.fixed (G:=G) (L:=L) 1; have hh x:0≤p x:=by unfold p e v; have ht:=h x; positivity
  refine ⟨z,C,(fun x=> |B x|),r,p,K+i,hB.higher, hr,by exact ((he.joins hF.mean).times (((he.joins hU.mean).joins ((Geo.fixed _).times (he.joins hJ))).power i)),?_⟩
  filter_upwards [hχ,hΓ,hX,hX',hG, ((Rate.flame (G:=G) (L:=L)).mul_left (8*o.a)).below (by norm_num) _ (half_pos hA.warm)] with
    x Hx hΓ hx hX' hg hp c f' S T hS hT R C' H
  have hQ := H.laws.data; have hF:=hQ.funds; have hy := H.laws.intake
  have hΛ : Tithe.Ticket R.activities R.p (fun _=>1) (2*incomingE G L x) := by
    have he' : R.activities.EBound R.p (incomingE G L x):= by rw [← hF.length_eq]; exact hy.cap.labels.boundE
    apply Tithe.no_charge _ _ he' ?_ (fun _=>rfl); obtain ⟨c,h,hP⟩:=he'; exact budget_nonneg (hP 0)
  obtain ⟨Ξ,HΞ⟩:= Hx _ _ S T hS hT R C' H _ hΛ
  have hp := (le_abs_self _).trans hp; refine ⟨Ξ,HΞ,⟨hA,hp,fun F' X ht hy hv hm=> hg c f' S T hS hF hQ.access F' X hv hy ht (hQ.localP F' X ht hv hm)⟩,hz,hh _,?_⟩
  intro M b Ψ hΛ E _ _ _ F' X Y y p' hζ hη ht hK hL hu hj hM hf hy' m
  let I:= edgesM S (H.unionP p') (radiusB x); let J':= X.catastrophe (o.ξ/2) R.beta (blaze p')
  let f(z : Air f' G):= facescale I z^(k*i); let S':=1+H.shapeW p'; let X' z:= J'.indicator f z
  let f₁:= maskRaise Ξ Ψ b z; let a:=(M.weight*(∏ i∈ p'\M.signs S, f₁ i))*v x*S'^i
  have hR:= hQ.localP F' X ht hK hη
  have hx':(1:ℝ)≤S':= le_add_of_nonneg_right (H.positive_volume p')
  have h₁ i:0≤ f₁ i:= raises _ hz hΛ.nonneg i
  have ha:a≥0 := mul_nonneg (mul_nonneg (mul_nonneg M.profit (prod_nonneg fun _ _=> h₁ _)) (pow_nonneg (by have ht':= h x; positivity) _)) (pow_nonneg (zero_le_one.trans hx') _)
  have hZ:MeasurableSet J' := Poll.sounded ..
  have hm:=globes I hR.sails (k*i*2); have hV := (globes I hR.sails (k*i)).1
  have hTax : Integrable (X': Air _ G→ℝ) X.dice := hV.indicator hZ
  have hE: ∫ x,X' x ∂X.dice ≤ (e x*S'^K)*Ξ.rad^(blaze p').card := by
    let i':ℝ:= I.card; let V:ℝ:= (lensS I G).card
    have hI: i'≤ S'*Animals.ballCost (radiusB x)* (Itinerary.density L:ℝ) := by
      have h:= Flux.crewsC H p'; rw [hF.length_eq] at h; apply h.trans; unfold S'; gcongr; linarith
    have he: 1≤e x:= le_add_of_nonneg_right (abs_nonneg _)
    have hV' : V=i'*Fintype.card G.ColorIndex := by simp [V,i',lensS]
    have hp := hm.2.trans (hΘ x i' V S' hx' (Nat.cast_nonneg _) hI hV')
    have hc : ∫ x,f x^2 ∂X.dice ≤ (e x*S'^K)^2 := by
      unfold f; simp_rw [← pow_mul]; apply hp.trans
      exact (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (pow_nonneg (zero_le_one.trans hx') _)).trans
        (le_self_pow₀ (one_le_mul_of_one_le_of_one_le he (one_le_pow₀ hx')) (by omega))
    refine divideC _ f hV _ (by positivity) _ hZ (by rw [← pow_mul, Nat.mul_comm]; rw [pow_mul]; exact Ξ.ship _ X ht hK hζ hη (blaze p')) (pow_nonneg Ξ.awake _) ?_ hc
    unfold f; simp_rw [← pow_mul]; exact hm.1
  have hhP: Integrable (fun z:F'.Slice G × Air _ G=> a*X' z.snd) m := (hTax.const_mul a).comp_snd _
  refine ⟨fun z=> a*X' z.2,hhP,?_,?_⟩
  · rw [integral_prod _ hhP]; dsimp only; simp_rw [integral_const_mul]; rw [ integral_const]; simp only [probReal_univ,one_smul]; unfold Team.whole; rw [if_pos ⟨⟨hj,Nat.zero_le _,Nat.zero_le _,H.positive_volume _⟩,hM⟩]
    apply (mul_le_mul_of_nonneg_left hE ha).trans; unfold a S' p; exact le_of_eq (by unfold f₁; rw [pow_add]; ring)
  intro ⟨v',Z'⟩
  let X:= X.wrapY v'; have hZ:= hQ.localP F' X ht hK hη
  obtain ⟨hw,hD⟩:= hx _ _ S T F' X ht hF hζ R.beta hy.positive Z' E Y y hy' hf
  have hp := hD o.a (mul_pos o.large hZ.sails.room.fiery) (by unfold Coat.t; rw [show X.x=_ from ht,hF.length_eq]; exact hp)
  have hq := hΓ c _ S T hF hS hQ.access E y Y F' X Z' R ht hK hζ hZ hy hf hp hw I
  have hψ:= hX' c f' S T F' X ht hζ hF.length_eq (show 0<2*o.a*X.t from by rw [mul_assoc]; exact mul_pos (by norm_num) hp.pulse) E Z' o.a R.beta y Y _ _ hp
  have hΩ:= Team.extra_cloth X Ψ Ξ ht hK hζ (show X.manifest from hη) hf hp (h x) (fun P B H=> ((hψ P B H).climb le_rfl (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (Nat.cast_nonneg _)))) (fun F t q h=>hΨ E _ t q F h) hΛ.value hΛ.paid
  apply (M.trail_budget X hu hM ht hK (show X.manifest from hη) hL hf hp hΩ (h x) hq (abs_nonneg _) h₁).climb _ le_rfl
  by_cases h:Z'∈J'
  · unfold a; change J'.indicator _ Z'≤ (_*v x*S'^i) * J'.indicator f Z'; rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
  change J'.indicator _ Z'≤a * J'.indicator _ Z'; rw [Set.indicator_of_notMem h,Set.indicator_of_notMem h,mul_zero]
end Team
end YM.PhysicalNext.Repeat.Lotus
