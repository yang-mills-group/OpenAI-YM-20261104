import YM.RGLocalTaylor.Engine.Rare

/-!
# All-order joint moment estimates: generation on the actual geometry.
`Rare` saves prices for every capped order BEFORE choosing the period or fields;
here settle also the full V-derivative prices and the sharing costs. Include the
expenses from the holding continuation. Based on `FlareW` purchase proofs in
Das/March/etc and `Charm`, adapted to keep all the extra data/suppression.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {η r q a Y W d C' A b s μ C v B : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R}

open March
namespace Awning

/-- All these constant powers and postulates are BEFORE mesh choices; this
ordering of the post L and before L events is used for construction.
Fresh uncertainty register `U`, arbitrary nat. -/
lemma registered (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P) : ∃ n:ℕ, ∀ (L:Side), n≤L.val →
    ∀ (U:ℕ) (D:Patch), D.Branches P.bind G → ∀ (i:ℕ) (χ:Chi) (W:ℝ), 0<W → ∀ (μ:ℝ), 0<μ → ∀ (o:Target.Order G W)
      (A f : ℝ), Canary G A f → ∀ (V : ℝ→ℝ), Rate G L (-(1/2)) V → (∀ᶠ x in atTop,0≤V x) →
    ∃ (C : ℝ) (q r e uJ vJ : ℝ→ℝ) (k l:ℕ), Rate G L (-(1/2)) q ∧ Rate G L 0 r ∧ Rate G L 0 e ∧ Rate G L 0 uJ ∧ Rate G L 0 vJ ∧ ∀ᶠ x in atTop, ∀ (c g:Side) (S : StepData c g) (T: Tube G S), S.patch=D → Stamp T →
      ∀ (R:Rep G g) (C':ℝ) (H:Cash W x μ L Q o C' T R),
      ∃ Ξ : Utopia H i (V x) (q x) (r x) C χ, Awning H Ξ A f (betaF G x L ^ (-(U:ℝ))) (e x) (uJ x) (vJ x) k l := by
  obtain ⟨n,hN⟩:= RareShips.whittle P Q
  refine ⟨n,fun L hL M D hD i χ W hW μ hm o A b hA V hV hv=>?_⟩
  obtain ⟨B,Z,hB,hZ,hX⟩:= Silica.clips hA P L i χ hV
  have hh {V:ℝ→ℝ} {p:ℝ} (h:Rate G L p V) := h.compare (v:=fun x=> |V x|) (Eventually.of_forall fun z=> (abs_abs _).le)
  have hb:= hh hB
  obtain ⟨C,r,hC,hr,hχ⟩:= hN L hL M D hD i χ W hW μ hm o V (fun x=>|B x|) hV hv hb
  obtain ⟨k,U,hU,hΓ⟩:= rump P L D hD o.K o.γ W o.a χ i hV hB hv hZ o.indexPay o.f A
  let s:= payE o.eta o.gap o.ample (tubularPrice G L)
  obtain ⟨F,K,hF,hΨ⟩:= walksW G L s (k*i*2)
  obtain ⟨J',hJ',hP',hX'⟩:= Clutch.central G L χ i hb (2*o.a)
  let e x:= 1+|F x|
  refine ⟨C,(fun x=> |B x|),r,e,(fun x=>|U x|),J',k,K,hb,hr,(Rate.const 1).add (hh hF),hh hU,hJ',?_⟩
  filter_upwards [hχ,hΓ,hX,hX',((Rate.flame (G:=G) (L:=L)).mul_left (8*o.a)).below (by norm_num) _ (half_pos hA.warm)] with
    x Hx h hx hΞa hp c f S T hS hT R C' H
  obtain ⟨Ξ,hΞ⟩:= Hx _ _ S T hS hT R C' H
  have hθ:= H.laws.data; have hh:= hθ.funds; have hy := H.laws.intake
  have hp := (le_abs_self _).trans hp
  let w0 : ℝ:= betaF G x L ^ (-(M:ℝ)); have hN':1 ≤ betaF G x L := by rw [←hh.length_eq]; exact hy.height.le
  have hw0:0≤w0:=Real.rpow_nonneg (zero_le_one.trans hN') _
  have he:1≤e x:= le_add_of_nonneg_right (abs_nonneg _)
  refine ⟨Ξ, hA,hp,hw0,Real.rpow_le_one_of_one_le_of_nonpos hN' (by simp),zero_le_one.trans he,abs_nonneg _,hP' _,?_,?_⟩
  · intro F' X z ht hK hζ hM E _ _ Y y hf hG v
    have hZ:= hθ.localP F' X ht hK hM
    obtain ⟨hw,hD⟩:= hx _ _ S T F' X ht hh hζ R.beta hy.positive z E Y y hG hf
    have hp := hD o.a (mul_pos o.large hZ.sails.room.fiery) (by unfold Coat.t; rw [show X.x=_ from ht,hh.length_eq]; exact hp)
    exact ⟨hp,h c _ S T hh hS hθ.access E y Y F' X z R ht hK hζ hZ hy hf hp hw,
      hΞa _ _ S T F' X ht hζ hh.length_eq (show 0 < 2*o.a*X.t from by rw [mul_assoc]; exact mul_pos zero_lt_two hp.pulse) E z o.a R.beta y Y _ _ hp⟩
  intro F' X p ht hK hζ hM I J
  let f(z : Air f G):= facescale I z^(k*i); let S':= 1+H.shapeW p
  have hR:= hθ.localP F' X ht hK hM
  have hx':(1:ℝ)≤S':= le_add_of_nonneg_right (H.positive_volume p)
  have hQ:MeasurableSet J := Poll.sounded ..
  have hm:=globes I hR.sails (k*i*2)
  have hV := (globes I hR.sails (k*i)).1
  let i':ℝ:= I.card; let V:ℝ:= (lensS I G).card
  have hI: i'≤ S'*ballCost (radiusB x)* (Itinerary.density L:ℝ) := by
    have h:= crewsC H p; rw [hh.length_eq] at h; apply h.trans; unfold S'; gcongr; linarith
  have hV' : V=i'*Fintype.card G.ColorIndex := by simp [V,i',lensS]
  have hp := hm.2.trans (hΨ x i' V S' hx' (Nat.cast_nonneg _) hI hV')
  have hc : ∫ x,f x^2 ∂X.dice ≤ (e x*S'^K)^2 := by
    unfold f; simp_rw [← pow_mul]; apply hp.trans
    exact (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (pow_nonneg (zero_le_one.trans hx') _)).trans
      (le_self_pow₀ (one_le_mul_of_one_le_of_one_le he (one_le_pow₀ hx')) (by omega))
  refine divideC _ f hV _ (by positivity) _ hQ (by rw [← pow_mul, Nat.mul_comm]; rw [pow_mul]; exact hΞ.alert _ X ht hK hζ hM (blaze p)) (pow_nonneg (mul_nonneg hw0 Ξ.awake) _) ?_ hc
  unfold f; simp_rw [← pow_mul]; exact hm.1

lemma available (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P) : ∃ n:ℕ, ∀ (L:Side), n≤L.val →
    ∀ (U:ℕ) (D:Patch), D.Branches P.bind G → ∀ (i:ℕ) (χ:Chi) (W:ℝ), 0<W → ∀ (μ:ℝ), 0<μ → ∀ (o:Target.Order G W),
    ∃ (A a C : ℝ) (q r e uJ vJ v w t B: ℝ→ℝ) (k l:ℕ), Rate G L 0 r ∧ Rate G L 0 e ∧ Rate G L 0 uJ ∧
      Rate G L 0 vJ ∧ Rate G L 0 B ∧ ∀ᶠ x in atTop, ∀ (c g:Side) (S : StepData c g) (T: Tube G S), S.patch=D → Stamp T →
      ∀ (R:Rep G g) (C':ℝ) (H:Cash W x μ L Q o C' T R),
      ∃ N : Captain H i C (w x) (v x) (t x) A a (r x) (B x) (q x) (l+i) χ,
        Awning H N.conduit A a (betaF G x L ^ (-(U:ℝ))) (e x) (uJ x) (vJ x) k l := by
  obtain ⟨n,hn⟩:= registered P Q
  refine ⟨n,fun L hL U D hD i χ W hW μ hm o=>?_⟩
  obtain ⟨A,a,hA⟩:= Eider.weave G; obtain ⟨Z,hZ,hq⟩:= March.oar G i
  let t x := 2*Pressure.fiery G x L
  have he : Rate G L (-(1/2)) t:= Rate.flame.mul_left 2
  let v x := ((i:ℝ)+1)*Z*t x
  have hh : Rate G L (-(1/2)) v:= he.mul_left _
  have hp : ∀ᶠ x : ℝ in atTop, 0<t x := ((Work.E09.betaF_growth G L).eventually_gt_atTop 0).mono fun x h=> mul_pos (by norm_num) (Work.E09.temp_pos h)
  have hv : ∀ᶠ x in atTop,0≤v x := hp.mono fun x h=>by unfold v; positivity
  obtain ⟨C,w,r,e,uJ,vJ,k,l,_,hr,he,hu,hJ,h⟩:= hn L hL U D hD i χ W hW μ hm o A a hA v hh hv
  let B x:= speedBill (e x) (uJ x) (r x) i
  have hB : Rate G L 0 B:= by simpa only [zero_mul,zero_add] using! he.mul ((((Rate.const _).add hu).add (hr.mul_left 2)).pow i)
  refine ⟨A,a,C,(fun x=> Z*t x),r,e,uJ,vJ,v,w,t,B,k,l,hr,he,hu,hJ,hB,?_⟩
  have hG:= Glass.portal P D L hD i χ hh hv o.K o.γ W o.indexPay o.f
  filter_upwards [hG,hp,h] with x hG hp h c f S T hS hT R b H
  obtain ⟨Ξ,h⟩:= h c f S T hS hT R b H; have hg:= H.laws.data
  have hr : 0≤ B x:= mul_nonneg h.earn (by have hr:=Ξ.active; have hu:=h.bSc; positivity)
  exact ⟨⟨Ξ,⟨hA,h.sc,h.flareW,fun F X hX hF hv hm=> hG c f S T hS hg.funds hg.access F X hv hF hX (hg.localP F X hX hv hm)⟩,mul_nonneg hZ.le hp.le,hp.le,(by have he:= hg.room.temperatures; rw [hg.funds.length_eq] at he; exact he),
    (by unfold v; positivity),hr, ⟨fun c=> hq c _ hp.le⟩,(by unfold v; nlinarith [mul_nonneg hZ.le hp.le])⟩,h⟩
end Awning
end YM.RGLocalTaylor
