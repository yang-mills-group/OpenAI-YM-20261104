import YM.Gaps1020.Local.Warnings
import YM.Gaps1020.Local.MarkedCharge
/-!
# Simultaneous angular controls on Generalized Team of the actual joint FlareW deformation

This extension follows AnalyticNext/CONNECTED_ACTIVITY_JETS_E6/March,
Gio, Captains. Strengthen their controls (after blocks L are chosen
sufficiently large) to expose the Clutch witnesses on the very deformation
which buys the angular budget. Include also warning powers specified at that
same timing, and the rate on conditional vertex velocities needed for the
uniform exponent Taylor remainder.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Thermal1020.Shared
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {j n k : ℕ} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {R : Rep G f}
variable {X : Coat T F} {I : Finset (Bond f)} {η r q Y W A B A' a β b p v d t γ C s C' μ g : ℝ} {l:ℕ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi} {Ñ : ChartRatio G}
variable {z : Air f G}

open March Next.Foundations
open PhysicalNext.Repeat.Lotus PhysicalNext.Repeat.Daisy
-- Flock permits sup+kernel mutually for all Teams, unlike Captain's
-- vacuum contract.
variable {H : Cash W s μ L Q o C T R} {Ξ : Utopia H j v d r C' χ}
def earnedBy (p:Molecule S)(M:Team R)(Ξ: Utopia H j v d r C' χ)(l:ℕ) :=
    if H.ticketsP 0 0 0 p ∧ M.signs S⊆p then (M.weight*∏ i∈others M p, Ξ.fare i)*(1+H.shapeW p)^l else 0
lemma earns (p:Molecule S)(M:Team R)(Ξ: Utopia H j v d r C' χ)(l:ℕ) : 0 ≤ earnedBy p M Ξ l:=by
   unfold earnedBy; split
   next h=> exact mul_nonneg (mul_nonneg M.profit (prod_nonneg fun i _=> Ξ.fares i)) (pow_nonneg (add_nonneg zero_le_one (H.positive_volume _)) _)
   next=> rfl
structure Flock (H : Cash W s μ L Q o C T R)(Ξ : Utopia H j v d r C' χ) (A B:ℝ)(l:ℕ): Prop where
   teams : ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (F : Forest S.ratio) (X : Coat T F)
    (U:E→ Config G c) (y:E) (M:Team R) (p:Molecule S), M.signs S⊆p → X.χ=χ → X.manifest → X.x=s → X.width=o.K → Healthy (Pressure.temp X.x) (H.unionP p) X.V →
    troupe T R Q.halo (radiusB s) p → Ac.Spark H.supportP p → Mode U y j v → U y=X.V →
    let m:=(F.order G).prod X.dice
    ∃ f, Integrable f m ∧ (∫ x,f x ∂m) ≤ B*earnedBy p M Ξ l ∧
      ∀ x, Brush j (f x) 1 (fun t=> teamWeightRhythm (edgesM S (H.unionP p) (radiusB s)) X (U t) A Q.table p R M (emptyTeamData M p) W o.a Q.halo x) y
-- general Teams covers the old vacuum contract identically.
def unmarked (R:Rep G f): Team R:=⟨∅,by simp⟩
lemma turnsEmpty (S:StepData c f)(R:Rep G f): (unmarked R).signs S=∅:= by unfold Team.signs; simp only [unmarked,image_empty]
lemma emptyPower (M:Molecule S)(Ξ:Utopia H j v d r C' χ)(l:ℕ): earnedBy M (unmarked R) Ξ l= Ξ.meant M l:= by
  unfold earnedBy Utopia.meant Team.weight others; simp only [turnsEmpty, empty_subset,and_true,sdiff_empty]; unfold unmarked; simp only [prod_empty,one_mul]
lemma emptyRhythm (M:Molecule S)(Q:ChartRatio G)(U:Config G c)(x:F.Slice G × Air f G):
   teamWeightRhythm I X U A Q M R (unmarked R) (emptyTeamData _ _) W a l x=rhythm I X U A Q M R W a l x:=by
  unfold teamWeightRhythm teamWeightRecoil; rw [lit]; unfold seats; rw [if_pos (show _ from turnsEmpty S R |>.symm ▸ empty_subset M)]; unfold others rhythm recoil; rw [turnsEmpty,sdiff_empty]
  unfold unmarked Team.paidU; simp only [prod_empty,one_mul]
lemma standardFlare (h:Flock H Ξ A B l): FlareW H Ξ A B l:=by
  constructor; intro E _ _ _ F X U y p hχ hM ht hk hH he hf hm hy m
  obtain ⟨f,hf',hH',hB⟩:=h.teams E F X U y (unmarked R) p (turnsEmpty S R |>.symm ▸ empty_subset p) hχ hM ht hk hH he hf hm hy
  rw [emptyPower] at hH'; exact ⟨f,hf',hH',fun x=> by simpa only [emptyRhythm] using! hB x⟩
lemma teamExposer (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P) : ∃ n:ℕ, ∀ (L:Side), n≤L.val →
    ∀ (D:Patch), D.Branches P.bind G → ∀ (r0:ℝ), 0≤r0 → ∀ (i:ℕ) (χ:Chi) (W:ℝ), 0<W → ∀ (μ:ℝ), 0<μ → ∀ (o:Target.Order G W)
      (A f : ℝ), Canary G A f → ∀ (V : ℝ→ℝ), Rate G L (-(1/2)) V → (∀ᶠ x in atTop,0≤V x) →
    ∃ (C : ℝ) (q r p : ℝ→ℝ) (l:ℕ), Rate G L (-(1/2)) q ∧ Rate G L 0 p ∧ Rate G L 0 r ∧ ∀ᶠ x in atTop, ∀ (c f:Side) (S : StepData c f) (T: Tube G S), S.patch=D → Stamp T →
      ∀ (R:Rep G f) (C':ℝ) (H:Cash W x μ L Q o C' T R), 8*o.a* Pressure.fiery G x L ≤ A/2 ∧
      ∃ Ξ : Utopia H i (V x) (q x) (r x) C χ, Flock H Ξ A (|p x|) l ∧ HasClutch Ξ A ∧ WarnBudget (betaF G x L^r0) Ξ := by
  obtain ⟨n,hN⟩:= Thermal1020.arm P Q
  refine ⟨n,fun L hL D hD r0 hr0 i χ W hW μ hm o A f hA V hV hv=>?_⟩
  obtain ⟨B,Z,hB,hZ,hX⟩:= Silica.clips hA P L i χ hV
  have hb:= hB.compare (v:=fun x=>|B x|) (Eventually.of_forall fun x=>(abs_abs _).le)
  obtain ⟨C,r,hC,hr,hχ⟩:= hN L hL D hD r0 hr0 i χ W hW μ hm o V (fun x=>|B x|) hV hv hb
  obtain ⟨k,U,hU,hΓ⟩:= rump P L D hD o.K o.γ W o.a χ i hV hB hv hZ o.indexPay o.f A
  let s:= payE o.eta o.gap o.ample (tubularPrice G L)
  obtain ⟨F,K,hF,hΨ⟩:= walksW G L s (k*i*2)
  obtain ⟨J',hJ',hP',hX'⟩:= Clutch.central G L χ i hb (2*o.a)
  let e x:= 1+|F x|; let v x:=(1+|U x|+2*(r x+J' x))^i; let p x:=e x*v x
  have hh {V:ℝ→ℝ} (h:Rate G L 0 V):= h.compare (v:=fun x=> |V x|) (Eventually.of_forall fun z=> (abs_abs _).le)
  have he:= Rate.const (G:=G) (L:=L) 1
  refine ⟨C,(fun x=> |B x|),r,p,K+i,hb,by unfold p; simpa only [zero_mul,zero_add] using! ((he.add (hh hF)).mul (((he.add
    (hh hU)).add ((hr.add hJ').mul_left 2)).pow i)),hr,?_⟩
  filter_upwards [hχ,hΓ,hX,hX', ((Rate.flame (G:=G) (L:=L)).mul_left (8*o.a)).below (by norm_num) _ (half_pos hA.warm)] with
    x Hx h hx hW hp c f S T hS hT R C' H
  obtain ⟨Ξ,hΞ⟩:= Hx _ _ S T hS hT R C' H
  have hθ:=H.laws.data; have hh:=hθ.funds; have hy := H.laws.intake
  have hp := (le_abs_self _).trans hp
  have hM : HasClutch Ξ A := by
    intro E _ _ _ F' X V y z he hΦ hζ hm hy hv
    obtain ⟨hw,h⟩:= hx _ _ S T F' X he hh hζ R.beta H.laws.intake.positive z E V y hy hv
    exact ⟨_, h o.a (by have hx: X.x=x:=he; unfold Coat.t; rw [he]; exact mul_pos o.large H.laws.data.room.fiery) (by unfold Coat.t; rw [he,hh.length_eq]; exact hp)⟩
  refine ⟨hp,Ξ,⟨?_⟩,hM,hΞ⟩
  intro E _ _ _ F' X Y y M p' hM' hζ hM ht hK hr hu he hf hy' m
  let I:= edgesM S (H.unionP p') (radiusB x); let J:= X.catastrophe (o.ξ/2) R.beta (blaze p')
  let f(z : Air f G):= facescale I z^(k*i); let S':=1+H.shapeW p'; let X' z:= J.indicator f z
  let a:=(M.weight*∏ i∈others M p', Ξ.tag i)*v x*S'^i
  have hR:= hθ.localP F' X ht hK hM
  have hx':(1:ℝ)≤S':= le_add_of_nonneg_right (H.positive_volume p')
  have ha:a≥0 := mul_nonneg (mul_nonneg (mul_nonneg M.profit (prod_nonneg fun _ _=> Ξ.tagged _)) (pow_nonneg (by have hq:= Ξ.active; have hq:= hP' x; positivity) _)) (pow_nonneg (zero_le_one.trans hx') _)
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
    dsimp only; simp_rw [integral_const_mul]; rw [ integral_const]; simp only [probReal_univ,one_smul]; rw [earnedBy,if_pos ⟨(H.attends _).2 he,hM'⟩,Ξ.remixes, remainBlaze]
    apply (mul_le_mul_of_nonneg_left hE ha).trans
    unfold a S' p; rw [abs_of_nonneg (by unfold e v; have h:=Ξ.active; have hq:= hP' x; positivity : 0 ≤ e x*v x)]; apply le_of_eq; ring
  intro ⟨v',z⟩
  let X:= X.wrapY v'; have hZ:= hθ.localP F' X ht hK hM
  obtain ⟨hw,hD⟩:= hx _ _ S T F' X ht hh hζ R.beta hy.positive z E Y y hy' hf
  have hp := hD o.a (mul_pos o.large hZ.sails.room.fiery) (by unfold Coat.t; rw [show X.x=_ from ht,hh.length_eq]; exact hp)
  have hq := h c _ S T hh hS hθ.access E y Y F' X z R ht hK hζ hZ hy hf hp hw I
  have hA'(M:Leaf R): areas R T 0 X.B (M.turn.badge S) ⊆ H.supportP (M.turn.badge S):= by
    change _⊆ areas R T Q.halo (radiusB x) _
    simp_rw [M.turn.badge_area]; exact Corona.halo_mono (by simp) (Subset.refl _)
  have he' :0<o.a*X.t:= hp.pulse
  have hM0 (M:Leaf R):= hW c _ S T F' X ht hζ hh.length_eq (show 0<(2*o.a)*X.t from by rw [mul_assoc]; positivity) E z o.a R.beta y Y _ _ hp _ _ (hA' M)
  have hR' (M:Leaf R): Brush i M.weight (J' x*spanW T R X.B Q.halo (M.turn.badge S)) (fun x=> M.fond (vary X (Y x)) o.a (steer X A (worldZ X R.beta z) (Y x)) (X.input (worldZ X R.beta z))) y:= by
    have hh := (Brush.certified (d:=0) (x:=y) (k:=i) (le_refl 0) (M.ingredient (X.input (worldZ X R.beta z)))|>.climb (M.earn _) (le_refl _)).paints (hM0 M)
    rw [mul_one,zero_add] at hh; apply hh.climb le_rfl
    apply mul_le_mul_of_nonneg_left _ (hP' _); rw [← sparkPath]
    change (coverNumber X.B (footprints T R _ (radiusB x) _):ℝ) ≤ 1+(_ + _)
    rw [← show X.B=radiusB x from congr_arg radiusB ht]
    apply le_trans _ (le_add_of_nonneg_left zero_le_one); exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hR := teamAccent Ξ p' M (X:=X) hM' hu ht hK hζ (show X.manifest from hM) hr hf hp (hP' x) (fun i _=> hR' i) hq (abs_nonneg _)
  change Brush _ _ _ (fun k=> teamWeightRecoil _ _ _ _ _ _ _ _ _ _ _ _ _) _; apply hR.climb _ le_rfl
  by_cases h:z∈J
  · change J.indicator _ z≤ a * X' z; unfold a X'; rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
  change J.indicator _ z≤a * X' z; unfold X'; rw [Set.indicator_of_notMem h,Set.indicator_of_notMem h,mul_zero]
lemma teamOboe (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P) : ∃ n:ℕ, ∀ (L:Side), n≤L.val →
    ∀ (D:Patch), D.Branches P.bind G → ∀ (r0:ℝ), 0≤r0 → ∀ (i:ℕ) (χ:Chi) (W:ℝ), 0<W → ∀ (μ:ℝ), 0<μ → ∀ (o:Target.Order G W)
      (A f : ℝ), Canary G A f → ∀ (V : ℝ→ℝ), Rate G L (-(1/2)) V → (∀ᶠ x in atTop,0≤V x) →
    ∃ (C : ℝ) (q r p : ℝ→ℝ) (l:ℕ), Rate G L 0 p ∧ Rate G L 0 r ∧ ∀ᶠ x in atTop, ∀ (c f':Side) (S : StepData c f') (T: Tube G S), S.patch=D → Stamp T →
      ∀ (R:Rep G f') (C':ℝ) (H:Cash W x μ L Q o C' T R), ∃ Ξ : Utopia H i (V x) (q x) (r x) C χ, Oboe H i (V x) (|p x|) l A f Ξ ∧ Flock H Ξ A (|p x|) l ∧ HasClutch Ξ A ∧ WarnBudget (betaF G x L^r0) Ξ := by
  obtain ⟨n,hN⟩:= Shared.teamExposer P Q
  refine ⟨n,fun L hL D hD r0 hr0 i χ W hW μ hm o A f hA V hV hv=>?_⟩
  obtain ⟨C,q,r,p,l,-,hp,hr,hX⟩:= hN L hL D hD r0 hr0 i χ W hW μ hm o A f hA V hV hv
  have hG:= Glass.portal P D L hD i χ hV hv o.K o.γ W o.indexPay o.f
  refine ⟨C,q,r,p,l,hp,hr,?_⟩
  filter_upwards [hX,hG] with x hx hy c f' S T hS hT R C' H
  obtain ⟨hz,Ξ,hq,hC,hW'⟩:= hx c f' S T hS hT R _ H
  have hg:= H.laws.data
  exact ⟨Ξ,⟨hA,hz,standardFlare hq,fun F X hX hF hv hm=> hy c f' S T hS hg.funds hg.access F X hv hF hX (hg.localP F X hX hv hm)⟩,hq,hC,hW'⟩
lemma teamIssued (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P) : ∃ n:ℕ, ∀ (L:Side), n≤L.val →
    ∀ (D:Patch), D.Branches P.bind G → ∀ (r0:ℝ), 0≤r0 → ∀ (i:ℕ) (χ:Chi) (W:ℝ), 0<W → ∀ (μ:ℝ), 0<μ → ∀ (o:Target.Order G W),
    ∃ (A a C : ℝ) (d v t r B q : ℝ→ℝ) (k:ℕ), Rate G L 0 B ∧ Rate G L 0 r ∧
      (∀ m z:ℕ, Rate G L Q.rate (fun x=>shiftG x^(m*i)* B x * Q.overture L μ x (k+m*i+z))) ∧ ∀ᶠ x in atTop,
      ∀ (c f:Side) (S:StepData c f) (T:Tube G S), S.patch=D→Stamp T→∀ (R:Rep G f) (C':ℝ) (H:Cash W x μ L Q o C' T R),
        ∃ N:Captain H i C (d x) (v x) (t x) A a (r x) (B x) (q x) k χ, Flock H N.conduit A (B x) k ∧ HasClutch N.conduit A ∧ WarnBudget (betaF G x L^r0) N.conduit := by
  obtain ⟨n,h⟩:= Shared.teamOboe P Q; refine ⟨n, fun L hL D hD r0 hr0 i χ W hW μ hm o=>?_⟩
  obtain ⟨A,a,hA⟩:= Eider.weave G; obtain ⟨Z,hZ,hq⟩:= March.oar G i
  let t x := 2*Pressure.fiery G x L
  have he : Rate G L (-(1/2)) t:= Rate.flame.mul_left 2
  let v x := ((i:ℝ)+1)*Z*t x
  have hh : Rate G L (-(1/2)) v:= he.mul_left _
  have hp : ∀ᶠ x : ℝ in atTop, 0<t x := ((Work.E09.betaF_growth G L).eventually_gt_atTop 0).mono fun x h=> mul_pos (by norm_num) (Work.E09.temp_pos h)
  obtain ⟨C,d,r,B,k,hB,hr,ht⟩:= h L hL D hD r0 hr0 i χ W hW μ hm o A a hA v hh (hp.mono (fun x hh=> by unfold v; positivity))
  let B' x:= |B x|; have hb' : Rate G L 0 B':= hB.compare (Eventually.of_forall fun x=> by simp [B'])
  refine ⟨A,a,C,d,v,t,r,B',fun x=> Z*t x,k,hb',hr,?_,?_⟩
  · intro m z
    have he : Rate G L 0 shiftG := (((Rate.radius_price).mul_left 2).add (Rate.const 1)).mul_left 4
    have hh := ((he.pow (m*i)).mul hb').mul (Q.rate_none L hm 0 (k+m*i+z) 0)
    rw [zero_mul,zero_add, zero_add] at hh; exact hh
  filter_upwards [hp,ht] with x hx hD' c f S T hS hT R B' H
  obtain ⟨Ξ,hF,hV,hΨ,hw⟩:=hD' c f S T hS hT R _ H; have hZ := hZ; have h:= H.laws.data
  exact ⟨⟨Ξ,hF,mul_nonneg hZ.le hx.le,hx.le,(by have he:= h.room.temperatures; rw [h.funds.length_eq] at he; exact he),
    (by unfold v; positivity),abs_nonneg _, ⟨fun c=> hq c _ hx.le⟩,(by unfold v; nlinarith [mul_nonneg hZ.le hx.le])⟩,hV,hΨ,hw⟩
end YM.ConnectedActivityE6.Blaze.Thermal1020.Shared
