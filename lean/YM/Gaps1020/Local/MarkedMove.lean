import YM.Gaps1020.Local.MarkedProducts
import YM.Gaps1020.Local.Manipulation
/-!
# Marked angular Joint integral

Pay all support hints after transfer. Mirrors Manipulation. Uses all
marks on the leaf.

Following AnalyticNext...{Ambit,Tropolis,Mercury}. The same change of
variables works because weights see the same projection on Air. In
particular no differentiating the fine mask or the input; multipliers
also preserve all resultant held-variable paths. Domination here justifies
the integral identity about the real (Healthy) point; use separate purchased
volume-independent prices below.
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

open PhysicalNext.Repeat.Lotus
section path
variable {E : Type*} [MeasurableSpace E]
variable (I : Finset (Bond f)) (X : Coat T F)
variable {Y : E→ F.Slice G} {z : E→ Air f G} (h : Canary G d A) (V : Config G c) (hV : Drivable X d A V)
variable (p : Molecule S) (M:Team R) (π : MulData (others M p)) (hπ : ∀ i, Measurable (π i))
include hπ h hV
lemma teamInland (he : Measurable Y) (hp : Measurable z) (ht : Intake P T X.x R) (hΞ : ShellAccess S G X.x W X.width γ)
    (hh : LocalRatio Ñ) : Measurable (fun i=> teamWeightRecoil I (X.wrapY (Y i)) V d Ñ p R M π W a l (z i)) := by
  let P' i:=X.wrapY (Y i); let f x:=course (P' x) d R.beta (z x) V
  obtain ⟨hJ,hZ⟩:= steering I X h V hV he hp ht.ready hΞ R.beta
  have hm (S : Coat T F) {_V : E→ Body (↥ (lensS I G))} (he:Measurable _V):=bulbB (fun _ _=> measurable_const : Borel fun i:E=> circuit (lensS I G) S.relating) he
  have hF : Measurable (fun x=> scalp I (P' x) V R.beta d (z x)) := hJ.mul ((show Measurable fun x=> lens₀ (circuit (lensS I G) (vary X V).relating)
      (Pond.swim _ (f x)) from hm (vary X V) ((swim_m (lensS I G)).comp (show Measurable f from hZ))).div (hm X ((swim_m (lensS I G)).comp hp)))
  apply Measurable.mul (f:=fun x=> scalp I _ _ _ _ _) hF
  exact teamCollected X hΞ ht hh p M π hπ (V:=fun x:E=>V) measurable_const he hZ

lemma teamWander (hp : X.relating.PosDef) (he : 500≤l) (Y : Support c) (hS : ground R T l X.B p⊆ Y)
    (q : Room P S T X.x) (ht : Intake P T X.x R) (hh : ShellAccess S G X.x W X.width γ) (hÑ : LocalRatio Ñ) (hv : I=edgesM S Y X.B) :
    teamWeightBars p (lensS I G) (vary X V) R M π Ñ W a l=∫ x, (∫ z,teamWeightRecoil I (X.wrapY x) V d Ñ p R M π W a l z ∂X.dice) ∂ F.order G := by
  unfold teamWeightBars; apply integral_congr_ae; filter_upwards with x
  let B:= lensS I G; let Z:= X.wrapY x; let A':= circuit B X.relating
  let J:= sweep A'; have hP : MeasurePreserving (swim B) X.dice J := Pond.orbit hp.posSemidef B
  let f : Air f G → ℝ:= teamWeightRecoil I Z V d Ñ p R M π W a l
  have hF : Measurable f := teamInland (Y:=fun (_:Air _ G)=> x) (z:=id) I X h V hV p M π hπ measurable_const measurable_id ht hh hÑ
  have hB : B=podium S G Y X.B := by unfold B; rw [hv]; exact chargedU ..
  have hf : confined (swim B) f := by
    intro u v hh; unfold f teamWeightRecoil; rw [Flux.slab I Z V u v hh d]; apply congrArg
    have hp := congr_arg (pitch I Z d R.beta V) hh; rw [pitch_alt,pitch_alt] at hp
    apply (teamWeightSync (X:=vary Z V) (X':=vary Z V) (l:=l) (Z:=Y) p M π ?_ q he (show Intake P T (vary Z V).x R from ht) hS)
    refine ⟨Village.refl ..,fun i hi=> (Pond.observe B).mp hp i (hB.symm ▸ hi), fun _ _=>Iff.rfl⟩
  have he: Drivable Z d A V := ⟨fun i=> hV.good i⟩
  let F' z:=lens₀ (circuit B (vary Z V).relating) z * teamWeight p R M π Ñ W a l (vary Z V) (Pond.spill B z)
  change (∫ z,F' z) = ∫ z,f z ∂X.dice
  rw [Pond.gathered (Pond.spill B) (spill_m B) hP (settled _) hf hF]
  change _ = ∫ z, f (Pond.spill B z) ∂ sweep A'
  rw [gyre I Z h ht.positive V he F', Shield.recommends A' (show A'.PosDef from hp.submatrix Subtype.val_injective) _]
  apply integral_congr_ae; filter_upwards with y
  let z:= spill B y; let w:= course Z d R.beta z V; let b:=pitch I Z d R.beta V y; let E v:=teamWeight p R M π Ñ W a l (vary Z V) v
  have hG : E (Pond.spill B b)=E w := by
    refine teamWeightSync (X:=vary Z V) (X':=vary Z V) (Z:=Y) p M π ?_ q (by assumption) (show Intake P T (vary Z V).x R from ht) hS
    exact ⟨Village.refl ..,fun i hi=> (observe B).1 (settled B b) i (hB.symm ▸ hi),fun _ _=> Iff.rfl⟩
  change jacL _ Z d R.beta V z*(lens₀ _ b*E _)=lens₀ A' y*(scalp I Z V R.beta d z* E w)
  have hp : scalp I Z V R.beta d z=jacL I Z d R.beta V z*(lens₀ (circuit B (vary Z V).relating) b/lens₀ A' y) := by
    unfold scalp; dsimp only; rw [show swim B z=y from settled ..]; rfl
  change jacL _ Z d R.beta V z*(lens₀ (circuit B (vary Z V).relating) b*E _)=_
  rw [hG,hp]; field_simp [ne_of_gt (fullFuel A' y)]
end path
section meristem
-- one leaf confers Zest even when the other leaves have no shared inputs.
-- retain the FiniteUniv evidence already in Lotus.Class for this particular
-- one-leaf ingredient chart (isolated sign with floating = 1).
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {V:E→Config G c}{x:E}
lemma leafReady (H : Cash W X.x μ L Q o C T R)(M:Leaf R)
    (h:Glass P X V x j W)(hp:Canary G d b)(ha:8*o.a*Pressure.fiery G X.x S.patch.L≤d/2):
    let w t u:=course (X.wrapY t.1) d R.beta t.2 (V u)
    Zest (fun (a:F.Slice G × Air f G) i=> M.paidU (vary (X.wrapY a.1) (V i)) o.a (worldZ (vary (X.wrapY a.1) (V i)) R.beta (w a i))) x j:=by
  intro g
  have hz:= M.supple X {M.turn.badge S} H h hp ha; simpa only [Leaf.floret, Finset.mem_singleton, if_true, Polar.floating,erase_singleton,prod_empty,mul_one] using! hz
end meristem
section permit
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {V:E → Config G c} {x:E}
variable (H : Cash W s μ L Q o C T R) (hX : X.x=s) (hM : X.manifest) (hK : X.width=o.K)
variable (hq : Glass P X V x j W) (hC : Canary G A b) (he : 8*o.a*Pressure.fiery G s L ≤ A/2)
variable (p : Molecule S)(M:Team R) (π : MulData (others M p)) (hπ : ∀ i, ContDiff ℝ (↑j) (π i))
include H hX hM hK hq hC he hπ
lemma teamMultiplied (I : Finset (Bond f)) :
    let m:=(F.order G).prod X.dice; let g v:= teamWeightRhythm I X (V v) A Q.table p R M π W o.a Q.halo
    Meristem g x m j ∧ ∀ᶠ y in 𝓝 x, Integrable (g y) m := by
  intro m g
  have heq:=H.laws.data; have hv := heq.funds.length_eq; rw [← hv,← hX] at he
  have hM :=heq.localP F X hX hK hM
  have ht:= (hX.symm ▸ H.laws.intake : Intake P T X.x R); have hh: ShellAccess S G X.x W X.width o.γ := by rw [hK,hX]; exact heq.access
  let A' := lensS I G; let U i:=circuit A' (vary X (V i)).relating; let V':= circuit A' X.relating
  have hx: U x=V' := by unfold U V'; rw [hq.lifts]; rfl
  have hF:= hM.sails.fullC; have hU' : V'.PosDef := hF.submatrix Subtype.val_injective
  have hV:= own_mat hM.sails I
  have hs : Bottom V'⁻¹ (1+payE o.eta o.gap o.ample (tubularPrice G L))⁻¹ := Control.lower_inverse hV.relented hV.weather.1.le hV.fuel hV.symmetry
    hV.ground hV.down.le hV.initial.1
  let X'(t:F.Slice G × Air f G):= X.wrapY t.1; let w t v:= course (X' t) A R.beta t.2 (V v)
  let z(t:F.Slice G×Air f G):= Pond.swim A' t.2; have hZ : MeasurePreserving z m (sweep V') := by
    have hs := (Pond.orbit hF.posSemidef A')
    apply hs.comp (show MeasurePreserving _ m X.dice from _); exact MeasureTheory.measurePreserving_snd
  let Z t i:= Pond.swim A' (w t i)
  obtain ⟨hΞ,hω⟩:= Glass.towers (U:=fun i:F.Slice G × Air f G=> i.2) (Y:=fun i=> i.1) hq hM.sails.room hC I ht.positive
  obtain ⟨B,hB,hk,hP⟩:= winglet (A:=U) (Z:=z) (V:=Z) (hx.symm ▸ hU') (hx.symm ▸ hs) (inv_pos.mpr hV.fuel)
    (fun i j=>hq.relate i.val j.val) hω
  let Φ i v:= seats p R M Q.table W o.a Q.halo (vary (X' i) (V v)) (w i v)
  have ht': 4*o.a*X.t < Q.table.radius := by
    have ht:=heq.covers; rw [← hv, ← hX] at ht; exact ht
  have hΨ : Zest Φ x j :=by
    unfold Φ seats; split_ifs
    swap; · exact Zest.still _
    have hr (i:Leaf R):= leafReady (X:=X) (Q:=Q) (o:=o) (show Cash W X.x μ L Q o C T R from hX.symm ▸ H) i hq hC he
    exact (Zest.full M.own _ (fun i _=> hr i)).paint (Zest.full (others M p) _ (fun i _=> tender hq hM.sails.room hC ht p (Y:=Prod.fst) Prod.snd Q.halo Q.table_exists (mul_pos o.large hM.sails.room.fiery) he ht' i))
  let Ψ i v:= teamWeight p R M π Q.table W o.a Q.halo (vary (X' i) (V v)) (w i v)
  have hTransform : Zest Ψ x j := hΨ.paint (Zest.full univ (fun k i v=> π k (row p R Q.table W o.a Q.halo (vary (X' i) (V v)) (w i v) k))
    (fun i (_:i∈ Finset.univ)=> (tender hq hM.sails.room hC ht p (Y:=Prod.fst) Prod.snd Q.halo Q.table_exists (mul_pos o.large hM.sails.room.fiery) he ht' i).wand (hπ i)))
  obtain ⟨J,hJ,hH⟩:= hΞ.post
  obtain ⟨K,h₁,h₂⟩:=hTransform.post
  refine Meristem.points g m ?_ ?_
  · let K' t:=(J*B (z t)*K)*(1+((1+1)+1))^j
    rw [hx] at hk
    have hb : Integrable (B ∘ z) m := (hZ.integrable_comp hB.aestronglyMeasurable).2 hk
    refine ⟨K',((hb.const_mul J).mul_const K).mul_const _,?_⟩
    filter_upwards [hH,h₂,hP] with i hi h hh s
    have hx' := hh s
    -- convert density origin
    rw [hx] at hx'
    exact (((hi s).paints hx').paints (h s)).trim
  obtain ⟨s,h⟩:= hq.sails; filter_upwards [nearby X hC hq.lifts h] with y hh'
  exact teamInland I X hC (V y) hh' p M π (fun i=>(hπ i).continuous.measurable) measurable_fst measurable_snd ht hh Q.table_exists

lemma teamUnfoldBars :
    let m:=(F.order G).prod X.dice; let I:=edgesM S (H.unionP p) (radiusB s)
    let g v:= teamWeightRhythm I X (V v) A Q.table p R M π W o.a Q.halo
    (fun v=> teamWeightBars p (podium S G (H.unionP p) (radiusB s)) (vary X (V v)) R M π Q.table W o.a Q.halo) =ᶠ[𝓝 x]
       fun v=>∫ y, g v y ∂m := by
  intro m I g; obtain ⟨_,ht⟩:= teamMultiplied H hX hM hK hq hC he p M π hπ I
  obtain ⟨v,hv⟩:= hq.sails; have he:= H.laws.data
  filter_upwards [ht,nearby X hC hq.lifts hv] with y hy hY
  rw [← chargedU (H.unionP p) (radiusB s)]; rw [integral_prod _ hy]
  have hs: ground R T Q.halo X.B p=H.unionP p:= by unfold Coat.B; rw [hX]; rfl
  apply teamWander I X hC (V y) hY p M π (fun i=>(hπ i).continuous.measurable) (he.localP F X hX hK hM).sails.fullC Q.buys (H.unionP p) hs.le
    (hX.symm ▸ he.room) (hX.symm ▸ H.laws.intake) (show ShellAccess S G X.x W X.width o.γ from ?_) Q.table_exists
  · unfold I Coat.B; rw [hX]
  rw [hK,hX]; exact he.access

end permit
end YM.ConnectedActivityE6.Blaze.Thermal1020.Shared