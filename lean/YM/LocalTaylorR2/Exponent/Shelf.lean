import YM.LocalTaylorR2.Germ
import YM.LocalTaylorR2.Exponent.Flutter
import YM.LocalTaylorR2.Exponent.Burst

/-! # At the post-period exchange. Here assume only the Burst version
 of the QUALITATIVE bounds. Adapt period-exchange of Port (in turn E6);
 use also full `IntegratorCost` when requesting that, with no formal
 change or condition assumed on modifying the mask.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Port
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {W s μ C : ℝ} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R}
open Bloch Laurent Channel Next.Foundations
variable (I : Finset (Bond f)) (X : Coat T F)
variable {Y : Support c} {K : Test T} {a d A:ℝ}
variable (V : Config G c) (h : Canary G d A) (hV : Drivable X d A V) (hx : X.x=s) (hk : X.width=o.K) (hK : Burst H Y K)

include h hV hx hk hK
lemma measurableTiltBurst {E : Type} [MeasurableSpace E] {Z:E→ F.Slice G} {z:E→ Air f G}
    (he:Measurable Z) (hp:Measurable z) : Measurable (fun i=> tilted R.beta I (X.wrapY (Z i)) V d K (z i)) := by
  have ht : Intake P T X.x R:= hx.symm ▸ H.laws.intake
  have hΞ : ShellAccess S G X.x W X.width o.γ:= by rw [hx,hk]; exact H.laws.data.access
  let P' i:=X.wrapY (Z i); let f x:=course (P' x) d R.beta (z x) V
  obtain ⟨hJ,hZ⟩:= Flux.steering I X h V hV he hp ht.ready hΞ R.beta
  have hm (B : Coat T F) {_V : E→ Body (↥ (lensS I G))} (he:Measurable _V):=bulbB (fun _ _=> measurable_const : Borel fun i:E=> circuit (lensS I G) B.relating) he
  have hF : Measurable (fun x=> scalp I (P' x) V R.beta d (z x)) := hJ.mul ((show Measurable fun x=> lens₀ (circuit (lensS I G) (vary X V).relating)
    (Pond.swim _ (f x)) from hm (vary X V) ((swim_m (lensS I G)).comp (show Measurable f from hZ))).div (hm X ((swim_m (lensS I G)).comp hp)))
  exact hF.mul (hK.borel E F X hx hk (fun _ => V) Z f measurable_const he hZ)

lemma recoilLawBurst (hp : X.relating.PosDef) (hv : I=edgesM S Y X.B) :
    average (vary X V) (lensS I G) K=∫ x, (∫ z,tilted R.beta I (X.wrapY x) V d K z ∂X.dice) ∂ F.order G := by
  unfold average; apply integral_congr_ae; filter_upwards with x
  have ht : Intake P T X.x R:= hx.symm ▸ H.laws.intake
  let B:= lensS I G; let Z:= X.wrapY x; let A':= circuit B X.relating
  let J:= sweep A'; have hP : MeasurePreserving (swim B) X.dice J := Pond.orbit hp.posSemidef B
  let f : Air f G → ℝ:= tilted R.beta I Z V d K
  have hF : Measurable f := measurableTiltBurst I X V h hV hx hk hK (Z:=fun _=>x) (z:=id) measurable_const measurable_id
  have hB : B=podium S G Y X.B := by unfold B; rw [hv]; exact chargedU ..
  have hf : confined (swim B) f := by
    intro u v hh; unfold f tilted; rw [Flux.slab I Z V u v hh d]; apply congrArg
    have hp := congr_arg (pitch I Z d R.beta V) hh; rw [pitch_alt,pitch_alt] at hp
    exact hK.links F _ _ _ _ hx hk Y (Subset.refl _) (Village.refl ..) (show Pond.swim (podium S G Y X.B) _=Pond.swim (podium S G Y X.B) _ from hB ▸ hp)
  have he: Drivable Z d A V := ⟨fun i=> hV.good i⟩
  let F' z:=lens₀ (circuit B (vary Z V).relating) z * K F (vary Z V) (Pond.spill B z)
  change (∫ z,F' z) = ∫ z,f z ∂X.dice
  rw [Pond.gathered (Pond.spill B) (spill_m B) hP (settled _) hf hF]
  change _ = ∫ z, f (Pond.spill B z) ∂ sweep A'
  rw [gyre I Z h ht.positive V he F', Shield.recommends A' (show A'.PosDef from hp.submatrix Subtype.val_injective) _]
  apply integral_congr_ae; filter_upwards with y
  let z:= spill B y; let w:= course Z d R.beta z V; let b:=pitch I Z d R.beta V y; let E v:= K F (vary Z V) v
  have hG : E (Pond.spill B b)=E w := by
    apply hK.links _ _ _ _ _ (show (vary Z V).x=s from hx) hk Y (Subset.refl _) (Village.refl ..)
    change swim (podium S G Y X.B) _=swim (podium S G Y X.B) _
    -- avoid dependency on b: from equal Air coordination
    let u:=Pond.spill B b; have hf : ∀ i ∈ B, u i=w i := (observe B).1 (settled B b)
    exact (observe _).2 (fun i hi=> hf i (hB.symm ▸ hi))
  change jacL _ Z d R.beta V z*(lens₀ _ b*E _)=lens₀ A' y*(scalp I Z V R.beta d z* E w)
  have hp : scalp I Z V R.beta d z=jacL I Z d R.beta V z*(lens₀ (circuit B (vary Z V).relating) b/lens₀ A' y) := by
    unfold scalp; dsimp only; rw [show swim B z=y from settled ..]; rfl
  change jacL _ Z d R.beta V z*(lens₀ (circuit B (vary Z V).relating) b*E _)=_
  rw [hG,hp]; field_simp [ne_of_gt (fullFuel A' y)]
end YM.LocalTaylorR2.Port


set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Port
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {W s μ C : ℝ} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R}
open Bloch Laurent Channel Next.Foundations
variable (X : Coat T F) {X' : Coat T F} {U:Support c} {K : Test T}
variable (hx : X.x=s) (hk : X.width=o.K) (hK : Burst H U K)
include hx hk hK
lemma agreesVillageBurst (Z : Support c) (he : U⊆ Z) (hv : Village X X' Z) :
    average X (podium S G Z X.B) K=average X' (podium S G Z X.B) K := by
  let I:=podium S G Z X.B
  have ht : Room P S T X.x:= hx.symm ▸ H.laws.data.room
  have ha : Pond.circuit I X.relating=Pond.circuit I X'.relating := by ext i j; exact hv.same_cov ht j.val j.property i.val
  unfold average; rw [ha]; apply integral_congr_ae; filter_upwards with q; apply integral_congr_ae; filter_upwards with y
  apply congr_arg₂ (·*·) rfl
  exact hK.links F (X.wrapY q) (X'.wrapY q) _ _ hx hk Z he (hv.wrap q q (fun _ _=> rfl)) rfl

lemma averageMeasBurst (I : Finset (Tubular f G)) : Measurable fun y=> average (vary X y) I K := by
  let E' := (Config G c × F.Slice G) × Body (↥ I)
  let V (t:E'):= t.1.1; let Y (t:E'):= t.1.2
  let f' (i:E') := lens₀ (Pond.circuit I (vary X (V i)).relating) i.2 * K F (drive X (V i) (Y i)) (Pond.spill I i.2)
  have hv : Measurable V := measurable_fst.comp measurable_fst
  have hh := c_measured X.shutter (A:=fun i=> (vary X (V i)).plate) (fun i j=> (Art.borel_plate X (show Intake P T X.x R from hx.symm ▸ H.laws.intake).ready i j).comp hv)
  have hz : Measurable f' := (bulbB (fun i j=> hh.1 i.val j.val : Borel fun i=> Pond.circuit I (vary X (V i)).relating) measurable_snd).mul
    (hK.borel E' F X hx hk _ _ _ hv (measurable_snd.comp measurable_fst) ((Pond.spill_m I).comp measurable_snd))
  exact ((hz.stronglyMeasurable.integral_prod_right' (ν:=MeasureTheory.volume)).integral_prod_right' (ν:=F.order G)).measurable

omit hx hk hK in
private lemma vibranceBurst {ι : Type} [Fintype ι] [DecidableEq ι] {A H Z : Matrix ι ι ℝ} (hp : A*H=H*Z) (he : H*Hᵀ=1) :
    ∃ E : Body ι≃ₗᵢ[ℝ] Body ι, ∀ t, (E t).ofLp= H *ᵥ (WithLp.ofLp t) ∧ lens₀ A (E t)=lens₀ Z t := by
  let L := Matrix.toEuclideanLin H
  have hh w v : inner ℝ (L w) (L v)=inner ℝ w v := by
    simp_rw [PiLp.inner_apply,RCLike.inner_apply,starRingEnd_apply,star_trivial]; exact respects _ (mul_eq_one_comm.mp he) (WithLp.ofLp v) (WithLp.ofLp w)
  have ht : A.det= Z.det:= mul_right_cancel₀ (Matrix.isUnit_det_of_right_inverse he).ne_zero (by rw [mul_comm Z.det,← Matrix.det_mul,hp,Matrix.det_mul])
  have hz : Surjective (L.isometryOfInner hh) := by
    intro x; refine ⟨WithLp.toLp _ (Hᵀ *ᵥ x.ofLp),?_⟩
    change WithLp.toLp _ (H *ᵥ (Hᵀ *ᵥ x.ofLp))=x; rw [Matrix.mulVec_mulVec,he,Matrix.one_mulVec,WithLp.toLp_ofLp]
  let V:= LinearIsometryEquiv.ofSurjective _ hz
  refine ⟨V,fun t=> ⟨rfl,?_⟩⟩
  unfold lens₀; rw [ht,show (V t).ofLp= H *ᵥ t.ofLp from rfl,Matrix.mulVec_mulVec,reverses hp he, ← Matrix.mulVec_mulVec,
    respects _ (mul_eq_one_comm.mp he)]
lemma rinseInvariantBurst (i : Finset (Bond f)) (z : Site c→ G.El) (hp : Hue X) :
    average (rinse X z) (lensS i G) K=average X (lensS i G) K := by
  have hI : Intake P T X.x R:= hx.symm ▸ H.laws.intake
  let B:=lensS i G; let Y:=rinse X z; let E:= Hues.sheen X z; let H:=Pond.circuit B E
  let A:=Pond.circuit B X.relating; let Z:=Pond.circuit B Y.relating
  have he : Y.relating*E=E*X.relating := relatesG X z hI.ready
  have hB i j (hi:i∈ B) (hj:j∉ B) : E i j=0 ∧ E j i=0 := by
    have ht : i.1≠j.1 := by intro h; apply hj; refine mem_product.mpr ⟨h ▸ (mem_product.mp hi).1,mem_univ _⟩
    exact ⟨Rotation.off (z ∘ atEdge S) i j ht,Rotation.off (z ∘ atEdge S) _ _ ht.symm⟩
  have hs : Z*H=H*A := by
    change Batch.principal B _*Batch.principal B _= Batch.principal B _*Batch.principal B _
    rw [← Batch.localize_right (fun i hi j hj=> (hB j i hj hi).2), ← Batch.localize_left (fun i hi j hj=> (hB i j hi hj).1),he]
  have hh : H*Hᵀ=1 := by
    change Batch.principal B E*Batch.principal B Eᵀ=1
    rw [← Batch.localize_left (fun i hi j hj=> (hB i j hi hj).1),Rotation.upside, Batch.within_one]
  obtain ⟨V,hV⟩:= vibranceBurst hs hh
  have hg (t) : Pond.spill B (V t)=weep X z (Pond.spill B t) := by
    ext i; change (spill B (V t)) i= (E *ᵥ (spill B t).ofLp) i; simp only [Matrix.mulVec,dotProduct]
    classical
    rw [← Finset.sum_subset (subset_univ B) (f:=fun j => E i j*(spill B t).ofLp j) (fun j _ hj=> by simp [Pond.spill,hj])]
    by_cases h : i∈ B
    · have hh : (spill B (V t)) i=(V t).ofLp ⟨i,h⟩ := by simp [Pond.spill,h]
      rw [hh, (hV t).1, Matrix.mulVec, dotProduct, ← sum_attach B]; exact Finset.sum_congr rfl fun j _=> by simp [Pond.spill,j.2]; exact Or.inl rfl
    simp only [Pond.spill,WithLp.ofLp_toLp]
    rw [dif_neg h]; symm; apply sum_eq_zero; intro j hj; rw [(hB _ _ hj h).2,zero_mul]
  unfold average
  rw [← (drinking X z).integral_comp' (fun y=> ∫ t, lens₀ Z t*K F (Y.wrapY y) (Pond.spill B t))]
  apply integral_congr_ae; filter_upwards with y
  rw [← V.measurePreserving.integral_comp V.toHomeomorph.measurableEmbedding (fun t=> lens₀ Z t*K F (Y.wrapY (pairs X z y)) (Pond.spill B t))]
  apply integral_congr_ae; filter_upwards with u
  rw [(hV u).2,hg]; apply congr_arg₂ (·*·) rfl
  exact hK.rotate F (X.wrapY y) hx hk hp z (Pond.spill B u)
end YM.LocalTaylorR2.Port


set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Port
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {W s μ C : ℝ} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R}
open Bloch Laurent Channel Next.Foundations Progress.StationaryScenes.Green Census
variable {I : Finset (Bond f)} {j l:ℕ} {A B C' K' d v r b:ℝ} {U : Support c} {K : Test T} {χ : Chi}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {V : E → Config G c} {x : E} {X:Coat T F}
variable (hX : X.x=s) (hM : X.manifest) (hK : X.width=o.K) (htK : Burst H U K)
variable (hq : Glass P X V x j W) (hC : Canary G A b) (he : 8*o.a*Pressure.fiery G s L ≤ A/2)
include hX hM hK htK hq hC he
lemma periodExchangeBurst  :
    let I := edgesM S U (radiusB s); let m:=(F.order G).prod X.dice; let g v:= duoTilt R.beta I X (V v) A K
    Meristem g x m j ∧ ∀ᶠ y in 𝓝 x, Integrable (g y) m := by
  intro I m g
  have heq:=H.laws.data; have hv := heq.funds.length_eq; rw [← hv,← hX] at he
  have hM :=heq.localP F X hX hK hM
  have ht:= (hX.symm ▸ H.laws.intake : Intake P T X.x R); have hh: ShellAccess S G X.x W X.width o.γ := by rw [hK,hX]; exact heq.access
  let A' := lensS I G; let U' i:=circuit A' (vary X (V i)).relating; let V':= circuit A' X.relating
  have hx: U' x=V' := by unfold U' V'; rw [hq.lifts]; rfl
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
  let Φ i v:= K F (vary (X' i) (V v)) (w i v)
  have hax : 8*o.a*Pressure.fiery G s L ≤ A/2:= by rw [← hv,← hX]; exact he
  have hΨ : Exponent.Drifts (towerScale S U X.B F) Φ x j:= htK.clutch F X hX hK (by assumption) j A b E V x hq hC hax _ (Subset.refl _)
  obtain ⟨J,hJ,hH⟩:= hΞ.post
  obtain ⟨K,h₁,k,h₂⟩:=hΨ.full
  obtain ⟨B,hB,-,hk,hP⟩:= wingletR2 k (A:=U') (Z:=z) (V:=Z) (hx.symm ▸ hU') (hx.symm ▸ hs) (inv_pos.mpr hV.fuel)
    (fun i j=>hq.relate i.val j.val) hω
  refine Meristem.points g m ?_ ?_
  · let b':= fun v : Body (↥ A') => B v*(1+‖v‖)^k
    let K' t := (J*b' (z t)*K)*(1+((1+1)+1))^j
    rw [hx] at hk
    have hFb : Measurable b' := hB.mul (show Measurable (fun v:Body (↥ A')=> (1+‖v‖)^k) by fun_prop)
    have hb : Integrable (b' ∘ z) m := (hZ.integrable_comp hFb.aestronglyMeasurable).2 hk
    refine ⟨K',((hb.const_mul J).mul_const K).mul_const _,?_⟩
    filter_upwards [hH,h₂,hP] with i hi h hh s'
    have hx' := hh s'; rw [hx] at hx'
    have hp : 1 + ‖z s'‖=towerScale S U X.B F s' := by change 1 + ‖swim A' _‖ = towerScale S U X.B F s'; unfold towerScale; rw [show X.B=radiusB s from congr_arg _ hX, show A'=_ from chargedU (S:=S) (G:=G) U (radiusB s)]
    -- now commute the allowance
    refine (((hi s').paints hx').paints (h s')).trim.climb (le_of_eq ?_) le_rfl
    unfold K' b'; rw [hp]; ring
  obtain ⟨s,h⟩:= hq.sails; filter_upwards [nearby X hC hq.lifts h] with y hh'
  exact measurableTiltBurst I X (V y) hC hh' hX hK htK measurable_fst measurable_snd

lemma slopesBurst :
    let m:=(F.order G).prod X.dice; let I:=edgesM S U (radiusB s)
    (fun y=> average (vary X (V y)) (podium S G U (radiusB s)) K) =ᶠ[𝓝 x]
       fun v=>∫ y, duoTilt R.beta I X (V v) A K y ∂m := by
  intro m I; obtain ⟨_,ht⟩:= periodExchangeBurst hX hM hK htK hq hC he
  obtain ⟨v,hv⟩:= hq.sails
  filter_upwards [ht,nearby X hC hq.lifts hv] with y hy hY
  rw [← chargedU U (radiusB s), integral_prod _ hy]
  apply recoilLawBurst _ X _ hC hY hX hK htK (H.laws.data.localP F X hX hK hM).sails.fullC
  change edgesM S _ _=edgesM S _ (radiusB X.x); rw [hX]

omit hX hM hK htK hq hC he

variable {Ξ : Utopia H j v d r C' χ}
include hX hM hK htK
lemma landsBurst (hC : Oboe H j v B l A b Ξ) (hp:IntegrandCost H U K j A v K' χ)
    (hz:X.χ=χ) (hU:Healthy (Pressure.temp s) U X.V) (hV: Mode V x j v) (hx: V x=X.V):
    Brush j K' 1 (fun y=> average (vary X (V y)) (podium S G U (radiusB s)) K) x := by
  let hq:=hC.flow F X hX hz hK hM E V x hx hV
  obtain ⟨f,hf,h,p⟩:= hp.bound F X hX hK hM hz hU E V x hV hx
  exact ((periodExchangeBurst hX hM hK htK hq hC.conduit hC.mode).1.buds f hf zero_le_one h
    (Filter.Eventually.of_forall p)).shimmy (slopesBurst hX hM hK htK hq hC.conduit hC.mode)


end YM.LocalTaylorR2.Port


