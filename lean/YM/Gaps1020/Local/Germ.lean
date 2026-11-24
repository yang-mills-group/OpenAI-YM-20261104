import YM.Gaps1020.Local.Manipulation
/-!
# Same gauge/Phi for the weighted complete germ

Following AnalyticNext...Chintz, Gio, Pattern. We retain all the
symmetry/mask conventions and show variation on this weighted
representation. Don't infer later post-reset alignment from these details.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Thermal1020
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


section attitude
private lemma vibrance {ι : Type} [Fintype ι] [DecidableEq ι] {A H Z : Matrix ι ι ℝ} (hp : A*H=H*Z) (he : H*Hᵀ=1) :
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

variable (e : Intake P T X.x R) (h : ShellAccess S G X.x W X.width d) (l : ℕ)
include h e
lemma weightedCoast (p : Molecule S)(π : MulData p) (i : Finset (Bond f)) (z : Site c→ G.El) (hÑ : LocalRatio Ñ) (ha : 0 < a*X.t) (hx : 4*a*X.t < Ñ.radius) (hp : Hue X) :
    weightedBars p π (lensS i G) (rinse X z) R Ñ W a l=weightedBars p π (lensS i G) X R Ñ W a l := by
  let B:=lensS i G; let Y:=rinse X z; let E:= Hues.sheen X z; let H:=Pond.circuit B E
  let A:=Pond.circuit B X.relating; let Z:=Pond.circuit B Y.relating
  have he : Y.relating*E=E*X.relating := relatesG X z e.ready
  have hB i j (hi:i∈ B) (hj:j∉ B) : E i j=0 ∧ E j i=0 := by
    have ht : i.1≠j.1 := by intro h; apply hj; refine mem_product.mpr ⟨h ▸ (mem_product.mp hi).1,mem_univ _⟩
    exact ⟨Rotation.off (z ∘ atEdge S) i j ht,Rotation.off (z ∘ atEdge S) _ _ ht.symm⟩
  have hs : Z*H=H*A := by
    change Batch.principal B _*Batch.principal B _= Batch.principal B _*Batch.principal B _
    rw [← Batch.localize_right (fun i hi j hj=> (hB j i hj hi).2), ← Batch.localize_left (fun i hi j hj=> (hB i j hi hj).1),he]
  have hh : H*Hᵀ=1 := by
    change Batch.principal B E*Batch.principal B Eᵀ=1
    rw [← Batch.localize_left (fun i hi j hj=> (hB i j hi hj).1),Rotation.upside, Batch.within_one]
  obtain ⟨V,hV⟩:= vibrance hs hh; let k:=own p
  have hg (t) : Pond.spill B (V t)=weep X z (Pond.spill B t) := by
    ext i; change (spill B (V t)) i= (E *ᵥ (spill B t).ofLp) i; simp only [Matrix.mulVec,dotProduct]
    classical
    rw [← Finset.sum_subset (subset_univ B) (f:=fun j => E i j*(spill B t).ofLp j) (fun j _ hj=> by simp [Pond.spill,hj])]
    by_cases h : i∈ B
    · have hh : (spill B (V t)) i=(V t).ofLp ⟨i,h⟩ := by simp [Pond.spill,h]
      rw [hh, (hV t).1, Matrix.mulVec, dotProduct, ← sum_attach B]; exact Finset.sum_congr rfl fun j _=> by simp [Pond.spill,j.2]; exact Or.inl rfl
    simp only [Pond.spill,WithLp.ofLp_toLp]
    rw [dif_neg h]; symm; apply sum_eq_zero; intro j hj; rw [(hB _ _ hj h).2,zero_mul]
  unfold weightedBars
  rw [← (drinking X z).integral_comp' (fun y=> ∫ t, lens₀ Z t*weighted p π R Ñ W a l (Y.wrapY y) (Pond.spill B t))]
  apply integral_congr_ae; filter_upwards with y
  rw [← V.measurePreserving.integral_comp V.toHomeomorph.measurableEmbedding (fun t=> lens₀ Z t*weighted p π R Ñ W a l (Y.wrapY (pairs X z y)) (Pond.spill B t))]
  apply integral_congr_ae; filter_upwards with u
  rw [(hV u).2,hg]; apply congr_arg₂ (·*·) rfl
  have hROW (i:Head S) : row p R Ñ W a l (Y.wrapY (pairs X z y)) (weep X z (Pond.spill B u)) i=row p R Ñ W a l (X.wrapY y) (Pond.spill B u) i := by
    let X':=X.wrapY y; let w:=Pond.spill B u; let v:= worldZ X' R.beta w
    have hx' := fights X' z (show ShellAccess S G X'.x W X'.width d from h) (show Intake P T X'.x R from e) l k hÑ
      (show 0<a*X'.t from ha) hx hp v w i; rw [show spinRow S z v=worldZ (sluice X' z) R.beta (weep X' z w) from
        (flight X' z e.ready h ..).symm] at hx'; exact hx'
  exact congr_arg₂ (·*·) (Finset.prod_congr rfl (fun i _=> hROW i)) (Finset.prod_congr rfl (fun i (_:i∈Finset.univ)=> congr_arg (π i) (hROW i)))
end attitude
lemma weightedSpices (p : Molecule S)(π : MulData p) (H : Cash W s μ L Q o C T R) (X : Coat T F) (hX:X.x=s) (U Z : Config G c)
    (hv : Agrees (H.unionP p) U Z) (hf : Healthy (Pressure.temp s) (H.unionP p) X.V) (he : (roster p).flags=∅)
    (Y:S.Choices) :
    let I:=podium S G (H.unionP p) (radiusB s)
    weightedBars p π I (vary ((planted X p).taggedL Y) U) R Q.table W o.a Q.halo=
      weightedBars p π I ((preps (vary X Z) (roster p)).taggedL Y) R Q.table W o.a Q.halo := by
  intro I
  let T:= H.laws.data; let A:= vary ((planted X p).taggedL Y) U; let A':=(preps (vary X Z) (roster p)).taggedL Y
  have hh : I=podium S G (H.unionP p) A.B := by unfold I; change _=podium S G _ (radiusB X.x); rw [hX]
  have hk : Village A A' (H.unionP p) := by
    refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl,hv⟩
    intro i hi; have he':i∉ RG.flags (Pressure.temp X.x) X.V:= by rw [hX]; exact Finset.disjoint_left.mp hf hi
    unfold A A' vary taggedL planted preps place; simp [he,he']
  rw [hh]; exact barsSync p π (show Room P S _ A.x from hX.symm ▸ T.room) Q.buys (show Intake P _ A.x R from hX.symm ▸ H.laws.intake)
    (by change ground R _ Q.halo (radiusB X.x) p ⊆ H.unionP p; rw [hX]; exact Finset.Subset.refl _) hk

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {V : E → Config G c} {x : E}
variable {H : Cash W s μ L Q o C T R} {Ξ : Utopia H j v d r C' χ}
lemma weightedFrieze (X : Coat T F) (W a : ℝ) (p : Molecule S)(π : MulData p) (R : Rep G f) (Ñ : ChartRatio G) (l : ℕ) :
    GaugeInvariant (fun V=> weightedFringe (vary X V) p π R Ñ W a l) := by
  intro z V
  let f:= MeasurableEquiv.piCongrRight (fun i=> MeasurableEquiv.mulRight (z i))
  let U:=(Measure.pi fun _:Site c=>G.probHaar)
  have hp : MeasurePreserving f U U := measurePreserving_pi _ _ (fun i : Site c=> measurePreserving_mul_right G.probHaar (z i))
  let Y:= vary X V; dsimp only [weightedFringe]; rw [← hp.integral_comp' (fun z=> weightedShelter (Y.rinse z) p π R Ñ W a l)]
  apply integral_congr_ae; filter_upwards with u; have ht : gauge u (gauge z V) = gauge (f u) V := by
    funext i; unfold Lattice.gauge; change _= (u _*z _)* V _* (u _*z _)⁻¹; group
  unfold vary rinse; simp_rw [ht]; rfl
lemma seamWeighted (p : Molecule S)(π : MulData p) (hX : X.x=s) (hk : X.width=o.K)(hπ : ∀ i,Measurable (π i)) : Measurable (fun y=> weightedFringe (vary X y) p π R Q.table W o.a Q.halo) ∧
    LocalOn (H.unionP p) (fun y=> weightedFringe (vary X y) p π R Q.table W o.a Q.halo) := by
  let Y:= Measure.pi fun _: Site c=> G.probHaar
  have hz := H.laws.data; have he : Intake P T X.x R := hX.symm ▸ H.laws.intake
  have ht : ShellAccess S G X.x W X.width o.γ := by rw [hX,hk]; exact hz.access
  constructor
  · have hp : Measurable fun (a:Config G c × (Site c → G.El))=> gauge a.2 a.1 := by
      refine measurable_pi_lambda _ fun i=> ?_; dsimp only [Lattice.gauge]; fun_prop
    exact (((shelterMeasured X ht he Q.table_exists p π hπ o.a Q.halo).comp hp).stronglyMeasurable.integral_prod_right' (ν:=Y)).measurable
  intro U V hu; unfold weightedFringe; apply integral_congr_ae; filter_upwards with z; refine shelterLocal (X:=X) p π (hX.symm ▸ hz.room) Q.buys he (gauge z U) (gauge z V) ?_; intro i hi hj; unfold Lattice.gauge; have ht : ground R T Q.halo X.B p=H.unionP p := by unfold Coat.B; rw [hX]; rfl
  rw [ht] at hi hj; rw [hu i hi hj]

lemma weightedRainbow (p : Molecule S)(π : MulData p) (hΘ : Oboe H j v B k A b Ξ) (hX : X.x=s) (hv : X.width=o.K) (hp : X.χ=χ) (he : (roster p).flags=∅)
    (hy : Healthy (Pressure.temp s) (H.unionP p) X.V) (hM : Mode V x j v) (hz : V x=X.V) : ∀ᶠ y in 𝓝 x,
      weightedFringe (vary X (V y)) p π R Q.table W o.a Q.halo = weightedShelter (vary X (V y)) p π R Q.table W o.a Q.halo := by
  let K:= (planted X p); let Y t y:= vary (K.taggedL t) (V y); have ht:= H.laws.data
  have hf t: ∀ᶠ y in 𝓝 x,Hue (Y t y):= eventual_hue (hΘ.flow F (K.taggedL t) hX hp hv (planted_valid X p) E V x hz hM)
    (ht.localP F (K.taggedL t) hX hv (planted_valid X p)).sails
  filter_upwards [eventually_all.mpr hf] with y hh
  let Z:= vary X (V y)
  let a (z:Coat T F):= weightedShelter z p π R Q.table W o.a Q.halo
  have hF z : a (Z.rinse z)=a Z := by
    unfold a weightedShelter; rw [show (Z.rinse z).B=Z.B from rfl, show Z.B=radiusB s from congr_arg _ hX]; split
    next h =>
      apply congr_arg likely; funext q
      let I:=podium S G (H.unionP p) (radiusB s); let b X:= weightedBars p π I (F:=F) (T:=T) X R Q.table W o.a Q.halo
      change b ((preps (vary X (gauge z (V y))) (roster p)).taggedL q)=b ((preps Z (roster p)).taggedL q)
      have ht k : b (vary (K.taggedL q) k)=b ((preps (vary X k) (roster p)).taggedL q) := weightedSpices p π H X hX k k (fun _ _ _=>rfl) hy he q
      unfold Z; rw [← ht, ← ht]
      change b ((Y q y).rinse z)=b (Y q y)
      unfold b I; rw [← chargedU];
      apply weightedCoast (show Intake P T (Y q y).x R from hX.symm ▸ H.laws.intake)
        (show ShellAccess S G (Y q y).x W (Y q y).width o.γ from (by change ShellAccess S G X.x W X.width o.γ; rw [hX,hv]; exact H.laws.data.access))
        _ p π _ z Q.table_exists _ _ (hh q)
      · apply mul_pos o.large; unfold Coat.t; change 0<Pressure.fiery G X.x _; rw [hX]; exact H.laws.data.room.fiery
      unfold Coat.t; change 4*_ * Pressure.fiery G X.x _ < _; rw [hX,H.laws.data.funds.length_eq]; exact H.laws.data.covers
    next => rfl
  change (∫ z, a (Z.rinse z) ∂ _) = a Z; simp_rw [hF]; simp
end YM.ConnectedActivityE6.Blaze.Thermal1020
