import YM.LocalTaylorR2.Terrain

/-!
# On the same union support, global equality of averages, covariance under gauge

Generalize Sterad and Chintz on the same step and support (`Kept`).
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
variable (X : Coat T F) {X' : Coat T F} {U:Support c} {K : Test T}
variable (hx : X.x=s) (hk : X.width=o.K) (hK : Kept H U K)
include hx hk hK
lemma agreesVillage (Z : Support c) (he : U⊆ Z) (hv : Village X X' Z) :
    average X (podium S G Z X.B) K=average X' (podium S G Z X.B) K := by
  let I:=podium S G Z X.B
  have ht : Room P S T X.x:= hx.symm ▸ H.laws.data.room
  have ha : Pond.circuit I X.relating=Pond.circuit I X'.relating := by ext i j; exact hv.same_cov ht j.val j.property i.val
  unfold average; rw [ha]; apply integral_congr_ae; filter_upwards with q; apply integral_congr_ae; filter_upwards with y
  apply congr_arg₂ (·*·) rfl
  exact hK.links F (X.wrapY q) (X'.wrapY q) _ _ hx hk Z he (hv.wrap q q (fun _ _=> rfl)) rfl

lemma averageMeas (I : Finset (Tubular f G)) : Measurable fun y=> average (vary X y) I K := by
  let E' := (Config G c × F.Slice G) × Body (↥ I)
  let V (t:E'):= t.1.1; let Y (t:E'):= t.1.2
  let f' (i:E') := lens₀ (Pond.circuit I (vary X (V i)).relating) i.2 * K F (drive X (V i) (Y i)) (Pond.spill I i.2)
  have hv : Measurable V := measurable_fst.comp measurable_fst
  have hh := c_measured X.shutter (A:=fun i=> (vary X (V i)).plate) (fun i j=> (Art.borel_plate X (show Intake P T X.x R from hx.symm ▸ H.laws.intake).ready i j).comp hv)
  have hz : Measurable f' := (bulbB (fun i j=> hh.1 i.val j.val : Borel fun i=> Pond.circuit I (vary X (V i)).relating) measurable_snd).mul
    (hK.borel E' F X hx hk _ _ _ hv (measurable_snd.comp measurable_fst) ((Pond.spill_m I).comp measurable_snd))
  exact ((hz.stronglyMeasurable.integral_prod_right' (ν:=MeasureTheory.volume)).integral_prod_right' (ν:=F.order G)).measurable

omit hx hk hK in
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
lemma rinseInvariant (i : Finset (Bond f)) (z : Site c→ G.El) (hp : Hue X) :
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
  obtain ⟨V,hV⟩:= vibrance hs hh
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
