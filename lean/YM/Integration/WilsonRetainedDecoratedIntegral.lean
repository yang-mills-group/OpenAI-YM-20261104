import YM.Integration.WilsonRetainedDecoratedWord

/-! The original Haar--Gaussian integral of a whole marked word at its rooted replacement price. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true

noncomputable section
namespace YM.Integration.WilsonRetainedDecoratedIntegral

open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open LocalTaylorR2 LocalTaylorR2.Port RGLocalTaylor RGLocalTaylor.Insert RGLocalTaylor.Mayer
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open WilsonRetainedMiniatureTaylor WilsonRetainedDecoratedWord
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
  {P : Teller G} {Q : ConnectedActivityE6.Target G P} {W s μ C : ℝ} {o : Target.Order G W}
  {R : Rep G f} {H : Cash W s μ L Q o C T R} {team select : Molecule S} {M : ℕ}

theorem cofactor (H : Cash W s μ L Q o C T R) (A : Team R) (team : Molecule S)
    (inside : A.signs S ⊆ team) (X : Coat T F) (z : momentSpace X) :
    |partners team (team\A.signs S) (Laminate.partner A H) X z| ≤ A.weight := by
  unfold partners
  rw [Laminate.compartments A team inside,abs_prod,←Laminate.coverTotal A S]
  apply prod_le_prod (fun _ _ => abs_nonneg _)
  intro i hi
  obtain ⟨m,hm,rfl⟩ := mem_image.mp hi
  unfold Laminate.partner Laminate.coverWeight
  rw [Laminate.chosenAt A S _ _ m hm,Laminate.chosenAt A S _ _ m hm]
  exact m.coin (X.wrapY z.1) o.a (worldZ (X.wrapY z.1) R.beta z.2)

private theorem same (H : Cash W s μ L Q o C T R) (X : Coat T F) (hx : X.x=s) (hm : X.manifest)
    (healthy : Healthy (Pressure.temp s) (H.unionP team) X.V)
    (q : LogIndex c f) (member : badge S q ∈ team) (z : momentSpace X) :
    let Y:=X.wrapY z.1
    Y.farLog R o.a Q.table z.2 q = weightLog H q F Y z.2 := by
  let Y:=X.wrapY z.1
  have room : Room P S T Y.x := hx.symm ▸ H.laws.data.room
  have h : Healthy (Pressure.temp Y.x) (roadway T R Y.B Q.halo q) Y.V := by
    change Healthy (Pressure.temp X.x) (roadway T R (radiusB X.x) Q.halo q) X.V
    rw [hx]
    exact Finset.disjoint_of_subset_left (subset_biUnion_of_mem H.supportP member) healthy
  have e := Polar.leisure Y o.a R Q.table room hm Q.buys z.2 (worldZ Y R.beta z.2)
    (Vine.shine Y room hm R.beta z.2) q h
  exact Real.exp_injective (sub_left_inj.mp e)

private theorem finite (H : Cash W s μ L Q o C T R) (p : ℕ)
    (kept : ∀q, Kept H (H.supportP (identityLog q)) (Pavilion.mosaics H p q))
    (A : Team R) (team : Molecule S) (inside : A.signs S⊆team)
    (start : Start (team\A.signs S)) (u : Decors (team\A.signs S) M)
    (X : Coat T F) (hx : X.x=s) (hw : X.width=o.K) (hm : X.manifest)
    (healthy : Healthy (Pressure.temp s) (H.unionP team) X.V) :
    Measurable fun z => Mayer.planned H team u (Laminate.partner A H) X z -
      model H p team start u (Laminate.partner A H) X z := by
  have factors : Measurable (partners team (team\A.signs S) (Laminate.partner A H) X) := by
    unfold partners
    apply Finset.measurable_fun_prod
    intro i hi
    rw [Laminate.compartments A team inside] at hi
    exact (Laminate.partnerFit (H:=H) (j:=0) hi).1.along (V:=fun _=>X.V) X hx hw (momentSpace X)
      measurable_const measurable_fst measurable_snd
  let σ := team\A.signs S
  have eqn (i : ↥σ) : badge S (index start i)=i.val := Classical.choose_spec (start i.val i.property)
  have member (i : ↥σ) : badge S (index start i)∈team := eqn i ▸ (mem_sdiff.mp i.property).1
  have mK (q : LogIndex c f) (K : Port.Test T) (h : Kept H (H.supportP (identityLog q)) K) :
      Measurable (fun z : momentSpace X=> K F (X.wrapY z.1) z.2) :=
    h.borel (momentSpace X) F X hx hw (fun _=>X.V) Prod.fst Prod.snd measurable_const measurable_fst measurable_snd
  have h₁ i : Measurable (fun z : momentSpace X => exponent H (X.wrapY z.1) z.2 (i : ↥σ).val) := by
    rw [← eqn i]
    have he : (fun z : momentSpace X => exponent H (X.wrapY z.1) z.2 (badge S (index start i))) =
        fun z => weightLog H (index start i) F (X.wrapY z.1) z.2 :=
      funext (fun z => same H X hx hm healthy _ (member i) z)
    rw [he]
    exact mK _ _ (logTest H (index start i))
  have h₂ (i : ↥σ) : Measurable (fun z : momentSpace X => filed H p (X.wrapY z.1) z.2 (index start i)) := by
    have he : (fun z : momentSpace X => filed H p (X.wrapY z.1) z.2 (index start i)) =
        fun z => Pavilion.mosaics H p (index start i) F (X.wrapY z.1) z.2 := by
      funext z
      have joined := same H X hx hm healthy _ (member i) z
      generalize index start i=q at joined ⊢
      rcases q with q|(k|q)
      · exact joined
      · rfl
      · exact joined
    rw [he]
    exact mK _ _ (kept (index start i))
  apply Measurable.sub
  · apply factors.mul
    apply Finset.measurable_fun_prod
    intro i _
    exact ((h₁ i).pow_const _).div_const _
  · apply factors.mul
    apply Finset.measurable_fun_prod
    intro i _
    exact ((h₂ i).pow_const _).div_const _

theorem original (H : Cash W s μ L Q o C T R) (p : ℕ)
    (kept : ∀q, Kept H (H.supportP (identityLog q)) (Pavilion.mosaics H p q))
    (w : Miniature c f → ℝ) (A : Team R) (team : Molecule S) (inside : A.signs S⊆team)
    (start : Start (team\A.signs S)) (u : Decors (team\A.signs S) M)
    (X : Coat T F) (hx : X.x=s) (hw : X.width=o.K) (hm : X.manifest)
    (healthy : Healthy (Pressure.temp s) (H.unionP team) X.V)
    (paid : ∀ (z : momentSpace X) (k : Miniature c f),
      Healthy (Pressure.temp X.x) (sleeve S X.B Q.halo k) X.V →
      |Mayer.exponent H (X.wrapY z.1) z.2 (identityLog (letter k)) -
        Pavilion.mosaics H p (letter k) F (X.wrapY z.1) z.2| ≤ w k)
    (hwN : ∀ k, 0≤w k) :
    let error z := Mayer.planned H team u (Laminate.partner A H) X z -
      model H p team start u (Laminate.partner A H) X z
    Integrable error (moment X) ∧ (∫ z, |error z| ∂moment X) ≤
      A.weight*(book u (H.w+carry w) start-book u H.w start) := by
  let Δ := book u (H.w+carry w) start-book u H.w start
  have positive (q : LogIndex c f) : 0≤H.w q :=
    (abs_nonneg _).trans ((H.quotes F X hx hw hm).2.1 q 0).1
  have margin : 0≤Δ := by
    apply sub_nonneg.mpr
    apply Finset.prod_le_prod
    · intro i _
      exact div_nonneg (pow_nonneg (positive _) _) (Nat.cast_nonneg _)
    · intro i _
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      apply pow_le_pow_left₀ (positive _)
      apply le_add_of_nonneg_right
      rcases index start i with q|(k|q)
      · exact le_rfl
      · exact hwN _
      · exact le_rfl
  let err z := Mayer.planned H team u (Laminate.partner A H) X z -
    model H p team start u (Laminate.partner A H) X z
  have bound (z : momentSpace X) : |err z| ≤ A.weight*Δ :=
    (sampled H p w X z hx hw hm sdiff_subset start u (Laminate.partner A H) healthy (paid z)).trans
      (mul_le_mul_of_nonneg_right (cofactor H A team inside X z) margin)
  have measurable := finite H p kept A team inside start u X hx hw hm healthy
  have hi : Integrable err (moment X) :=
    (memLp_top_of_bound measurable.aestronglyMeasurable _ (Eventually.of_forall bound)).integrable le_top
  refine ⟨hi,(integral_mono hi.norm (integrable_const _) bound).trans_eq ?_⟩
  simp [Δ]

/-- The same original representative pays the full word, uniformly before its regulators. -/
theorem purchased (P : Teller G) (Q : ConnectedActivityE6.Target G P) (o : Target.Order G W)
    (L : Side) (D : Patch) (hD : D.Branches P.bind G) (χ : Chi) (p j : ℕ)
    (η : ℝ) (hη : 0<η) (v d : ℝ → ℝ)
    (hv : Rate G L (-(1/2)) v) (hd : Rate G L (-(1/2)) d) (hn : ∀ᶠ s in atTop, 0≤v s) :
    ∀ᶠ s in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (R : Rep G f)
      (μ C : ℝ) (H : Cash W s μ L Q o C T R), S.patch=D →
      ∃ w : Miniature c f → ℝ,
      Sales (radiusB s) Q.relative Q.ε (sleeve S (radiusB s) Q.halo) w (fun _ => 0)
        (betaF G s L ^ (-((p:ℝ)+1-η)/2)) ∧
      ∀ (A : Team R) (team : Molecule S), A.signs S ⊆ team →
        ∀ (start : Start (team\A.signs S)) (M : ℕ) (u : Decors (team\A.signs S) M)
        (F : Forest S.ratio) (X : Coat T F), X.x=s → X.width=o.K → X.manifest → X.χ=χ →
        Healthy (Pressure.temp s) (H.unionP team) X.V →
        let error z := Mayer.planned H team u (Laminate.partner A H) X z -
          model H p team start u (Laminate.partner A H) X z
        Integrable error (moment X) ∧ (∫ z, |error z| ∂moment X) ≤
          A.weight*(book u (H.w+carry w) start-book u H.w start) := by
  obtain ⟨_,_,_,pass⟩ := Pavilion.titular v d L o P Q p j 0 hv hd hn D hD χ
  filter_upwards [WilsonRetainedMiniatureRoot.original P Q o L D hD χ p j η hη v d hv hd hn,pass]
    with s rooted tests
  intro c f S T R μ C H patch
  obtain ⟨w,sales,_,point⟩ := rooted c f S T R μ C H patch
  refine ⟨w,sales,?_⟩
  intro A team inside start M u F X hx hw hm hχ healthy
  exact original H p (tests c f S T R μ C H patch).stamp w A team inside start u X hx hw hm healthy
    (fun z k hk => (point F (X.wrapY z.1) hx hw hm hχ z.2 k hk).2) sales.nonneg

end YM.Integration.WilsonRetainedDecoratedIntegral
end
