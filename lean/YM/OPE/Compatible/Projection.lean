import YM.OPE.Compatible.Primitive

/-!
# Reality and covariance of projection

Including the O(4) spin of the labels and their filtration.  Use on the
physical table.  It's not an assertion that the basis picked when coding
components has each individual vector invariant under rotations; the action
preserves each homogeneous *space*.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cov.Survey
open Function Set Filter Table MeasureTheory
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {L : Register G} {S : Table L} {R : S.Rotation}
variable {I J : Type} [Fintype I] [Fintype J] {d : ℕ}

variable (D : Prism (S:=S) (d:=d))
variable {P : DiffPlan S} {ρ : S.RealSpin} (H : R.Laws P ρ) (hT : S.Hierarchy)
  (hR : R.Oriented S)

include hT hR H

omit hT in
lemma shot_rotated {x : I → E4} (hx : sized D x) (p : I → S.Tag) (K g : Ortho) :
    R.act d g (shot R D x p K) = shot R D (Ortho.move g ∘ x) (R.label g ∘ p) (g*K) := by
  have he (e:D.probes) := kernel_move hR (beside p (labelSet R e.val K)) (lives D hx e K) g
  unfold shot
  rw [← H.group]; apply congr_arg; apply congr_arg
  ext1 e
  specialize he e; rw [beside_commutes,beside_commutes] at he
  have hf : Ortho.move g ∘ placements e.val K = placements e.val (g*K) := by
    ext1 i; exact (Ortho.move_mul g K _).symm
  have hh : R.label g ∘ labelSet R e.val K = labelSet R e.val (g*K) := by
    ext1 i; simp only [labelSet, Rotation.label, comp_apply]
    exact congr_arg (fun v:S.Field (e.val.letter i).fst => (⟨_,v⟩:S.Tag)) (H.group _ g K _).symm
  rw [hf,hh] at he
  exact he.symm

lemma raw_rotated {x : I → E4} (hx : sized D x) (p : I → S.Tag) (g : Ortho) :
    R.act d g (raw R D x p) = raw R D (Ortho.move g ∘ x) (R.label g ∘ p) := by
  let F := LinearMap.toContinuousLinearMap ((R.act d g).toLinearMap.restrictScalars ℝ)
  unfold raw
  trans ∫ K : Ortho, R.act d g (shot R D x p K) ∂angles
  · exact (F.integral_comp_comm (shot_integrable D H hT.smooth p hx)).symm
  simp_rw [shot_rotated D H hR hx p]
  exact (measurePreserving_mul_left angles g).integral_comp (Homeomorph.mulLeft g).measurableEmbedding _

lemma proj_rotated {x : I → E4} (hx : sized D x) (p : I → S.Tag) (g : Ortho) :
    R.act d g (projection R D ρ x p) = projection R D ρ (Ortho.move g ∘ x) (R.label g ∘ p) := by
  rw [projection,projection,map_smul,map_add, ← H.real,
    show conjugate ρ ∘ R.label g ∘ p = R.label g ∘ conjugate ρ ∘ p from
      funext fun i => conjugate_label_comm H g _,
    raw_rotated D H hT hR hx p g,raw_rotated D H hT hR hx _ g]

lemma shot_fix (p : S.Field d) (K : Ortho) : shot R D (sole 0) (sole ⟨d,p⟩) K = p := by
  let u := R.act d K⁻¹ p
  have hf : R.act d K u = p := by
    unfold u; rw [← H.group,mul_inv_cancel,H.fixes]
  have he (e : D.probes) : kernel S (beside (sole 0) (placements e.val K))
      (beside (sole ⟨d,p⟩) (labelSet R e.val K)) = MultipleContact.response S d e u := by
    have h := kernel_move hR (beside (sole ⟨d,u⟩) (S.classTokens ∘ e.val.letter))
      (bearing_clear e.val) K
    rw [beside_commutes, beside_commutes, kernel_center hT e.val u,
      show Ortho.move K ∘ sole (0:E4) = sole 0 from funext fun i => (Ortho.motion K).map_zero,
      show R.label K ∘ sole (⟨d,u⟩:S.Tag) = sole (⟨d,p⟩:S.Tag) by
        ext1 i; simp only [Function.comp_apply,sole,Rotation.label]; exact congr_arg (fun v:S.Field d => (⟨d,v⟩:S.Tag)) hf] at h
    rw [MultipleContact.response_self]; exact h
  unfold shot; simp_rw [he]; rw [D.fixes]; exact hf
lemma raw_fix (p : S.Field d) : raw R D (sole 0) (sole ⟨d,p⟩) = p := by
  unfold raw; simp only [shot_fix D H hT hR p,integral_const]; simp
lemma proj_fix (p : S.Field d) : projection R D ρ (sole 0) (sole ⟨d,p⟩) = p := by
  rw [projection, raw_fix D H hT hR p,
    show conjugate ρ ∘ sole (⟨d,p⟩:S.Tag) = sole (⟨d,S.conj ρ d p⟩:S.Tag) from rfl,
    raw_fix D H hT hR, S.reflect_star ρ, ← two_smul ℂ, smul_smul]; norm_num

omit hR
omit hT H in
lemma proj_conjugated (x : I → E4) (p : I → S.Tag) :
    S.conj ρ d (projection R D ρ x p) = projection R D ρ x (conjugate ρ ∘ p) := by
  rw [projection,projection,map_smulₛₗ,map_add,
    show conjugate ρ ∘ conjugate ρ ∘ p = p from funext fun i => conjugate_twice ρ _, S.reflect_star ρ]
  rw [add_comm, map_inv₀, map_ofNat]

-- order, rise, unit deletion expressed via exterior tests. No matching
-- required for those invariances.
omit H hT in
lemma shot_eq {x : I → E4} {y : J → E4} (p : I → S.Tag) (q : J → S.Tag)
    (K : Ortho)
    (h : ∀ (e : D.probes) w,
      kernel S (beside x (placements e.val K)) (beside p w) =
      kernel S (beside y (placements e.val K)) (beside q w)) :
    shot R D x p K = shot R D y q K := by
  unfold shot
  rw [funext (fun e:D.probes => h e (labelSet R e.val K))]

omit H in
lemma proj_eq {x : I → E4} {y : J → E4} (hx : sized D x) (hy : sized D y)
    (p : I → S.Tag) (q : J → S.Tag)
    (h : ∀ (K : Ortho) (e : D.probes) w,
      kernel S (beside x (placements e.val K)) (beside p w) =
      kernel S (beside y (placements e.val K)) (beside q w)) :
    projection R D ρ x p = projection R D ρ y q := by
  have HS : S.respects S := fun _ => le_rfl
  have hf (K : Ortho) : shot R D x (conjugate ρ ∘ p) K = shot R D y (conjugate ρ ∘ q) K := by
    apply shot_eq
    intro e w
    have hh (u : D.probes) (k : Fin u.val.n → S.Tag) : conjugate ρ ∘ conjugate ρ ∘ k = k :=
      funext fun i => conjugate_twice ρ _
    have hc := kernel_conj hT.laws.toSymmetric ρ ρ HS (beside p (conjugate ρ ∘ w)) (lives D hx e K)
    have hb := kernel_conj hT.laws.toSymmetric ρ ρ HS (beside q (conjugate ρ ∘ w)) (lives D hy e K)
    rw [beside_commutes,hh] at hc hb
    rw [hc,hb,h]
  unfold projection raw
  simp_rw [shot_eq D p q _ (h _), hf]

omit H in
lemma proj_perm {x : I → E4} (hx : sized D x) (p : I → S.Tag) (e : J ≃ I) :
    projection R D ρ (x ∘ e) (p ∘ e) = projection R D ρ x p := by
  apply proj_eq D hT (sized_perm D e hx) hx _ _
  intro K u w
  let f := e.sumCongr (Equiv.refl (Fin u.val.n))
  have he (Y : Type) (p : I → Y) (w : Fin u.val.n → Y) : beside (p ∘ e) w = beside p w ∘ f := by
    ext1 i; cases i <;> rfl
  rw [he,he]; exact kernel_order hT.laws.toSymmetric f _ (lives D hx u K)

omit H in
lemma proj_filter (h : P.Inclusions S) {x : I → E4} (hx : sized D x) (p : I → S.Tag)
    {n m : ℕ} (he : n ≤ m) (v : S.Field n) (j : I) :
    projection R D ρ x (update p j ⟨m,P.rise he v⟩) = projection R D ρ x (update p j ⟨n,v⟩) := by
  refine proj_eq D hT hx hx _ _ ?_
  intro K u w
  have hf (t : S.Tag) : beside (update p j t) w = update (beside p w) (.inl j) t := by
    ext1 i; cases i with
    | inl i=> by_cases hi : i=j <;> simp [hi]
    | inr i=> simp
  rw [hf,hf]
  have heq := kernel_filter P h hT.laws.toSymmetric (lives D hx u K) (beside p w) he v (Sum.inl j)
  convert heq using 1
  all_goals congr! 3

omit H in
lemma proj_unit {x : I → E4} (z : E4) (hx : sized D (beside (sole z) x)) (p : I → S.Tag) (n : ℕ) :
    projection R D ρ (beside (sole z) x) (beside (sole ⟨n,S.unit n⟩) p) = projection R D ρ x p := by
  apply proj_eq D hT hx (sizedBeside D hx)
  intro K u w
  let f := Equiv.sumAssoc Unit I (Fin u.val.n)
  have he (Y : Type) (v : Unit → Y) (p : I → Y) (w : Fin u.val.n → Y) :
      beside (beside v p) w = beside v (beside p w) ∘ f := by
    ext1 i; rcases i with (i|i)|i <;> rfl
  have ht : Injective (beside (sole z) (beside x (placements u.val K))) := by
    have h := lives D hx u K; rw [he] at h
    intro i j hij
    obtain ⟨i,rfl⟩ := f.surjective i; obtain ⟨j,rfl⟩ := f.surjective j
    exact congr_arg f (h hij)
  rw [he,he,kernel_order hT.laws.toSymmetric f _ ht]; exact kernel_unit S hT.laws (fun _ => le_rfl) _ _ _ _ ht

omit H in
lemma shot_straight {x : I → E4} (hx : sized D x) (n : I → ℕ) (K : Ortho) :
    ∃ q : MultilinearMap ℂ (fun i => S.Field (n i)) (S.Field d), ∀ v,
      q v = shot R D x (stockTag (d:=n) v) K := by
  let m := MultilinearMap.pi (fun e:D.probes =>
      withExterior S (placements e.val K) (labelSet R e.val K) n x)
  refine ⟨(R.act _ K).toLinearMap.compMultilinearMap (D.decode.compMultilinearMap m),?_⟩
  intro v
  unfold shot
  change R.act d K (D.decode _) = _
  apply congr_arg; apply congr_arg
  ext1 e
  change withExterior S (placements e.val K) (labelSet R e.val K) n x v = _
  rw [exterior_apply]
  let f := Equiv.sumComm (Fin e.val.n) I
  have he (Y : Type) (p : Fin e.val.n → Y) (q : I → Y) : beside p q = beside q p ∘ f := by
    ext1 i; cases i <;> rfl
  conv_lhs => rw [he,he S.Tag]
  exact kernel_order hT.laws.toSymmetric f _ (lives D hx e K)

lemma raw_straight {x : I → E4} (hx : sized D x) (n : I → ℕ) :
    ∃ q : MultilinearMap ℂ (fun i => S.Field (n i)) (S.Field d), ∀ v,
      q v = raw R D x (stockTag (d:=n) v) := by
  choose m hm using fun k => shot_straight (R:=R) D hT hx n k
  refine ⟨MultilinearMap.mk' (fun v : Slots S n => raw R D x (stockTag v)) ?_ ?_, fun _ => rfl⟩
  · intro v i a b
    unfold raw
    have hh (K : Ortho) := (m K).map_update_add v i a b
    simp_rw [← hm, hh]
    exact integral_add (by simp_rw [hm]; exact shot_integrable D H hT.smooth _ hx) (by
      simp_rw [hm]; exact shot_integrable D H hT.smooth _ hx)
  intro v i c a
  unfold raw
  have hh (K : Ortho) := (m K).map_update_smul v i c a
  simp_rw [← hm, hh]; exact integral_smul ..

lemma proj_straight {x : I → E4} (hx : sized D x) (n : I → ℕ) :
    ∃ q : MultilinearMap ℂ (fun i => S.Field (n i)) (S.Field d), ∀ v,
      q v = projection R D ρ x (stockTag (d:=n) v) := by
  obtain ⟨m,hm⟩ := raw_straight D H hT hx n
  let b (v : Slots S n) : Slots S n := fun i => S.conj ρ (n i) (v i)
  have he (v) : conjugate ρ ∘ stockTag v = stockTag (b v) := rfl
  have hu (v i a) : b (update v i a) = update (b v) i (S.conj ρ (n i) a) := by
    ext1 j; by_cases h : i=j
    · subst j; simp only [b,update_self]
    simp [b, Ne.symm h]
  let M : MultilinearMap ℂ (fun i => S.Field (n i)) (S.Field d) := MultilinearMap.mk'
    (fun v => S.conj ρ d (m (b v))) (fun v i a a' => by simp_rw [hu,map_add,m.map_update_add,map_add])
    (fun v i c a => by simp_rw [hu,map_smulₛₗ,m.map_update_smul,map_smulₛₗ]; simp)
  refine ⟨(2:ℂ)⁻¹ • (m + M),fun v => ?_⟩
  simp only [projection, he,← hm]; rfl
end YM.OPE.Cov.Survey
