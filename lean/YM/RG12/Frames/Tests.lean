import YM.RG12.Frames.Motions
import YM.RG12.Frames.Across

/-! # Sufficient physical march data on comparable-radius measurements -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Frames
open Function Finset Filter
open scoped Topology BigOperators
variable {d : ℕ} {V : Grade d → Type} [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℂ (V i)]
variable {F E : Type} [AddCommGroup F] [Module ℂ F]
variable {s t u : ℕ → ℝ} {Y : ℕ → Col V →ₗ[ℂ] F} {P : Col V ≃ₗ[ℂ] F}
  {A J : ℕ → Col V ≃ₗ[ℂ] Col V} {g : ℕ → F → ℝ} {K : ℝ} {p b n₀ : ℕ}
  [FiniteDimensional ℂ (Col V)]

/-- The test cost g is typically from reflected 2-point evaluations on the same geometry for
all columns (see later files). Permits testing it in *any* units making this ratio comparison
meaningful. Implement `Y` on PHYSICAL independent labels with the corresponding engineering
normalization AT THIS SCALE. Don't assume the columns a basis. Coercivity can be supplied from
just low-order data at this scale (adapters to Tests below/later), without a full-distance
WilsonX matching.

J shears before comparing next measurements at current scale to those at next scale. The
shear has to act trivially at the SAME grade; can use the identity with no effect. Only
consecutive scales are compared, not common detector lists against the IR.
-/
structure Consecutive (s t u : ℕ → ℝ) (Y : ℕ → Col V →ₗ[ℂ] F) (P : Col V ≃ₗ[ℂ] F)
    (R : ℕ → F → ℝ) (J : ℕ → Col V ≃ₗ[ℂ] Col V)
    (K : ℝ) (p b n₀ : ℕ) : Prop where
  spacing i : n₀ ≤ i → 0 < t i ∧ 1 ≤ u i ∧ t (i+1) = t i / u i
  times i : n₀ ≤ i → K ≤ s i ∧ s i + 1 ≤ s (i+1) ∧ s (i+1)/s i ≤ s i
  compatibility i : n₀ ≤ i → triangular V (P.symm.toLinearMap.comp (Y i))
  charges i : n₀ ≤ i → Tests (R i ∘ Y i) K
  shears i : n₀ ≤ i → triangular V (J i).toLinearMap ∧
    ∀ j : Grade d, ∀ x : V j, block V (J i).toLinearMap j j x = x
  affordable i : n₀ ≤ i → ∀ x, ‖J i x‖ ≤ s i^b * ‖x‖ ∧ ‖(J i).symm x‖ ≤ s i^b * ‖x‖
  at_step i : n₀ ≤ i → ∀ x : Col V,
    let r := s (i+1)/s i
    R i (Y (i+1) (dilate (u i) (J i x))) ≤ r^p * R (i+1) (Y (i+1) x) ∧
      R (i+1) (Y (i+1) x) ≤ r^p * R i (Y (i+1) (dilate (u i) (J i x)))

variable {R : ℕ → F → ℝ}

theorem enough (h : Consecutive s t u Y P R J K p b n₀) :
    ∃ Z : ℕ → Col V ≃ₗ[ℂ] F, (∀ i, n₀ ≤ i → (Z i).toLinearMap = Y i) ∧
      ∃ A : ℕ → Col V ≃ₗ[ℂ] Col V,
        Moves s t u Z P A (fun i=> compress (R i ∘ Y i)) K p (p+b+4) n₀ := by
  have hi (i : ℕ) : ∃ Z : Col V ≃ₗ[ℂ] F, n₀ ≤ i → Z.toLinearMap=Y i:=by
    by_cases he:n₀ ≤ i
    · have hQ:= h.charges i he
      have hz: R i 0=0:= by simpa [Function.comp] using hQ.zero
      let U := P.symm.toLinearMap.comp (Y i); have hp: Injective (Y i):= LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr (fun x hx=> norm_le_zero_iff.mp (by
        have htF:= hQ.lower x; simpa [comp,hx,hz] using htF)))
      refine ⟨LinearEquiv.ofBijective (Y i) ⟨hp,?_⟩,fun _=>rfl⟩
      have hs : Surjective U := LinearMap.injective_iff_surjective.mp (P.symm.injective.comp hp : Injective U)
      intro x; obtain ⟨y,hy⟩:= hs (P.symm x); exact ⟨y,P.symm.injective hy⟩
    exact ⟨P,fun hi=>(he hi).elim⟩
  choose Z hZ using hi; refine ⟨Z,hZ,?_⟩
  have he (i : ℕ) : ∃ A: Col V ≃ₗ[ℂ] Col V, n₀ ≤ i → ∀ x, A x=(Z i).symm (Z (i+1) (dilate (u i) x)):=by
    by_cases he : n₀ ≤ i
    · have hu:= zero_lt_one.trans_le (h.spacing i he).2.1
      let D: Col V≃ₗ[ℂ]Col V:= LinearEquiv.ofLinear (dilate (u i)) (dilate (u i)⁻¹) (by apply LinearMap.ext; intro x; exact scale_cancel' hu.ne' x) (by apply LinearMap.ext; intro x; exact scale_cancel hu.ne' x)
      exact ⟨D.trans ((Z (i+1)).trans (Z i).symm), fun _ _=>rfl⟩
    exact ⟨LinearEquiv.refl _ _,fun hi=>(he hi).elim⟩
  choose A hA using he
  have hP (i : ℕ) (he : n₀ ≤ i) : triangular V (P.symm.toLinearMap.comp (Z i).toLinearMap):= by rw [hZ i he]; exact h.compatibility i he
  have hp(i : ℕ)(he : n₀ ≤ i): triangular V (A i).toLinearMap:=by
    have hx := (tri_dilate (V:=V) (u i))
    have hL:= (hP (i+1) (he.trans i.le_succ)).comp hx
    let W:= (Z i).trans P.symm; have hW : triangular V W.symm.toLinearMap:=triangular.inv (A:=W) (hP i he)
    have hr:= hW.comp hL; intro j k hk x; unfold block; rw [LinearEquiv.coe_toLinearMap,hA i he];
    specialize hr j k hk x; change (Z i).symm (P (P.symm (Z _ _))) _ = 0 at hr; rwa [P.apply_symm_apply] at hr
  have hsum(i : ℕ)(he : n₀ ≤ i) : Compared (A i) (J i) (R i ∘ Y i) (R (i+1) ∘ Y (i+1)) K (s i) (s (i+1)/s i) p b:=by
    have hf:= he.trans i.le_succ;
    refine ⟨h.charges i he,h.charges _ hf,hp i he,h.shears i he,h.affordable i he,fun x=>?_⟩
    have hx(y): Y i (A i y)= Y (i+1) (dilate (u i) y):= by rw [hA i he, ← hZ i he,← hZ (i+1) hf]; exact (Z i).apply_symm_apply _
    unfold Function.comp; rw [hx]; exact h.at_step i he x
  have hpos i (he:n₀ ≤ i):1 ≤ s i:= (h.charges i he).legal.trans (h.times i he).1
  have hT i (he:n₀ ≤ i):1 ≤ s (i+1)/s i:=(one_le_div (zero_lt_one.trans_le (hpos i he))).mpr ((le_add_of_nonneg_right zero_le_one).trans (h.times i he).2.1)
  have hz i (he:n₀ ≤ i):= TestedStep (hsum i he) (h.times i he).1 (hT i he) (h.times i he).2.2
  refine ⟨A,h.spacing,fun i he=> ⟨hpos i he,(h.times i he).2.1⟩,fun i he=> (hz i he).1, fun i he=> (hz i he).2, fun i he x=>?_, hP _ le_rfl⟩
  rw [hA i he, (Z i).apply_symm_apply, scale_cancel' (ne_of_gt (zero_lt_one.trans_le (h.spacing i he).2.1))]
end YM.RG12.Frames
