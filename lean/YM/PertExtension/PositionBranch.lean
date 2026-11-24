import YM.PertExtension.PositionSolve

/-! Exact implicit solve of the same finite-position normalization equations
as the formal recursion, around a regular free reading. Also stability of
regularity. Arrays supplied to this module must evaluate the indicated
position-space products on actual input frames for physical use. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace YM.PertExtension.Position.TestSystem
open Set Function Filter PowerSeries LinearMap
open scoped Topology ContDiff BigOperators Classical
variable {J P : Type*} [Fintype J]{arity : P→ℕ}
variable (D : TestSystem J P arity)

abbrev Parameter := Questionnaire (J:=J) (arity:=arity) D.tests→ℝ

def solver (p:D.Parameter × D.Z) : D.Parameter × D.Z :=
  ⟨p.1,D.lieResult p.1 p.2⟩

lemma smooth_solve : ContDiff ℝ ω D.solver := by
  apply contDiff_fst.prodMk
  apply D.select.toContinuousLinearMap.contDiff.comp
  apply contDiff_pi.mpr
  intro v
  unfold insert; apply ContDiff.sum; intro w hw
  let e : (D.Parameter × D.Z) → ℝ := fun p=>p.1 ⟨v.fst,w⟩
  let q : D.Parameter →L[ℝ] ℝ := ContinuousLinearMap.proj ⟨v.fst,w⟩
  apply ContDiff.mul (show ContDiff ℝ ω e from q.contDiff.comp contDiff_fst)
  apply contDiff_prod; intro i hi
  exact contDiff_const.add ((ContinuousLinearMap.proj _).contDiff.comp
    ((ContinuousLinearMap.proj _).contDiff.comp (D.Z.subtypeL.contDiff.comp contDiff_snd)))

lemma solve_fderiv (a : Mark J arity→ℝ) (z:D.Z) :
    fderiv ℝ D.solver (a ∘ markIn D.tests,0) (0,z)=(0,D.inspect a z) := by
  let f := fderiv ℝ D.solver (a ∘ markIn D.tests,0)
  let L : D.Z →L[ℝ] D.Parameter × D.Z := ContinuousLinearMap.inr ℝ _ _
  have h : HasFDerivAt (fun u=>D.solver ((a ∘ markIn D.tests, (0:D.Z)) + L u)) (f.comp L) 0 := by
    have he := (D.smooth_solve.differentiable (by simp)) (a ∘ markIn D.tests,0) |>.hasFDerivAt
    have hl : HasFDerivAt (fun u=>(a ∘ markIn D.tests, (0:D.Z)) + L u) L 0 := by convert L.hasFDerivAt.const_add _
    exact ((by simpa using he) : HasFDerivAt D.solver f ((a ∘ markIn D.tests,0)+L 0)).comp (g':=f) (0:D.Z) hl
  simp [L] at h
  have h₂ := h.snd.unique (show HasFDerivAt (D.lieResult (a ∘ markIn _)) _ _ from ((D.lieResult_contDiff _).differentiable (by simp) _).hasFDerivAt)
  have h₁ := h.fst.unique (hasFDerivAt_const _ _)
  exact Prod.ext (DFunLike.congr_fun h₁ z) (DFunLike.congr_fun h₂ z)

lemma solve_fst (a) (p:D.Parameter × D.Z) : (fderiv ℝ D.solver (a,0) p).1 = p.1 := by
  let L := ContinuousLinearMap.fst ℝ D.Parameter D.Z
  have h₁ :=
    ((L.hasFDerivAt (x:=(a,0))).unique (((D.smooth_solve.differentiable (by simp) _).hasFDerivAt)).fst).symm
  exact DFunLike.congr_fun h₁ p

lemma eventually_fullrank (a : Mark J arity→ℝ)(h : D.Regular a) :
    ∀ᶠ p : D.Parameter × D.Z in 𝓝 (a ∘ markIn D.tests,0), Bijective (fderiv ℝ D.solver p) := by
  have he : Bijective (fderiv ℝ D.solver (a ∘ markIn D.tests,0)) :=
     ⟨fun p q hp => by
         have he := D.solve_fst (a ∘ markIn D.tests)
         have h₁ : p.1=q.1:=(he p).symm.trans ((congr_arg Prod.fst hp).trans (he q))
         have ht := congr_arg (fun x:D.Parameter×D.Z=> x- (fderiv ℝ D.solver (a ∘ markIn D.tests,0)) (p.1,0)) hp
         rw [←map_sub,←map_sub,show p-(p.1,0)=(0,p.2) by ext <;> simp,h₁,show q-(q.1,0)=(0,q.2) by ext <;> simp,D.solve_fderiv,D.solve_fderiv] at ht
         exact Prod.ext h₁ (h.rank.injective (congr_arg Prod.snd ht)), fun y=> by
         let f := fderiv ℝ D.solver (a ∘ markIn D.tests,0)
         obtain ⟨z,hz⟩:= h.rank.surjective (y.2-(f (y.1,0)).2)
         refine ⟨(y.1,0)+(0,z),?_⟩
         rw [map_add,D.solve_fderiv]; exact Prod.ext (by simp [D.solve_fst]) (by change (f _).2+(D.inspect a) z=y.2;rw [hz]; abel)⟩
  exact (D.smooth_solve.continuous_fderiv (by simp)).continuousAt.eventually
    (Units.isOpen.mem_nhds (ContinuousLinearMap.isUnit_iff_bijective.mpr he)) |>.mono fun _ h=>ContinuousLinearMap.isUnit_iff_bijective.mp h

/-- A convenient local branch. At the regular point it satisfies the
equations at all raw data sufficiently near the displayed leading data. -/
def branch (a : Mark J arity→ℝ)(p : D.Parameter): D.Z :=
  let L:=fderiv ℝ D.solver (a ∘ markIn D.tests,0)
  if h : Bijective L then
    let S : (D.Parameter×D.Z) ≃L[ℝ] (D.Parameter×D.Z):= (LinearEquiv.ofBijective L.toLinearMap h).toContinuousLinearEquiv
    (HasStrictFDerivAt.localInverse D.solver S (a ∘ markIn D.tests,0)
        (D.smooth_solve.hasStrictFDerivAt (by simp)) (p,D.target)).2
  else 0

theorem tends (a) (h : D.Regular a) : Tendsto (fun x=>(x,D.branch a x)) (𝓝 (a ∘ markIn D.tests)) (𝓝 (a ∘ markIn D.tests,0)) := by
  have hS := D.eventually_fullrank a h |>.self_of_nhds
  simp only [branch,dif_pos hS]
  have ht : D.solver (a ∘ markIn D.tests,0)=(a ∘ markIn D.tests,D.target) := Prod.ext rfl (by simpa [solver,lieResult] using h.fits)
  let S := LinearEquiv.ofBijective (fderiv ℝ D.solver (a ∘ markIn D.tests,0)).toLinearMap hS
  have hr : HasStrictFDerivAt D.solver S.toContinuousLinearEquiv.toContinuousLinearMap _:= D.smooth_solve.hasStrictFDerivAt (by simp)
  have HH := HasStrictFDerivAt.localInverse_tendsto (f':=S.toContinuousLinearEquiv) hr
  apply tendsto_id.prodMk_nhds
  apply (continuousAt_snd.tendsto.comp HH).comp
  rw [ht]; exact tendsto_id.prodMk_nhds tendsto_const_nhds

theorem solves (a) (h : D.Regular a) : ∀ᶠ x in 𝓝 (a ∘ markIn D.tests),D.lieResult x (D.branch a x)= D.target := by
  have hS := D.eventually_fullrank a h |>.self_of_nhds
  simp only [branch,dif_pos hS]
  let L := fderiv ℝ D.solver (a ∘ markIn D.tests,0)
  have he := D.smooth_solve.hasStrictFDerivAt (x:=(a ∘ markIn D.tests, 0)) (by simp)
  let S : (D.Parameter×D.Z) ≃L[ℝ] (D.Parameter×D.Z) := (LinearEquiv.ofBijective L.toLinearMap hS).toContinuousLinearEquiv
  let B := he.localInverse D.solver S _
  have ht : D.solver (a ∘ markIn D.tests,0)=(a ∘ markIn D.tests,D.target) := Prod.ext rfl (by simpa [solver,lieResult] using h.fits)
  have hp:= he.eventually_right_inverse (f':=S)
  rw [ht] at hp
  filter_upwards [(tendsto_id.prodMk_nhds tendsto_const_nhds).eventually hp] with i hi
  obtain h₁:= congr_arg Prod.fst hi; change (B (i,D.target)).1=i at h₁
  change D.lieResult i (B (i,D.target)).2=D.target
  have := congr_arg Prod.snd hi
  change D.lieResult (B (i,D.target)).1 (B (i,D.target)).2=D.target at this
  rw [h₁] at this; exact this

end YM.PertExtension.Position.TestSystem
