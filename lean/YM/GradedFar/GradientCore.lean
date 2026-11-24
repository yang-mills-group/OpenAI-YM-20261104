import YM.GradedFar.Sunlight
-- adapted from YM/Integration/WilsonMacroscopicRelativeGradient to allow non-origin operands
-- budget and hypotheses unchanged. Needed for (M.4)-continuum derivative proof.

/-! Differentiate the actual joined physical moment with the exterior
positions fixed. Use its original finite naming, including a nonsorted or
independently supplied spectator roster. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Window
open Function Filter Finset Set Extraction Table Spec Next.Rank OPE OPE.Orbits OPE.Nesting PhysMS
open scoped Topology BigOperators ContDiff Classical
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {V : Table C.book} {n : ℕ} {E : Type} [Fintype E]

private abbrev N (n : ℕ) (E : Type) [Fintype E] := Fintype.card (Fin n ⊕ E)
private abbrev name (n : ℕ) (E : Type) [Fintype E] := runNames (Fin n ⊕ E)

private def enter {m : ℕ} (ξ : Fin m ≃ Fin n ⊕ E) : Points n →L[ℝ] Points m :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _:Fin m=>E4)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j : Fin m=>Sum.elim (fun i : Fin n=>PiLp.proj (𝕜:=ℝ) 2 (fun _:Fin n=>E4) i) (fun _:E=>(0:Points n→L[ℝ]E4)) (ξ j))

omit [Fintype E] in
private theorem enter_at {m : ℕ} (ξ : Fin m ≃ Fin n ⊕ E) (x : Points n) (j : Fin m) :
    enter ξ x j = beside x.ofLp (fun _:E=>0) (ξ j) := by
  change (Sum.elim (fun i : Fin n=>PiLp.proj (𝕜:=ℝ) 2 (fun _:Fin n=>E4) i) (fun _:E=>(0:Points n→L[ℝ]E4)) (ξ j)) x=_
  cases h:ξ j with | inl i=>rfl | inr j=>rfl

omit [Fintype E] in
private theorem enter_axis {m : ℕ} (ξ : Fin m ≃ Fin n ⊕ E) (i : Fin n) (a : Axis) : enter ξ (Points.direction i a) = Points.direction (ξ.symm (.inl i)) a := by
  apply PiLp.ext;intro j
  rw [enter_at]
  by_cases hj : j=ξ.symm (.inl i)
  · subst j;simp only [Equiv.apply_symm_apply,beside,Sum.elim_inl,Points.direction,PiLp.single_eq_same]
  have h0 : ξ j ≠ .inl i := fun he=>hj (ξ.apply_eq_iff_eq_symm_apply.mp he)
  cases h:ξ j with
  | inl k =>
    have ne : k≠i := fun eq=>h0 (h.trans (congrArg Sum.inl eq))
    simp only [beside,Sum.elim_inl,Points.direction,PiLp.single_apply,if_neg hj,if_neg ne]
  | inr k =>simp only [beside,Sum.elim_inr,Points.direction,PiLp.single_apply,if_neg hj]

private def place (o:E4) (r : ℝ) (y : E→E4) (x : Points n) := points ((beside (sites o r x) y) ∘ name n E)
private theorem place_diff (o:E4) (r : ℝ) (y : E→E4) (x : Points n) : HasFDerivAt (place o r y) (r • enter (name n E)) x := by
  let tail := points ((beside (fun _:Fin n=>o) y) ∘ name n E)
  have he : place o r y = fun z : Points n=>(r • enter (name n E)) z+tail := by
    funext z;apply PiLp.ext;intro j
    change beside (sites o r z) y (name n E j)=r • (enter (name n E) z j)+beside (fun _:Fin n=>o) y (name n E j)
    rw [enter_at]
    cases h:name n E j with | inl i=>simp [beside,sites,add_comm] | inr a=>simp [beside]
  rw [he];exact (r • enter (name n E)).hasFDerivAt.add_const tail

private theorem pull (o:E4) (r : ℝ) (y : E→E4) (x : Points n) (row : Points (N n E)→ℂ)
    (sm : DifferentiableAt ℝ row (place o r y x)) (i : Fin n) (a : Axis) :
    Points.gradient i a (row ∘ place o r y) x = r • Points.gradient ((name n E).symm (.inl i)) a row (place o r y x) := by
  letI : ContinuousSMul ℝ (Points n) := IsBoundedSMul.continuousSMul
  have dg : HasFDerivAt (row ∘ place o r y) ((fderiv ℝ row (place o r y x)).comp (r • enter (name n E))) x := sm.hasFDerivAt.comp x (place_diff o r y x)
  change fderiv ℝ (row ∘ place o r y) x (Points.direction i a) = _
  rw [dg.fderiv]
  change fderiv ℝ row (place o r y x) (r • (enter (name n E) (Points.direction i a))) = _
  rw [enter_axis,map_smul];rfl

private def combined (v : Fin n→V.Tag) (w : E→V.Tag) : Fin (N n E)→V.Tag := beside v w ∘ name n E
private theorem physical (F : Spec.Final C f V) (q : Viewers F) (v : Fin n→V.Tag) (w : E→V.Tag)
    (o:E4) (r : ℝ) (y : E→E4) (x : Points n) : whole (spectator F q) (sites o r x) (voices v) y (voices w) =
      V.useAt (spectator F q) (place o r y x) (combined v w) := by
  change V.useAt (spectator F q) _ (fun l=> tags (stages (voices v) (voices w)) (name n E l)) = _
  apply congrArg (V.useAt (spectator F q) (place o r y x));funext l
  change tags (stages (voices v) (voices w)) (name n E l) = beside v w (name n E l)
  cases h:name n E l with | inl i=>rfl | inr a=>rfl

theorem smooth (F : Spec.Final C f V) (q : Viewers F) (v : Fin n→V.Tag) (w : E→V.Tag)
    (o:E4) (r : ℝ) (y : E→E4) {x : Points n} (hc : Injective (beside (sites o r x) y)) :
    DifferentiableAt ℝ (fun z : Points n=>whole (spectator F q) (sites o r z) (voices v) y (voices w)) x := by
  let row (z : Points (N n E)) := V.useAt (spectator F q) z (combined v w)
  have safe : place o r y x∈conf _ := runs_conf.mpr hc
  have sm : DifferentiableAt ℝ row (place o r y x) :=
    ((V.class_smooth _ (spectate F q).smooth (combined v w)).contDiffAt ((conf_open _).mem_nhds safe)).differentiableAt (by simp)
  rw [show (fun z : Points n=>whole (spectator F q) (sites o r z) (voices v) y (voices w))=row ∘ place o r y from funext (physical F q v w o r y)]
  exact sm.comp x (place_diff o r y x).differentiableAt

/-- The `r` multiplies precisely the differentiated inner field; the
exterior field and all its positions are fixed in physical coordinates. -/
theorem at_slot (F : Spec.Final C f V) (q : Viewers F) (v : Fin n→V.Tag) (w : E→V.Tag)
    (o:E4) (r : ℝ) (y : E→E4) {x : Points n} (hc : Injective (beside (sites o r x) y)) (i : Fin n) (a : Axis) :
    Points.gradient i a (fun z : Points n=>whole (spectator F q) (sites o r z) (voices v) y (voices w)) x =
    r • whole (spectator F q) (sites o r x)
      (voices (Function.update v i ⟨(v i).1+1,F.sector.derivatives.deriv (v i).1 a (v i).2⟩)) y (voices w) := by
  let j := (name n E).symm (.inl i)
  let rhs : V.Tag := ⟨(v i).1+1,F.sector.derivatives.deriv (v i).1 a (v i).2⟩
  let tags := combined v w
  let row (z : Points (N n E)) := V.useAt (spectator F q) z tags
  have atj : tags j=v i := by change beside v w (name n E ((name n E).symm (.inl i)))=v i;rw [Equiv.apply_symm_apply];rfl
  have updated : update tags j rhs=combined (update v i rhs) w := by
    funext l;by_cases hl:l=j
    · subst l;rw [update_self]; change rhs=beside (update v i rhs) w (name n E ((name n E).symm (.inl i)));rw [Equiv.apply_symm_apply];exact (update_self i rhs v).symm
    have ne : name n E l ≠ Sum.inl i := fun h=>hl ((name n E).apply_eq_iff_eq_symm_apply.mp h)
    rw [update_of_ne hl]
    change beside v w (name n E l) = beside (update v i rhs) w (name n E l)
    cases h:name n E l with
    | inl k => exact (update_of_ne (fun ek=>ne (h.trans (congrArg Sum.inl ek))) rhs v).symm
    | inr k =>rfl
  have safe : place o r y x ∈ conf (N n E) := runs_conf.mpr hc
  have dd := F.sector.derivatives.derivative_slot (spectate_evolution F q) (spectate F q).laws.toSymmetric
    (spectate F q).smooth safe j tags (v i).2 a
  rw [show update tags j (⟨(v i).1,(v i).2⟩ : V.Tag)=tags from atj ▸ update_eq_self ..] at dd
  have sm : DifferentiableAt ℝ row (place o r y x) :=
    ((V.class_smooth _ (spectate F q).smooth tags).contDiffAt ((conf_open _).mem_nhds safe)).differentiableAt (by simp)
  have source : (fun z : Points n=>whole (spectator F q) (sites o r z) (voices v) y (voices w))=row ∘ place o r y := funext (physical F q v w o r y)
  rw [source,physical F q (update v i rhs) w o r y x]
  rw [pull o r y x row sm i a]
  apply congrArg (fun c : ℂ=>r • c)
  change Points.gradient j a row (place o r y x) = V.useAt (spectator F q) (place o r y x) (combined (update v i rhs) w)
  change V.useAt (spectator F q) (place o r y x) (update tags j rhs)=Points.gradient j a row (place o r y x) at dd
  rw [updated] at dd; exact dd.symm

end YM.Integration.GradedFar.Window
