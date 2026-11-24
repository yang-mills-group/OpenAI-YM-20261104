import YM.Next.PHASE.Roots

/-!
# Heterogeneous two-scale roots for training contact comparisons

Treat any central difference as a whole unit in that cell. When extending over all possible arities, exterior weight bounds may not be homogeneous; expose the individual Single roots (adapted from YM/Next/PHASE/Roots.lean). This will serve the two-tier pricing on confirmed cutoff geometries before invoking derivatives/interpolation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Costar
open Function Set Filter MeasureTheory Extraction Extraction.Spin Cells Lattice Wilson Next.Phase
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{N p : ℕ}
variable {T Y : Tiling (C.side N p)} {ι κ : Type*} [Fintype ι] [Fintype κ]

private lemma copy_prod (c : T.Cell) (F : ι → Config G (C.side N p) → ℂ) (U : Config G (C.side N p)) :
    T.copy c (fun x => ∏ i, F i x) U = ∏ i, T.copy c (F i) U := by
  classical
  by_cases h : T.hand c <;> simp [Tiling.copy,h,star_prod]

/-- Price the root of an entire exterior group, not a product of coarse-cell
one-field root assumptions. Even the empty group may be used. -/
lemma exterior_pay (H : C.Makes) (yh : Y.kind=.link) (th : T.kind=.link) (offset : Y.base=T.base)
    (tiles : Y.side.val ∣ T.side.val) {b : ℕ} (hb : b ≤ N) (hf : span C.S hb p ∣ Y.side.val)
    (v : κ → C.book.Token) (x : κ → Site (C.side N p)) (o : T.Cell) (hx : ∀ i, T.which (x i) = o)
    (margins : ∀ i, Next.Phase.Inside Y (3 * span C.S hb p) (x i))
    (sep : ∀ i j, i ≠ j → Y.side.val < separation (x i) (x j))
    (B : κ → ℝ) (hB : ∀ i,0 ≤ B i) (funds : ∀ i, Single C (v i) (B i) b N p) :
    ∃ F : Config G (C.side N p) → ℂ, T.copy o F = (fun U => ∏ i, C.seen (v i) (x i) U) ∧
      Interior (T.chamber 0) F ∧ T.rootTest (C.beta N p) F ≤  ∏ i, B i := by
  classical
  let M := 3 * span C.S hb p
  choose y hy using fun i => T.pointed o (x i)
  let f : Frame := ((way T o).1⁻¹, (way T o).2)
  let w i := token C.book (v i) f
  let g i := C.seen (w i) (y i)
  let F := fun U => ∏ i, g i U
  have Hc (i) : Interior (T.chamber 0) (g i) := by
    have hc : Next.Phase.Inside T M (x i) := shared_inside _ _ offset yh th tiles _ _ (margins i)
    unfold Next.Phase.Inside at hc
    rw [hx] at hc
    have hm : y i ∈ T.margin 0 M := (T.reflected_margin _ _ _).mpr ((hy i).symm ▸ hc)
    refine Around.figure H _ (w i) M (y i) hm ?_
    intro z hz a
    have hh : (z a).natAbs < span C.S hb p := ((funds i).2 0 f).2.choose_spec z hz a
    unfold M; omega
  have Hw (i) : C.ref (w i).1 ≤ N := ((funds i).2 0 f).1.choose_spec.1
  have Ht i : T.copy o (g i) = C.seen (v i) (x i) := by
    change T.copy o (C.seen (w i) (y i)) = _
    rw [Extraction.Spin.uses H T o (y i) (w i) (Hw i),hy,
      show token C.book (w i) (way T o) = v i from isotropy ..]
  refine ⟨F,funext (fun U => ?_),Interior.combines _ _ (fun i _ => Hc i),?_⟩
  · simp_rw [F,copy_prod,Ht]
  let z : T.Cell × κ → Site (C.side N p) := fun i => T.copyMap i.1 (y i.2)
  let W (i : T.Cell × κ) := token C.book (w i.2) (way T i.1)
  let c (i : T.Cell × κ) := Y.which (z i)
  have Hm (i) : Next.Phase.Inside Y M (z i) := by
    have hi : Next.Phase.Inside Y M (T.copyMap o (y i.2)) := by rw [hy]; exact margins _
    exact (inside_reflected T Y offset tiles th yh i.1 _ _).mpr ((inside_reflected T Y offset tiles th yh o _ _).mp hi)
  have hc : Injective c := by
    rintro ⟨s,i⟩ ⟨t,j⟩ he
    have h : T.which (z (s,i)) = T.which (z (t,j)) := shared_cell T Y offset tiles he
    have heq k i : T.which (z (k,i))=k := by
      refine T.which_chamber (T.enumerate k ((T.reflected_chamber _ o).mpr ?_))
      rw [hy, ← hx i]; exact (shared_inside T Y offset yh th tiles M _ (margins i)).1
    rw [heq,heq] at h
    subst t; congr 1; by_contra H
    have hg := (Hm (s,i)).1
    have hh := Y.extent hg (x := z (s,i)) (y := z (s,j)) (show z (s,j) ∈ Y.chamber (c (s,i)) from he ▸ (Hm (s,j)).1)
    have ht : separation (z (s,i)) (z (s,j)) = separation (x i) (x j) := by
      dsimp only [z]
      rw [separation_copy, ← separation_copy T o,hy,hy]
    exact (sep i j H).not_ge (ht ▸ hh)
  have hi (i : T.Cell × κ) : Around.imageBudget (C := C) (fun _ : Fin 1 => W i) (B i.2) b N p :=
    ((funds i.2).moves f).moves (way T i.1)
  choose D hD h₁ h₂ using fun i : T.Cell × κ =>
    Lease.alive H (0 : Fin 1) (z i) (hi i) hb hf (z := c i) (Hm i)
  have he (U : Config G (C.side N p)) :
      T.fullAt (fun _ => F) U = ∏ i : T.Cell × κ, Y.copy (c i) (D i) U := by
    unfold Tiling.fullAt F
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    rw [copy_prod]; apply Finset.prod_congr rfl; intro i _
    rw [hD]
    exact congrFun (Extraction.Spin.uses H T k (y i) (w i) (Hw i)) U
  apply le_of_pow_le_pow_left₀ (T.cells_positive.ne') (Finset.prod_nonneg (fun i _=>hB i))
  rw [T.powering]
  change ‖moment _ (T.fullAt _)‖ ≤ _
  rw [show T.fullAt (fun _ => F)=_ from funext he]
  apply le_trans ((Y.planted (seamless H ..) _ hc D h₁).trans
    (Finset.prod_le_prod (fun i _ => Y.root_nonneg _ _) (fun i _ => h₂ i)))
  rw [Fintype.prod_prod_type]
  simp

private lemma gather {α : Type*} [Fintype α] {U : Type*} [CommMonoid U] (f : κ → α)
    [(i : α) → Fintype {x // f x=i}] (g : κ → U) :
    (∏ i : α, ∏ j : {x // f x=i}, g j.val) = ∏ j : κ, g j := by
  have he := Equiv.prod_comp (Equiv.sigmaFiberEquiv f) g
  rw [Fintype.prod_sigma] at he; exact he



theorem stocked (H : C.Makes) (yh : Y.kind=.link) (th : T.kind=.link) (offset : Y.base=T.base)
    (tiles : Y.side.val ∣ T.side.val) {b : ℕ} (hb:b ≤ N) (hY:span C.S hb p ∣ Y.side.val)
    (F : ι→Config G (C.side N p) → ℂ)(c:ι→ T.Cell) (hi: Injective c)
    (A:ι→ℝ) (hr:∀ i, Interior (T.chamber 0) (F i))(hA:∀ i,T.rootTest (C.beta N p) (F i)≤ A i)
    (v : κ → C.book.Token) (y: κ → Site (C.side N p)) (hy:∀ j, Next.Phase.Inside Y (3*span C.S hb p) (y j))
    (he : ∀ i j, c i ≠ T.which (y j)) (hp : ∀ i j, i≠j → Y.side.val < separation (y i) (y j))
    (B:κ→ℝ) (hB:∀ i,0≤B i)(hd:∀ j,Single C (v j) (B j) b N p):
    ‖moment (C.beta N p) (fun U=> (∏ i,T.copy (c i) (F i) U)*∏ j,C.seen (v j) (y j) U)‖ ≤ (∏ i,A i)*∏ i,B i :=by
  classical
  let e i:=T.which (y i); let s:= Set.range e; let f : κ → s:= Set.rangeFactorization e
  let D:= Sum.elim c (fun p:s=> p.val); letI : Fintype s:= Fintype.ofFinite _; have hec i (a:s) : c i ≠ a.val:= by obtain ⟨j,hj⟩:= a.property; rw [← hj];exact he i j
  have hInj : Injective D := by
    rintro (i|i) (j|j) h
    · rw [hi h]
    · exact (hec i j h).elim
    · exact (hec j i h.symm).elim
    rw [Subtype.ext (show i.val=j.val from h)]
  choose E hE hw hg using fun i : s =>
    exterior_pay (κ := {x // f x=i}) H yh th offset tiles hb hY (fun j => v j.val) (fun j => y j.val) i.val
      (fun j => congrArg Subtype.val j.property) (fun j => hy _) (fun j l h => hp _ _ (Subtype.val_injective.ne h))
      (fun j=> B j.val) (fun j=> hB j.val) (fun j => hd _)
  let V := Sum.elim F E
  let W := Sum.elim A (fun i : s => ∏ j : {x // f x=i}, B j.val)
  have ht i : T.rootTest (C.beta N p) (V i) ≤ W i := by
    rcases i with i|i
    · exact hA i
    change T.rootTest _ (E i) ≤ ∏ j : {x // f x=i}, B j.val
    exact hg i
  have hv (U : Config G (C.side N p)) :
      (∏ i, T.copy (c i) (F i) U) * (∏ j, C.seen (v j) (y j) U) = ∏ i, T.copy (D i) (V i) U := by
    rw [Fintype.prod_sum_type, ← gather f (fun j => C.seen (v j) (y j) U)]
    simp only [D,V,Sum.elim_inr,Sum.elim_inl,hE]
  rw [funext hv]
  apply (le_trans <| (T.planted (seamless H ..) D hInj V (by rintro (i|i); exacts [hr _,hw _])).trans
    (Finset.prod_le_prod (fun _ _ => T.root_nonneg _ _) (fun i _ => ht i)))
  unfold W; rw [Fintype.prod_sum_type]; simp only [Sum.elim_inl,Sum.elim_inr]
  rw [gather f B]

end YM.Contacts.Costar
