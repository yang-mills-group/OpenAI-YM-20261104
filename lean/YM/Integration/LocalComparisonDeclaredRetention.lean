import YM.Integration.LocalComparisonEnvelope

/-! Static declarations for the native padded forced-coefficient array.

`Bands.Active` gives every natural-number slot a nonempty marker mode, even
when a slot is unused padding. Full source-address retention therefore applies
to the statically declared slots, not to these arbitrary padding modes. The
declaration is fixed before the test arguments; outside it every coefficient
is identically zero for all tests and fields. A genuine declared coefficient
keeps its full address even when its current test value is zero.

The native encoding must identify its declaration set and prove the padding
equation. This module neither chooses declarations from observed nonzero
values nor asserts that an arbitrary source has such a presentation.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison
open Lattice Wilson RG Marker RG3.Script.Picnic

variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V]
    {R : Census V} {X Y : Type*} {P : Rep G n} {o : V → Site n}

/-- Address retention on the source encoding's fixed genuine forced slots.
Regular and caption layouts already have a region in which zero padding can
be placed, so their original unconditional address clauses are unchanged. -/
structure RetainsDeclared (declared : Set (ℕ × ℕ))
    (T : Taste X o P R) (address : V → Support n) : Prop where
  origins v : o v ∈ address v
  regular i v : v ∈ (T.menu.rays i).val → address v ⊆ T.menu.branch i
  forced i j : (i, j) ∈ declared → ∀ v ∈ (T.menu.marks i j).val,
    address v ⊆ (P.activities.forced i).support
  padding i j : (i, j) ∉ declared → ∀ x, T.menu.force x i j = 0
  captions i v : v ∈ (T.tag i).val → address v ⊆ T.site i

/-- The earlier stronger receipt remains available as the all-declared case. -/
theorem Retains.declared {T : Taste X o P R} {address : V → Support n}
    (H : Retains T address) : RetainsDeclared Set.univ T address where
  origins := H.origins
  regular := H.regular
  forced i j _ := H.forced i j
  padding i j h := (h (Set.mem_univ (i, j))).elim
  captions := H.captions

/-- No retention clause is lost when every slot is declared. -/
theorem RetainsDeclared.all {T : Taste X o P R} {address : V → Support n}
    (H : RetainsDeclared Set.univ T address) : Retains T address where
  origins := H.origins
  regular := H.regular
  forced i j := H.forced i j (Set.mem_univ (i, j))
  captions := H.captions

theorem RetainsDeclared.pullback {declared : Set (ℕ × ℕ)}
    {T : Taste X o P R} {address : V → Support n}
    (H : RetainsDeclared declared T address) (f : Y → X) :
    RetainsDeclared declared (pullback f T) address where
  origins := H.origins
  regular := H.regular
  forced := H.forced
  padding i j h x := H.padding i j h (f x)
  captions := H.captions

/-- Relative-norm encoding retains the same declaration, including genuine
coefficients that a zero scalar happens to annihilate. -/
theorem RetainsDeclared.priceNormalized {declared : Set (ℕ × ℕ)}
    {T : Taste X o P R} {address : V → Support n}
    (H : RetainsDeclared declared T address) (cost : R.Mode → ℝ) :
    RetainsDeclared declared (priceNormalized cost T) address where
  origins := H.origins
  regular := H.regular
  forced := H.forced
  padding i j h x := by
    funext U
    change (cost (T.menu.marks i j))⁻¹ • T.menu.force x i j U = 0
    rw [congrFun (H.padding i j h x) U]
    simp only [Pi.zero_apply, smul_zero]
  captions := H.captions

/-- An actually nonzero coefficient must be declared. This is a consequence
of the static padding equation, not the definition of declaration. -/
theorem RetainsDeclared.declared_of_nonzero {declared : Set (ℕ × ℕ)}
    {T : Taste X o P R} {address : V → Support n}
    (H : RetainsDeclared declared T address) {x : X} {i j : ℕ}
    {U : Config G n} (h : T.menu.force x i j U ≠ 0) : (i, j) ∈ declared := by
  by_contra hn
  exact h (congrFun (H.padding i j hn x) U)

end YM.Integration.LocalComparison
