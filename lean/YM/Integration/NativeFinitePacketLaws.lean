import YM.Integration.NativeFiniteMarkedPackets

/-! Transfer original finite-token certificates to their exact Nat-padded
packet layout. The rank cast changes no token field or mathematical property. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.LocalComparison.MarkedPackets
open Function Finset Lattice Wilson RG Marker
open Comparison.Density.RenderM
open scoped Classical

variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V]
  {R : Census V} {D : V → ComparisonDensity.Address.Orbit} {count : ℕ}
  (mode : Fin count → R.Mode) (rank : Fin count → ℕ) (power : Fin count → ℤ)
  (T : (k : Fin count) → Token G n (fun v => (D v).Mood) (rank k))
  (hm : ∀ k, mode k ≠ R.quiet) (hg : ∀ k, 0 ≤ power k + (rank k : ℤ))

private theorem rank_at (i : ℕ) (hi : i < count) :
    (ofFin mode rank power T hm hg).rank i = rank ⟨i, hi⟩ := by
  change (if h : i < count then rank ⟨i, h⟩ else 0) = _
  exact dif_pos hi

private theorem token_at (i : ℕ) (hi : i < count) :
    (ofFin mode rank power T hm hg).packet i =
      some (cast (congrArg (fun q => Token G n (fun v => (D v).Mood) q)
        (rank_at mode rank power T hm hg i hi).symm) (T ⟨i, hi⟩)) := by
  change (if h : i < count then
    some (cast (congrArg (fun q => Token G n (fun v => (D v).Mood) q)
      (rank_at mode rank power T hm hg i h).symm) (T ⟨i, h⟩))
    else none) = _
  rw [dif_pos hi]

omit [DecidableEq V] in
private theorem property_cast {a b : ℕ} (h : a = b)
    (Q : (q : ℕ) → Token G n (fun v => (D v).Mood) q → Prop)
    (t : Token G n (fun v => (D v).Mood) a) (ht : Q a t) :
    Q b (cast (congrArg (fun q => Token G n (fun v => (D v).Mood) q) h) t) := by
  cases h
  exact ht

/-- Every present Nat entry has all the original finite token's laws,
with its exact original mode, rank and coupling power. Padding is absent. -/
theorem ofFin_all
    (Q : R.Mode → (q : ℕ) → ℤ → Token G n (fun v => (D v).Mood) q → Prop)
    (hQ : ∀ k, Q (mode k) (rank k) (power k) (T k))
    (i : ℕ) (t : Token G n (fun v => (D v).Mood)
      ((ofFin mode rank power T hm hg).rank i))
    (ht : (ofFin mode rank power T hm hg).packet i = some t) :
    Q ((ofFin mode rank power T hm hg).mode i)
      ((ofFin mode rank power T hm hg).rank i)
      ((ofFin mode rank power T hm hg).power i) t := by
  have hi : i < count := by
    by_contra hn
    rw [ofFin_absent mode rank power T hm hg i (Nat.le_of_not_gt hn)] at ht
    cases ht
  let k : Fin count := ⟨i, hi⟩
  have he : t = cast (congrArg (fun q => Token G n (fun v => (D v).Mood) q)
      (rank_at mode rank power T hm hg i hi).symm) (T k) :=
    Option.some.inj (ht.symm.trans (token_at mode rank power T hm hg i hi))
  subst t
  have hmode : (ofFin mode rank power T hm hg).mode i = mode k := by
    change (if h : i < count then mode ⟨i, h⟩ else R.quiet) = _
    exact dif_pos hi
  have hpower : (ofFin mode rank power T hm hg).power i = power k := by
    change (if h : i < count then power ⟨i, h⟩ else 0) = _
    exact dif_pos hi
  rw [hmode, hpower]
  exact property_cast (rank_at mode rank power T hm hg i hi).symm
    (fun q t => Q (mode k) q (power k) t) (T k) (hQ k)

end YM.Integration.LocalComparison.MarkedPackets
end
