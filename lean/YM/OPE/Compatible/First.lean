import YM.OPE.Compatible.Joint
import YM.OPE.Single

/-!
# A single OPE through all horizons

* Continuum, including every character. On a same construction as in
  `Spec.CLOSED`, gives the *actual* quantitative tested OPE simultaneous on
  the unselected and every character system and therefore arbitrary
  probability mixtures.
* `Shade`/`Covered` wrappers from `Beam`, `Seen` from `Joint`; estimates on
  full compression algebra imply the every-state and test bounds, see the
  joint corollaries there. For all arities, field lists, separated shape
  geometries. Uses arbitrary positive ε loss here. Includes rotations,
  translations, permutation covariance through the original field action.
  See `Laws`. Proof estimates only against **fixed** spectators at **fixed**
  orbits in detector reads; later-added exteriors neither fit the projection
  nor change it.
* Uses intermediate theorems of `YM.OPE.Single` on its actual witness.
  Does *not* claim UV cutoff convergence outside the limit order of the
  construction, nor unrestricted collision limits at a fixed cutoff.
  All rate estimates are continuum ones; our `grouped-product` estimate
  is directly on the coherent readout, no extra perturbative reporting
  conventions here.
* This file is upstream of any perturbative comparisons, and doesn't have
  nested or logarithmic estimates; `Tree` will use it.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cov.Display
open Function Set Filter MeasureTheory Survey Signal
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book}
    (U : Spec.Final C f S)
variable {I J l:Type} [Fintype I] [Fintype J] {δ η c ε M : ℝ} {φ : Filter l}
    {X:l → I → E4} {Y:l → J → E4} {O:l → E4} {r:l → ℝ}

lemma later (a : Tones U) (hr : Tendsto r φ (𝓝[>] 0)) :
  ∀ᶠ i in φ, ∀ (x:I→ E4) (p:I→ S.Tag) (o:E4), beam U a (r i) x p o = lens U a x p o := by
    filter_upwards [hr.eventually (p:=fun x=>0<x) self_mem_nhdsWithin,
      (hr.mono_right nhdsWithin_le_nhds).eventually (gt_mem_nhds (period_pos (supplies S) a.fst))]
      with i hi he x p o using fully U a a.fst le_rfl hi he.le x p o

variable (H : Services C f S) (p : I → S.Tag) (q : J → S.Tag) (a : Tones U)
    (hη : 0 < η) (hM : 0 ≤ M) (hc : 0 < c) (he : 0 < ε)

include H U hη hM he p
lemma one_shape [φ.NeBot] (hr : Tendsto r φ (𝓝[>] 0))
    (hx : ∀ᶠ i in φ, WithinRoom (r i) M η (X i) (O i)) :
    ∀ᶠ i in φ, Covered S (r i) (X i) (O i) ∧
      ‖beam U a (r i) (X i) p (O i)‖ ≤ (r i)^((a.fst:ℝ) - (bill p:ℝ)-ε) := by
  obtain ⟨hg,hf⟩ := room_regime hr hM hη hx
  have hR := run_towards hr
  have hp := step_rate U H hR p hf hg zero_lt_one a
  have he' := (loglife hr).rpow ((a.fst:ℝ) - (bill p:ℝ)-ε)
  filter_upwards [hx,hf.inject,hr.eventually (valid_geometry (I:=I) (S:=S) M),
    he'.outweigh hp (by linarith only [he]) hR,later (I:=I) U a hr] with i hi ht h hd h'
  exact ⟨h (X i) _ ht hi.span,(h' _ p _).symm ▸ hd⟩
include q hc
lemma seen_one [φ.NeBot] (hr : Tendsto r φ (𝓝[>] 0))
    (hx : ∀ᶠ i in φ, WithinRoom (r i) M η (X i) (O i))
    (hy : ∀ᶠ i in φ, ClearOf (O i) (Y i) c) (k : ℕ) :
    ∀ᶠ i in φ, Seen U k (r i) (X i) p (O i) (Y i) q ((r i)^((k:ℝ)+1-(bill p:ℝ)-ε)) := by
  obtain ⟨hg,hf⟩ := room_regime hr hM hη hx
  have hR := run_towards hr
  obtain ⟨hw,hc'⟩ := free_clear hR hc hy
  have hi := ((hf.chorus (hw.mono zero_le_one)
    ((Rec_spacing hR hc' hg zero_lt_one).mono zero_le_one)).inject).and
    (((Kept.sole φ _ O 0).chorus hw hc').inject)
  have hp := price_from_viewers U k p q r X O Y hi hr (fun v => single_rate U H hR p q v hf hg hc' zero_lt_one le_rfl hw le_rfl k)
  have he' := (loglife hr).rpow ((k:ℝ)+1-(bill p:ℝ)-ε)
  filter_upwards [hx,hf.inject,hr.eventually (valid_geometry (I:=I) (S:=S) M),
    he'.outweigh hp (by linarith only [he]) hR,hi] with i hx hi ht hp hh
  exact ⟨ht _ _ hi hx.span,hh.1,hh.2,hp⟩

structure Simple (U : Spec.Final C f S) : Prop where
  -- covariant splitting and homogeneous basis intrinsic to `beam`, no later choice.
  terms {I:Type} [Fintype I] (p:I → S.Tag) (a : Tones U) (η M ε : ℝ) : 0 < η → 0 ≤ M → 0 < ε →
    ∀ᶠ r:ℝ in 𝓝[>] 0, ∀ (x:I → E4) (o:E4), WithinRoom r M η x o →
      Covered S r x o ∧ ‖beam U a r x p o‖ ≤ r^((a.fst:ℝ) - (bill p:ℝ) - ε)
  horizons {I J : Type} [Fintype I] [Fintype J] (p:I → S.Tag) (q:J→ S.Tag) (η M c ε : ℝ) :
    0 < η → 0 ≤ M → 0 < c → 0 < ε → ∀ k : ℕ,
      ∀ᶠ r:ℝ in 𝓝[>] 0, ∀ (x:I → E4) (o:E4) (y:J → E4), WithinRoom r M η x o → ClearOf o y c →
        Seen U k r x p o y q (r^((k:ℝ)+1-(bill p:ℝ)-ε))

omit hη hM he p q hc
lemma universal : Simple U := by
  constructor
  · intro I _ p a η M ε hη hM he
    have hw := refine_geometry (P:=fun (r:ℝ) (b:(I→E4)×E4) => WithinRoom r M η b.1 b.2)
      (Q:=fun (r:ℝ) b => Covered S r b.1 b.2 ∧ ‖beam U a r b.1 p b.2‖≤ r^((a.fst:ℝ) - (bill p:ℝ) - ε))
      (φ:=𝓝[>]0) (fun f ψ hN hp h => ⟨ψ,hN,le_rfl,one_shape (r:=fun r=>r) (X:=fun x => (f x).1)
        (O:=fun x => (f x).2) U H p a hη hM he (tendsto_id.mono_left hp) h⟩)
    filter_upwards [hw] with r hr x o using hr (x,o)
  intro I J _ _ p q η M c ε hη hM hc he k
  have hw := refine_geometry (P:=fun (r:ℝ) (b:(I→E4)× E4 × (J→E4)) =>
        WithinRoom r M η b.1 b.2.1 ∧ ClearOf b.2.1 b.2.2 c)
    (Q:=fun (r:ℝ) b => Seen U k r b.1 p b.2.1 b.2.2 q (r^((k:ℝ)+1-(bill p:ℝ)-ε)))
    (φ:=𝓝[>] 0) (fun f ψ hN hp h => ⟨ψ,hN,le_rfl,seen_one (r:=fun r=>r)
      (X:=fun x => (f x).1) (O:=fun x => (f x).2.1) (Y:=fun x => (f x).2.2) U H p q hη hM hc he
        (tendsto_id.mono_left hp) (h.mono fun _ hi => hi.1) (h.mono fun _ hi => hi.2) k⟩)
  filter_upwards [hw] with r hr x o y hx hy using hr (x,o,y) ⟨hx,hy⟩

omit H U
-- include witness for consumers of other components via Services, no refactoring
/-- Joint existence with the original Final. -/
theorem slope (G:Gauge) (h:G.Simple) : ∃ (C:Family G) (f:Extraction.Order) (S:Table C.book), Services C f S ∧
    ∃ U : Spec.Final C f S, Simple U := by
  obtain ⟨C,g,A,S,U,p,-⟩ := OPE.single G h Extraction.Order.full
  exact ⟨C,_,A,S,U,universal U S⟩
end YM.OPE.Cov.Display
