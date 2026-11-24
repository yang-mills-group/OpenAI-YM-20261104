import YM.Integration.WilsonCenteredNestedTreeSharp

/-! The two distinct numerical comparisons in the ordinary deposited pair.
The child is tested at g(a) and the parent at g(r) on its genuine filed
actor. The physical reader and the independent rule retain their signs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedTreeLocalRows
open Function Filter Set Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader OPE.Prescription
open OPE.Log OPE.Nesting OPE.Nesting.Atom OPE.Nesting.Tree OPE.Nesting.Composite
open WilsonCenteredNestedTwoVertex WilsonCenteredNestedProgram WilsonCenteredNestedPairChord
open WilsonCenteredNestedRawRows WilsonCenteredNestedRawPair WilsonCenteredNestedPairRead
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

def innerValue (A:Rule F Q) (g:ℝ→ℝ) (v:full.Leaf→S.Tag) (z:full.Plot) (a:ℝ) {D:ℕ} (t:Menu.Cut Q D) : ℂ :=
  A 2 t.1 t.2 a (g a) (skyline (childPlace 0 z)) (near v) (anchor (childPlace 0 z))

def outerValue (A:Rule F Q) (g:ℝ→ℝ) (v:full.Leaf→S.Tag) (z:full.Plot) (r:ℝ) (m:ℕ)
    (c:Q.channels m) {D:ℕ} (t:Menu.Cut Q D) : ℂ := A 2 m c r (g r) (skyline z) (placed F Q t (other v)) (anchor z)

lemma assembled (A:Rule F Q) (g:ℝ→ℝ) (r a:ℝ) (v:full.Leaf→S.Tag) (z:full.Plot) (D m:ℕ) (c:Q.channels m) :
    run F Q A g full (dates r a) z v (caps m D) m ⟨Fin.last m,c⟩ =
      ∑ t:Menu.Cut Q D,innerValue F Q A g v z a t * outerValue F Q A g v z r m c t := by
  rw [deposited F Q A g m D v z r a m c]
  apply Finset.sum_congr rfl
  intro t _
  apply congrArg (_ * ·)
  apply congrArg (fun w=>A 2 m c r (g r) (skyline z) w (anchor z))
  funext i
  fin_cases i
  · exact (heldTags F Q m D v t).1
  · exact (heldTags F Q m D v t).2

theorem signed (A:Rule F Q) (g:ℝ→ℝ) (r a:ℝ) (v:full.Leaf→S.Tag) (z:full.Plot) (D m:ℕ) (c:Q.channels m) :
    Kernel.chord F Q z v c (caps m D) - run F Q A g full (dates r a) z v (caps m D) m ⟨Fin.last m,c⟩ =
    ∑t:Menu.Cut Q D,
      ((innerValue F Q (measured F Q) g v z a t - innerValue F Q A g v z a t) * outerValue F Q (measured F Q) g v z r m c t +
      innerValue F Q A g v z a t * (outerValue F Q (measured F Q) g v z r m c t - outerValue F Q A g v z r m c t)) := by
  rw [←WilsonCenteredNestedProgram.chord F Q g (dates r a) z v (caps m D) m c]
  change run F Q (measured F Q) g full (dates r a) z v (caps m D) m ⟨Fin.last m,c⟩ - _ = _
  rw [assembled F Q (measured F Q) g r a v z D m c,assembled F Q A g r a v z D m c,←Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _=>by ring

def invoice (A:Rule F Q) (g:ℝ→ℝ) (r a:ℝ) (v:full.Leaf→S.Tag) (z:full.Plot) (D m:ℕ) (c:Q.channels m)
    (e h:Menu.Cut Q D→ℝ) : ℝ := ∑t:Menu.Cut Q D,
      (e t * ‖outerValue F Q (measured F Q) g v z r m c t‖ + ‖innerValue F Q A g v z a t‖ * h t)

theorem priced (A:Rule F Q) (g:ℝ→ℝ) (r a:ℝ) (v:full.Leaf→S.Tag) (z:full.Plot) (D m:ℕ) (c:Q.channels m)
    (e h:Menu.Cut Q D→ℝ)
    (near_price:∀t,‖innerValue F Q (measured F Q) g v z a t - innerValue F Q A g v z a t‖≤e t)
    (root_price:∀t,‖outerValue F Q (measured F Q) g v z r m c t - outerValue F Q A g v z r m c t‖≤h t) :
    ‖Kernel.chord F Q z v c (caps m D) - run F Q A g full (dates r a) z v (caps m D) m ⟨Fin.last m,c⟩‖ ≤
      invoice F Q A g r a v z D m c e h := by
  rw [signed]
  apply (norm_sum_le ..).trans
  apply Finset.sum_le_sum
  intro t _
  apply (norm_add_le ..).trans
  rw [norm_mul,norm_mul]
  exact add_le_add (mul_le_mul_of_nonneg_right (near_price t) (norm_nonneg _))
    (mul_le_mul_of_nonneg_left (root_price t) (norm_nonneg _))

end YM.Integration.WilsonCenteredNestedTreeLocalRows
