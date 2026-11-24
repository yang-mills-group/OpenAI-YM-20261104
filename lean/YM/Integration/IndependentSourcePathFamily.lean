import YM.Integration.OriginalMarkedSourceComet

/-! Construct an independent preblock source family by summing the genuine
field paths and address rows at their named primitive marks. Both the finite
periods and the cover are part of the same native operator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.IndependentSourcePathFamily
open Function Finset Lattice Wilson RG Source Labels Marker
open WilsonCoeffUV WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank
open WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open OriginalMarkedSourceComet
open scoped Classical BigOperators

variable {ι : Type} [DecidableEq ι] [Fintype ι] {G : Gauge}

/-- Raw coefficients are fixed before the external tests, at one independently
specified field stencil and compact derivative address. -/
structure Seed (G : Gauge) (D : ℕ) where
  rank : ℕ
  head : ℕ
  path : Fin rank → RG.Slot
  color : Fin rank → G.ColorIndex
  weight : ℂ
  quadrant : ℂ →L[ℝ] ℝ
  knob : Knob D
  point : Chamber

variable {D k : ι → ℕ} {I : ι → Type} [∀ i, Fintype (I i)]
  (X : ∀ i, I i → Seed G (D i))

private def atom {d : ℕ} (v : Seed G d) := colour v.path v.color v.weight v.quadrant
private def comet {d : ℕ} (v : Seed G d) := current (atom v) (claim d v.knob v.point)

def single (i : ι) (p : Cover) : Era G (Pen D {i}) :=
  ∑ b : I i, let u := X i b; source D i (atom u) u.knob u.point u.head p

def packOne (i : ι) (u : Era G (Pen D {i})) (M : Finset ι) : Era G (Pen D M) :=
  if h : {i} = M then h ▸ u else 0

def independent (z : ι → Cover) : family G D := fun M => ∑ i, packOne i (single X i (z i)) M

@[simp] theorem singleton (z : ι → Cover) (i : ι) : independent X z {i} = single X i (z i) := by
  unfold independent
  rw [Finset.sum_eq_single i]
  · simp [packOne]
  · intro j _ hji; simp [packOne,hji]
  · simp

private theorem dark (z : ι → Cover) (M : Finset ι) (hm : ∀ i, M ≠ {i}) : independent X z M = 0 := by
  unfold independent
  exact Finset.sum_eq_zero fun i _ => dif_neg (Ne.symm (hm i))

theorem empty (z : ι → Cover) : independent X z ∅ = 0 := dark X z ∅ (by simp)

theorem legal (z : ι → Cover) (hX : ∀ i b, (X i b).rank ≤ k i + (X i b).head) :
    Eu k (independent X z) := by
  intro M
  by_cases h : ∃ i, M={i}
  · obtain ⟨i,rfl⟩ := h
    rw [singleton,mass,Finset.sum_singleton]
    apply Auth.sum
    intro b _
    exact certified _ _ _ (fun g a=>invariant _ _ _ _ g a) _ _ _ _ (hX i b) _
  · rw [dark X z M (fun i hmi => h ⟨i,hmi⟩)]
    exact unstamped

/-- All costs are the original Comet path/colour invoice and the one fixed
kinetic width. Summing over the finite heat order makes this single cost work
for every tensor degree and every specified collection of marks. -/
def charge (k : ι → ℕ) (cap : ℕ) (w : ℝ) (i : ι) (b : I i) : ℝ :=
  ∑ j : Fin (k i+cap+1), |integerP (comet (X i b)) w * flour G (steep w) (X i b).rank j.val|

def bill (k : ι → ℕ) (cap : ℕ) (w : ℝ) : ℝ := ∑ i, ∑ b : I i, charge X k cap w i b

omit [Fintype ι] [∀ i,Fintype (I i)] in
private theorem charged (i : ι) (b : I i) (z : ι → Cover) (cap : ℕ) {w : ℝ} (hw : 0<w)
    (hX : (X i b).rank ≤ k i+(X i b).head) (e j : ℕ) (he : e≤cap) :
    let v:=X i b
    Wig terrain z (steep w) (charge X k cap w i b) {i} ((source D i (atom v) v.knob v.point v.head (z i)).2 e j) := by
  intro v
  by_cases hj : j≤k i+cap
  · apply (funded D i (atom v) v.knob v.point v.head z hw e j).more
    refine (le_abs_self _).trans ?_
    exact Finset.single_le_sum (f:=fun u : Fin (k i+cap+1) =>
      |integerP (comet v) w*flour G (steep w) v.rank u.val|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ (⟨j,by omega⟩ : Fin (k i+cap+1)))
  · have hz := movesCount (august (comet v)) hX e j (by omega)
    have gone : ((source D i (atom v) v.knob v.point v.head (z i)).2 e j) = 0 := by
      funext x
      change (petal D i) ((moved v.rank v.head (august (comet v)) e j) _) = 0
      rw [hz]; exact map_zero _
    rw [gone]
    exact Wig.zero.more (Finset.sum_nonneg fun _ _ => abs_nonneg _)

/-- The complete independently indexed raw source is admitted before blocking,
for arbitrary prescribed fine site lifts. The budget retains each original
field path, each source derivative, and each non-vacuum weight. -/
theorem preblock (z : ι → Cover) (Z : Finset ι) (cap : ℕ) {w : ℝ} (hw : 0 < w)
    (hX : ∀ i b, (X i b).rank ≤ k i + (X i b).head) :
    0 ≤ bill X k cap w ∧ Eu k (independent X z) ∧ independent X z ∅=0 ∧
      safeB z (independent X z) Z cap (steep w) (bill X k cap w) := by
  have hc i b : 0 ≤ charge X k cap w i b := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hb : 0 ≤ bill X k cap w := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun b _ => hc i b
  refine ⟨hb,legal X z hX,empty X z,?_⟩
  intro M _ e he j
  by_cases h : ∃ i, M={i}
  · obtain ⟨i,rfl⟩ := h
    rw [singleton,Finset.card_singleton,pow_one]
    have hs := Wig.sum (Z:=Finset.univ) (fun b _ => charged X i b z cap hw (hX i b) e j he)
    have htotal := hs.more (Finset.single_le_sum (s:=Finset.univ) (f:=fun a=>∑ b,charge X k cap w a b) (fun a _ => Finset.sum_nonneg fun b _ => hc a b) (Finset.mem_univ i))
    simpa only [single,Prod.snd_sum,Finset.sum_apply,bill] using htotal
  · rw [dark X z M (fun i hmi => h ⟨i,hmi⟩)]
    exact Wig.zero.more (pow_nonneg hb _)

end YM.Integration.IndependentSourcePathFamily
end
