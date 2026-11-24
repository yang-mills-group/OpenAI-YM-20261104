import YM.Integration.OriginalRootedPacketLayout

/-! The native normalized, square-free marked transfer depends only on the
incoming submasks of the active mode. No inactive root needs to be moved
when comparing two different presentations of that same active mode. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalMarkedRootDependence
open Function Filter Finset Lattice RG Wilson Marker Laurent Precision
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Embroider WilsonCoeffUV.Mer.Rolls
open WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Soil
open IndependentSourcePathFamily OriginalRootedPacketLayout
open scoped BigOperators Classical

variable {V : Type} [DecidableEq V] {G : Gauge} {D : V→ℕ} {J : Finset V}

def agrees (E F : family G D) (J : Finset V) := ∀ H⊆J, E H=F H

theorem levels {E F : family G D} (h : agrees E F J) : levelsO E J=levelsO F J := by
  induction J using Finset.strongInduction with
  | H S ih =>
    by_cases hz : S=∅
    · subst S; rw [empty_level,empty_level]
    conv_lhs => rw [levelsO,dif_neg hz]
    conv_rhs => rw [levelsO,dif_neg hz]
    congr 1
    apply sum_congr rfl
    intro A hA
    split
    next ha =>
      rw [h A ha.1,ih (S\A) (sh_k ha.1 ha.2) (fun T hT => h T (hT.trans sdiff_subset))]
    next _ => rfl

theorem reverse {E F : family G D} (h : agrees E F J) : reverseO E J=reverseO F J := by
  induction J using Finset.strongInduction with
  | H S ih =>
    by_cases hz : S=∅
    · subst S; rw [empty_reverse,empty_reverse]
    conv_lhs => rw [reverseO,dif_neg hz]
    conv_rhs => rw [reverseO,dif_neg hz]
    rw [h S (subset_refl _)]
    congr 2
    apply sum_congr rfl
    intro A hA
    split
    next ha =>
      rw [ih A (lt_of_le_of_ne ha.1 ha.2) (fun T hT => h T (hT.trans ha.1)),h _ sdiff_subset]
    next _ => rfl

theorem transfer (A : Levels G) (O : ChartRatio G) (m N : ℕ) (k : V→ℕ)
    {E F : family G D} (h : agrees E F J) : logO A O m N E k J=logO A O m N F k J := by
  apply reverse
  intro H hH
  unfold edV
  rw [levels (fun T hT => h T (hT.trans hH))]

def «scoped» (K : (V → Cover)→family G D) :=
  ∀ J y y', (∀ a∈J,y a=y' a) → K y J = K y' J

theorem transfer_scoped (K : (V → Cover)→family G D) (hK : «scoped» K)
    (A : Levels G) (O : ChartRatio G) (m N : ℕ) (k : V→ℕ) :
    «scoped» (fun y => logO A O m N (K y) k) := by
  intro J y y' he
  exact transfer A O m N k (fun H hH => hK H y y' (fun v hv => he v (hH hv)))

variable [Fintype V]

theorem independent_roots {I : V → Type} [∀ v,Fintype (I v)] (X : ∀ v,I v→Seed G (D v)) :
    «scoped» (independent X) := by
  intro J y y' he
  unfold independent
  apply sum_congr rfl
  intro v _
  unfold packOne
  split
  next h => rw [he v (h ▸ mem_singleton_self _)]
  next _ => rfl

omit [Fintype V] in
theorem chart (K : (V → Cover)→family G D) (hK : «scoped» K)
    (A : Levels G) (O : ChartRatio G) (m N : ℕ) (k : V→ℕ)
    (C : Census V) (s : {s:C.Mode // s.val.Nonempty}) {n : Side} (p : V→Site n) :
    logO A O m N (K (placed C p s)) k s.val.val =
      logO A O m N (K (fun v => lift (p (owner C s)) + lift (p v - p (owner C s)))) k s.val.val := by
  apply transfer_scoped K hK
  intro v hv
  by_cases he : v=owner C s
  · subst v
    simp [OriginalRootedPacketLayout.placed,toe]
  · simp [OriginalRootedPacketLayout.placed,OriginalRootedPacketLayout.actual,toe,he,mem_erase.mpr ⟨he,hv⟩]

end YM.Integration.OriginalMarkedRootDependence
end
