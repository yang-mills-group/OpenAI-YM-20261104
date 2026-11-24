import YM.RG11Proof.Bridge.Removal

/-!
# One conversion on comparable overlap demands

Formal limit arrays ONLY. The varying regulator comparison moves c_m(s)
needn't restrict across overlaps; their solved continuum jets will by this
theorem. This endpoint takes many substantial external inputs, e.g.
`RegControl` through the required orders on sufficiently large common field
horizons. It neither generates those inputs nor interprets the array
coefficients at positive coupling on an actual `Family`. The Bills here are
on the common regulator, not the Gram transforms of `F` (that's a different
estimate). -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Bridge
open PowerSeries YM.PertExtension.Position YM.RG11.Jets YM.RG11.Formal YM.RG11.Rate YM.RG11.Horizon Filter
open scoped Classical BigOperators Topology

variable {P : Type*} {shape : P→ℕ} (M : Horizon.Mesh ℝ shape)
universe u

/-- `M.J n` may for instance index a stipulated real filtered basis on the
horizon n of fields E_{h(n)} ordered from the unit included, h(0) sufficient
for coupling-normalization request. Choose one ψ across all n, common P tests.
Fix `α` as large as needed to hold regulator index tuples (or block hierarchies),
size/delay may depend arbitrarily on the m,n,k requests. This is NOT cutoff
uniform at actual scales; it enables coefficient-by-coefficient identification
only, with rate on each such regulator, not rates through physical Gram readout.
-/
structure Way (α : Type*) (M : Horizon.Mesh ℝ shape) (n k : ℕ) (m : Finset (Mark (M.J n) shape)) where
  π : Budget α
  live : π.along.NeBot
  pivot : α→ArrayAt (M.J n) ℝ shape
  column : α→ArrayAt (M.J n) ℝ shape
  translate : α→Change ℝ (M.J n)
  bills : RegControl π k m (M.A n) (M.B n) pivot column (M.requests n) translate
  axis : ℝ
  slope_ne : axis ≠ 0
  derives : Tendsto (fun a=> coeff 1 (translate a).g) π.along (𝓝 axis)

variable (α : Type*)

/-- Version allowing cofinally many order & field demands, all finite mark
lists there. One can also use with just enlarged test demand at those higher
field horizons whose projections include the desired finite tests (and
higher-horizon detector). -/
structure High : Prop where
  feasible (n k:ℕ) : ∃ N, n ≤ N ∧ ∃ K, k ≤ K ∧
    ∀ m : Finset (Mark (M.J N) shape),
      ∃ m' : Finset (Mark (M.J N) shape), m ⊆ m' ∧ Nonempty (Way α M N K m')

variable {α} (D : ∀ n, Detector (M.requests n) (M.A n)) (hs : High M α)
include hs D

theorem all_compatible (hS : M.Steady) : Nonempty M.Reports := by
  refine ⟨Horizon.Mesh.obtainReports M D hS ?_⟩
  intro n k
  obtain ⟨N,hN,K,hK,h⟩:= hs.feasible n (max 1 k)
  refine ⟨N,hN,K,(le_max_right ..).trans hK,fun m=>?_⟩
  classical
  let Q:=D N
  obtain ⟨m',hm,⟨W⟩⟩ := h (m ∪ TestDemand Q)
  haveI := W.live
  have he : TestDemand Q ⊆ m':= Finset.union_subset_iff.mp hm |>.2
  obtain ⟨hg,hB⟩ := RegControl.finite_match W.bills he ((le_max_left ..).trans hK) W.axis W.slope_ne W.derives
  exact ⟨solution Q (M.B N),hg, fun i hi=> hB i (hm (Finset.mem_union_left _ hi))⟩

omit hs D in
/-- Spell out orientation and the common inverse and coupling, removing FPS
Through wrappers. -/
theorem read (C : M.Reports) (H : M.Steady) :
    ∃ (T f : PowerSeries ℝ) (Z D : ∀ n, Square (M.J n) ℝ⟦X⟧),
    (Coupling T ∧ Coupling f) ∧ PowerSeries.subst f T=PowerSeries.X ∧ PowerSeries.subst T f=PowerSeries.X ∧
    (∀ n, Change.Good (M.requests n) ⟨f,Z n⟩ ∧ Change.Good (M.requests n) ⟨T,D n⟩ ∧ Z n*subs f (D n)=1 ∧ D n*subs T (Z n)=1 ∧
          M.B n=(Change.act ⟨T,D n⟩ (M.A n)) ∧ M.A n=(Change.act ⟨f,Z n⟩ (M.B n))) ∧
    (∀ {n m} (h:n ≤ m), Horizon.take (M.rise h) (D m)=D n ∧ Horizon.take (M.rise h) (Z m)=Z n):= by
  let t (n:ℕ):=(C.c n).g; let f(n:ℕ):=(Change.undo _ (C.good n)).g
  let D (n:ℕ):=(C.c n).Z; let Z (n:ℕ):=(Change.undo _ (C.good n)).Z
  have ht n : t n=t 0:= congrArg Change.g (C.matched (Nat.zero_le n))
  have hz n : f n=f 0:= by unfold f Change.undo; simp only; congr 1; exact ht n
  have hu n : (⟨f 0,Z n⟩ : Change ℝ (M.J n))=Change.undo _ (C.good n) := Change.ext (hz n).symm rfl
  have hd n : (⟨t 0,D n⟩ : Change ℝ (M.J n))=C.c n:= Change.ext (ht n).symm rfl
  refine ⟨t 0,f 0,Z,D,⟨(C.good 0).ruler,reverse_good _ (C.good 0).ruler⟩,compose_reverse_apply _ (C.good 0).ruler,reverse_compose_apply _ (C.good 0).ruler,?_,?_⟩
  · intro i
    have h:=C.good i
    refine ⟨(hu i).symm ▸ (Change.Good.undoes _ h), (hd i).symm ▸ h,?_,?_,?_,?_⟩
    · rw [← hz i]; exact congrArg Change.Z (Change.compose_undo_left _ h)
    · rw [← ht i]; exact congrArg Change.Z (Change.compose_undo_right _ h)
    · rw [hd,C.answers]
    rw [hu,C.answers,Change.undo_action_left]
  intro i j h
  have he : Horizon.take (M.rise h) (D j) = D i := congrArg Change.Z (C.matched h)
  refine ⟨he,?_⟩
  have hQ:= Horizon.Coherent.sym_inverse _ (H.sensors h) (C.good j)
  change Horizon.take (M.rise h) (Change.undo _ (C.good j)).Z = (Change.undo _ (C.good i)).Z
  trans (Change.undo _ (Horizon.Coherent.good _ (H.sensors h) (C.good j))).Z
  · exact congrArg Change.Z hQ
  simp_rw [C.matched h] -- dependent proof
end YM.RG11.Bridge
