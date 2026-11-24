import YangMills.WilsonProof.NativeSupport.YM.Next.MAXWELL.Ends
import YM.Next.MAXWELL.Shelves

/-! At engineering cap six an invariant field is a sum of a vacuum word,
invariant two-curvature words with at most two derivatives, and cubic words.
The averaging and all three parts live in the original Maxwell polynomial. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerCapWords
open Set Function Maxwell Maxwell.Free MvPolynomial
open scoped BigOperators
variable {G : Gauge}

private theorem extracts (p : Slot G →₀ ℕ) (hp : p≠0) : ∃ i q, p=q+Finsupp.single i 1 := by
  classical
  obtain ⟨i,h⟩ : p.support.Nonempty := by simpa using hp
  have ht : Finsupp.single i 1 ≤ p := by
    intro x; by_cases he : x=i
    · subst x; rw [Finsupp.single_eq_same]; exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp h)
    simp [Ne.symm he]
  exact ⟨i,p-Finsupp.single i 1,(tsub_add_cancel_of_le ht).symm⟩

private theorem binary (p q : Slot G) (h : G.Simple) : moyenne G (X p * X q) ∈ Teams G p.1 q.1 := by
  classical
  rw [← symbol_coordinate p,← symbol_coordinate q]; simp_rw [divide,Finset.sum_mul,Finset.mul_sum,map_sum]
  apply Submodule.sum_mem; intro i _; apply Submodule.sum_mem; intro j _
  obtain ⟨t,ht⟩ := duet (flavor_pick (coordinateLeg p) _) (flavor_pick (coordinateLeg q) _) i j h
  rw [ht]; exact Submodule.smul_mem _ (t:ℂ) (in_team G _ _)

private theorem averaged {p : WickPol G} (h : Pure 3 p) : Pure 3 (moyenne G p) :=
  (distilled_eq ..).mpr ((moyenne_gloss _ 3 p).trans (congrArg _ ((distilled_eq ..).mp h)))

theorem covers (h : G.Simple) (V : Submodule ℂ (WickPol G)) (hv : 1∈V)
    (hp : ∀ j l, j+l≤2 → Teams G j l ≤ V) (ht : ∀ p, Pure 3 p → p∈V) :
    shellSector G 6 ≤ V := by
  classical
  intro p hP; obtain ⟨H,W⟩ := sector.mp hP
  rw [← paints_self W]
  rw [lowerCap,MvPolynomial.restrictSupport_eq_span] at H
  refine Submodule.span_induction (p := fun p _ => moyenne G p∈V) ?_ ?_ ?_ ?_ H
  · rintro _ ⟨x,hx,rfl⟩; change degree x ≤ 6 at hx
    by_cases hz : x=0
    · subst x; change moyenne G 1∈V; rw [paints_self fun _ => map_one _]; exact hv
    obtain ⟨i,p,rfl⟩ := extracts _ hz
    rw [weight_next] at hx
    by_cases hz : p=0
    · subst p; simp only [zero_add]; change moyenne G (X i)∈V
      rw [← symbol_coordinate,solo _ h]; exact V.zero_mem
    obtain ⟨j,p,rfl⟩ := extracts _ hz
    rw [weight_next] at hx
    by_cases hz : p=0
    · subst p; simp only [zero_add]
      rw [show MvPolynomial.monomial _ 1=X (R:=ℂ) j * X i by rw [X,X,MvPolynomial.monomial_mul,one_mul]]
      exact hp _ _ (by omega) (binary j i h)
    obtain ⟨k,p,rfl⟩ := extracts _ hz
    rw [weight_next] at hx
    by_cases hz : p=0
    · subst p; apply ht; apply averaged
      apply isWeightedHomogeneous_monomial
      simp [Finsupp.weight_single]
    obtain ⟨l,p,rfl⟩ := extracts _ hz
    rw [weight_next] at hx; omega
  · rw [map_zero]; exact V.zero_mem
  · intro x y _ _ hx hy; rw [map_add]; exact V.add_mem hx hy
  intro t y _ hy; rw [map_smul]; exact V.smul_mem _ hy

end YM.Integration.WilsonMaxwellThermometerCapWords
