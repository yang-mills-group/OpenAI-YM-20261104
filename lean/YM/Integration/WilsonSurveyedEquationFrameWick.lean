import YM.Integration.WilsonSurveyedEquationFrameBasis
import YM.Integration.WilsonPositionProgramTrialPublicJointFourHorizons

/-! The actual survey Wick subtraction consumes at least two curvature slots.
At engineering height at most seven the full invariant correction is a scalar. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonSurveyedEquationFrameWick
open Source Source.Drops WilsonLimitConstruction Finset Finsupp MvPolynomial Next.Rank.Normal XSpace XSpace.Contraction Labels
open scoped BigOperators Pointwise
variable {ι : Type*}

private def room (b : ι → ℕ) (d k : ℕ) : Submodule ℂ (poly ι) :=
  MvPolynomial.restrictSupport ℂ {a | Finsupp.weight b a + k ≤ d}

private lemma view (b : ι → ℕ) (d k : ℕ) (p : poly ι) :
    p ∈ room b d k ↔ ∀a ∈ p.support, Finsupp.weight b a + k ≤ d :=
  MvPolynomial.mem_restrictSupport_iff ..

private lemma cheaper {b : ι → ℕ} {d e k : ℕ} (h : d ≤ e) :
    room b d k ≤ room b e k := MvPolynomial.restrictSupport_mono _ fun _ ha => le_trans ha h

private lemma tagged {b : ι → ℕ} {d k : ℕ} {p : poly ι} (i : ι) (hp : p ∈ room b d k) :
    MvPolynomial.X i * p ∈ room b (d + b i) k := by
  classical
  rw [view]
  intro a ha
  obtain ⟨x,hx,y,hy,rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ ha)
  change x ∈ (monomial (single i 1) (1:ℂ)).support at hx
  have eq := Finset.mem_singleton.mp (support_monomial_subset hx)
  subst x
  simpa [Finsupp.weight_single,add_assoc,add_comm,add_left_comm] using Nat.add_le_add_right ((view _ _ _ _).mp hp y hy) (b i)

private lemma clipped {b : ι → ℕ} (floor : ∀i,2 ≤ b i) (v : ι → ℂ)
    {p : poly ι} {d : ℕ} (hp : p ∈ weightBound b d) : slit v p ∈ room b d 2 := by
  classical
  rw [p.as_sum,map_sum]
  apply Submodule.sum_mem
  intro a ha
  rw [slit,mkDerivation_monomial,Finsupp.sum]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro i hi
  rw [smul_eq_mul,mul_comm,MvPolynomial.C_mul']
  apply Submodule.smul_mem
  rw [view]
  intro x hx
  have eq := Finset.mem_singleton.mp (support_monomial_subset hx)
  subst x
  have pos : 1 ≤ a i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
  have le : Finsupp.single i 1 ≤ a := Finsupp.single_le_iff.mpr pos
  have id := congrArg (Finsupp.weight b) (tsub_add_cancel_of_le le)
  have total := (bounded b).mp hp a ha
  simp only [map_add,Finsupp.weight_single,one_smul] at id
  have small := floor i
  omega

private lemma expense (b : ι → ℕ) (floor : ∀i,2 ≤ b i) (C : Cov ι)
    {d : ℕ} {p : poly ι} (hp : p ∈ weightBound b d) : milk C p - p ∈ room b d 4 := by
  classical
  let T : Module.End ℂ (poly ι) := milk C - LinearMap.id
  change T p ∈ _
  suffices pay : ∀a : ι →₀ ℕ, ∀c : ℂ, T (monomial a c) ∈ room b (weight b a) 4 by
    rw [p.as_sum,map_sum]
    exact Submodule.sum_mem _ fun a ha => cheaper ((bounded b).mp hp a ha) (pay _ _)
  intro a c
  apply Extra.FD.per_factor a
  · change milk C (MvPolynomial.C c) - MvPolynomial.C c ∈ _
    rw [fine,sub_self]
    exact Submodule.zero_mem _
  intro u i hu
  change milk C (monomial (u + single i 1) c) - monomial (u + single i 1) c ∈ _
  rw [monomial_add_single,pow_one,mul_comm (monomial u c),feeds]
  rw [show X i * milk C (monomial u c) + slit (C.cov i) (milk C (monomial u c)) -
      X i * monomial u c = X i * (milk C (monomial u c) - monomial u c) +
      slit (C.cov i) (milk C (monomial u c)) by ring]
  simp only [map_add,Finsupp.weight_single,one_smul]
  apply Submodule.add_mem
  · exact tagged i hu
  · have cut := clipped floor (C.cov i) (wick_bound b C (has_self b u c))
    rw [view] at cut ⊢
    intro x hx
    have hi := cut x hx
    have fh := floor i
    omega

variable {G : Gauge} {H : Hol G} {h : ℕ}

theorem lower (A : Survey G H h) (z : ℝ) (p : Label G h) :
    ∃ q : Label G (h - 4), A.insertW z p - p = raiseLabel G (Nat.sub_le h 4) q := by
  let s := A.insertW z p - p
  have cost := expense (generation (G:=G)) (fun i => by simp [generation]) (A.selfCov z) p.property.1
  have sub : s.val ∈ limited G (h - 4) := by
    change s.val ∈ weightBound generation _
    rw [bounded]
    intro x hx
    have wh := (view _ _ _ _).mp cost x hx
    omega
  exact ⟨⟨s.val,sub,s.property.2⟩,rfl⟩

theorem scalar (F : Frame G (h - 4)) (A : Survey G H h) (z : ℝ) (p : Label G h) (simple : G.Simple)
    (rank : h ≤ 7) : ∃c : ℂ, A.insertW z p = p + c • Labels.unit G h := by
  obtain ⟨q,eq⟩ := lower A z p
  obtain ⟨c,hc⟩ := WilsonPositionProgramTrialPublicJointFourHorizons.scalar F simple (by omega) q
  refine ⟨c,?_⟩
  rw [hc,map_smul] at eq
  rw [sub_eq_iff_eq_add] at eq
  calc
    A.insertW z p = c • Labels.unit G h + p := eq
    _ = _ := add_comm ..

end YM.Integration.WilsonSurveyedEquationFrameWick

