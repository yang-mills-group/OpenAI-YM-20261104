import YM.Integration.WilsonUniformUnmarkedCourse

/-! The spatial vacuum remainder and the numerical kinetic reset on the
original run, with one onset for every upper cutoff and physical period.
The comparison retains the computed, field-independent partition term. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonUniformUnmarkedReclosure
open Filter Function PowerSeries Lattice RG Wilson Tree Stationary Push.Uniform Bloch Exterior Precision
open FormalBulk08 Jets Flat Reef Mesa Lava Shore Lotus Wine Bank Orb Next.Free Series
open PhysicalNext.Repeat.Legato MSbar MSbar.Heath MSbar.Rolling MSbar.Cacao MSbar.Midpoint MSbar.Bakery MSbar.Bakery.Portal
open WilsonConditionalTaylorCourseAttachment WilsonConditionalTaylorFieldBalance WilsonConditionalTaylorResetCoordinates
open WilsonMovingPolynomialPull
open scoped Classical Topology BigOperators

variable {G : Gauge} {n : Side} {I : Type} [Fintype I] {p : ℕ}

def offset (i : ℕ) (A B : Pap I) : ℝ :=
  MvPolynomial.coeff 0 (coeff i A)-MvPolynomial.coeff 0 (coeff i B)

theorem coefficient {A B : Pap I} (h : Fields p A B) {i : ℕ} (hi : i ≤ p) :
    coeff i A=coeff i B+MvPolynomial.C (offset i A B) := by
  apply components
  intro d
  rw [map_add]
  by_cases dz : d=0
  · subst d
    simp only [MvPolynomial.homogeneousComponent_zero,MvPolynomial.coeff_C,if_true,offset,map_sub]
    abel
  · rw [MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_C _ _),if_neg dz,add_zero]
    exact h i hi d (by omega)

def partition (A B : Nesting G n) (g : ℝ) (p : ℕ) : ℝ :=
  -(∑ i ∈ Finset.range (p+1),g^i*offset i A B)

theorem film {A B : Nesting G n} (h : Fields p A B) (Q : Rep G n) (g : ℝ) :
    Aqua.film Q A g p = fun x => Aqua.film Q B g p x + partition A B g p := by
  funext x
  have cell (i : ℕ) (hi : i ≤ p) :
      Lis.atlas A p i Q.path Q.clip x=Lis.atlas B p i Q.path Q.clip x+offset i A B := by
    unfold Lis.atlas MSbar.Wave.joy MSbar.Wave.tariff
    simp only [map_sub,coefficient h hi,map_add,MvPolynomial.eval_C]
    ring
  have pay : Aqua.ore Q A g p x =
      Aqua.ore Q B g p x+∑ i ∈ Finset.range (p+1),g^i*offset i A B := by
    unfold Aqua.ore
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [cell i (by have :=Finset.mem_range.mp hi;omega),mul_add]
  change Aqua.vine Q g x - Aqua.ore Q A g p x =
    Aqua.vine Q g x - Aqua.ore Q B g p x + partition A B g p
  rw [pay]
  unfold partition
  ring

theorem evaluation {a b : PowerSeries ℝ} (h : Through p a b) (g : ℝ) :
    Bakery.taste p a g=Bakery.taste p b g := by
  unfold Bakery.taste
  apply Finset.sum_congr rfl
  intro i hi
  rw [h i (by have :=Finset.mem_range.mp hi;omega)]

variable (R : Run G) (simple : G.Simple) (u : G.ColorIndex) (V : Voice G)
variable (bought : WilsonConditionalTaylorPurchase.Inventory u V R.kit)
variable (wood : ∀ j,Lodge (R.family.path.levels.clock.op j 0).patch)
variable (tags : ∀ j n,(primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices)

include bought simple in
theorem calibrated (s p m : ℕ) (hs : 6 ≤ s) (hm : 4 ≤ m) (room : p+2 ≤ m) :
    ∀ᶠ k : ℕ in atTop, ∀ N per, k ≤ N →
      (∀ j, k ≤ j → j ≤ N →
        let Q:=R.family.path.rep N per j
        let B:=placed R u wood tags N per j
        ∃ c : ℝ, Ballet.Ticket (R.family.path.levels.clock.hatBeta j) (R.family.side j per)
          (fun x=>Aqua.film Q B (Stock.cue Q.beta) p x + c) s p m) ∧
      ∀ j, k ≤ j → j < N →
        let g:=fun i=>Stock.cue (R.family.path.rep N per i).beta
        |g j/g (j+1)-Bakery.taste p (bookU (price R u wood tags N per j)) (g j)| ≤
          Mosaic.goalP (R.family.path.levels.clock.hatBeta j) p := by
  have docket:=(Qlocal.Schedule.docket_of_invoice simple R u V bought.2.2).1
  filter_upwards [docket.purse s p m hs hm room] with k budget N per kN
  obtain ⟨⟨S,law⟩,given⟩:=budget N per kN
  obtain ⟨spatial,kinetic,_⟩:=given S law
  have issue:=WilsonUniformUnmarkedCourse.issued R simple u V bought wood tags N per k p S law
  constructor
  · intro j lo hi
    let Q:=R.family.path.rep N per j
    let B:=placed R u wood tags N per j
    let g:=Stock.cue Q.beta
    refine ⟨partition (S.Poly j) B g p,?_⟩
    have h:=film (issue j lo hi).1 Q g
    exact h ▸ spatial j lo hi
  · intro j lo hi
    have h:=evaluation ((issue j lo hi.le).2 hi).1 (Stock.cue (R.family.path.rep N per j).beta)
    dsimp only
    rw [←h]
    exact kinetic j lo hi

end YM.Integration.WilsonUniformUnmarkedReclosure
