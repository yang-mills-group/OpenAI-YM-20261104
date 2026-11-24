import YM.Integration.FVA1Physical.Wilson.BoundaryRows

/-! A true pair of disjoint, separately testable boundary perturbations, with
the same joint posterior in all factors. Its connected logarithm is an
authentic two-insertion response. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Set MeasureTheory Lattice RG YM.Wilson Tree Push.BetaTransport Pressure
open RGComparison.Core16 RGComparison.Core16.Descent
open MSbar MSbar.Rolling MSbar.Midpoint MSbar.Wave Push Push.Uniform Exterior
open scoped Classical BigOperators
variable {G : Gauge} {n c f : Side} {S : StepData c f} (F : Forest S.ratio) (p : Descent n f)

theorem gain_split (β : ℕ → ℝ) (U V W Z : Config G c)
    (split : ∀ e, (V e=U e ∧ Z e=W e) ∨ (W e=U e ∧ Z e=V e))
    (t : (push S F p).Tags) (x : Fields G (push S F p)) :
    boundaryGain (push S F p) β U Z t x =
      boundaryGain (push S F p) β U V t x * boundaryGain (push S F p) β U W t x := by
  let d := push S F p
  have all (Y : Config G c) : varyBonds Finset.univ U Y = Y := by funext e; simp [varyBonds]
  have repr (Y : Config G c) := (all Y) ▸ gain_at_bonds F p β Finset.univ U Y t x
  rw [repr Z,repr V,repr W,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  rcases split e with ⟨l,r⟩|⟨l,r⟩ <;> simp only [linkGain,l,r,sub_self,mul_zero,Real.exp_zero,one_mul,mul_one]

variable (d : Descent n c)
def jointBoundaryRead (β : ℕ → ℝ) (U V W : Config G c) :=
  (∑ t, ∫ x, d.integrand β t 1 U x * (boundaryGain d β U V t x * boundaryGain d β U W t x) ∂d.measure G) /
    massAt d β U

def connectedPair (β : ℕ → ℝ) (U V W : Config G c) :=
  Real.log (jointBoundaryRead d β U V W / (boundaryRead d β U V * boundaryRead d β U W))

theorem physical_pair_pressure (h : (push S F p).OK G) (β : ℕ→ℝ) (U V W Z : Config G c)
    (split : ∀ e, (V e=U e ∧ Z e=W e) ∨ (W e=U e ∧ Z e=V e)) :
    let D := push S F p
    connectedPair D β U V W = (Real.log (D.vacuum β Z) - Real.log (D.vacuum β W)) -
      (Real.log (D.vacuum β V) - Real.log (D.vacuum β U)) := by
  intro D
  have pair : jointBoundaryRead D β U V W = boundaryRead D β U Z := by
    have equal (t : D.Tags) (x : Fields G D) : boundaryGain D β U V t x * boundaryGain D β U W t x =
        boundaryGain D β U Z t x := (gain_split F p β U V W Z split t x).symm
    unfold jointBoundaryRead boundaryRead
    simp_rw [equal]
  rw [connectedPair,pair,boundary_read_eq D h,boundary_read_eq D h,boundary_read_eq D h]
  have pos T := (D.positive β h T).ne'
  rw [Real.log_div (div_ne_zero (pos Z) (pos U)) (mul_ne_zero (div_ne_zero (pos V) (pos U)) (div_ne_zero (pos W) (pos U))),
    Real.log_mul (div_ne_zero (pos V) (pos U)) (div_ne_zero (pos W) (pos U)),
    Real.log_div (pos Z) (pos U),Real.log_div (pos V) (pos U),Real.log_div (pos W) (pos U)]
  ring

private theorem field_unchanged {e : Bond c} (g : ℝ) (x y : Positions (Primary c G))
    (quiet : panel G c y e=0) : palace (g • (x+y)) e=palace (g • x) e := by
  unfold palace
  rw [map_smul,map_add,map_smul]
  change G.lieExp (g • (panel G c x e + panel G c y e)) * 1 = G.lieExp (g • panel G c x e) * 1
  rw [quiet,add_zero]

/-- A held field variation at one bond and an arbitrary remote field are disjoint
in the true exponential coordinates. All colors of all remote bonds are allowed. -/
theorem chart_split (g b : ℝ) (x v : Positions (Primary c G)) (e : Bond c) (col : G.ColorIndex) (r : ℕ) (hr : 0<r)
    (far : ∀ j, v j ≠ 0 → r ≤ separation e.1 (Measuring.chart c G j)) :
    let H := b • bolt (primary e col)
    let U := palace (g • x)
    let V := palace (g • (x+H))
    let W := palace (g • (x+v))
    let Z := palace (g • ((x+H)+v))
    ∀ j, (V j=U j ∧ Z j=W j) ∨ (W j=U j ∧ Z j=V j) := by
  intro H U V W Z j
  by_cases hj : j=e
  · subst j
    have zeroV : panel G c v e=0 := by
      ext k
      change v (primary e k)=0
      by_contra hh
      have remote := far (primary e k) hh
      change r ≤ separation e.1 e.1 at remote
      simp only [separation_self] at remote
      omega
    exact Or.inr ⟨field_unchanged g x v zeroV,field_unchanged g (x+H) v zeroV⟩
  have hh : panel G c H j=0 := by
    dsimp only [H]
    rw [map_smul,←brand e col,edges,Pi.smul_apply,Pi.single_eq_of_ne hj,smul_zero]
  refine Or.inl ⟨field_unchanged g x H hh,?_⟩
  change palace (g • ((x+H)+v)) j=palace (g • (x+v)) j
  rw [add_right_comm]
  exact field_unchanged g (x+v) H hh

end YM.Integration.FVA1Physical.Wilson
