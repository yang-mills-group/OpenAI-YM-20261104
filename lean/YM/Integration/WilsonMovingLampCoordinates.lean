import YM.Integration.WilsonMovingSectionLamp

/-! Every genuine lamp has finitely many physical contact links. Its complete
mixed Taylor row, after repeated contacts have been identified, is the Taylor
series of the original group-field observable on the complete torus. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingLampCoordinates
open Function Lattice Exterior Wilson Stationary Precision RG Push.Uniform Bloch
open RGComparison.Core16 RGComparison.Core16.Spool RGComparison.Core16.Lumen
open FormalBulk08 Jets
open scoped Classical ContDiff BigOperators Topology

theorem unit (G : Gauge) {I : Type} [Fintype I] (s : Wire G I) :
    tint G I (Jets.dotI s) = Lumen.one s := by
  change Lumen.vector (Jets.dotI s) = _
  have h := (Lumen.repr (G:=G) (Jets.dotI s)).symm
  simpa [Jets.dotI, Pi.single_apply, ite_smul] using h

theorem tensor (G : Gauge) {I : Type} [Fintype I] (q : (I → G.Color) → ℝ) (n : ℕ) :
    (∑ a : Fin n → Wire G I, MvPolynomial.C (Tensor.coeff q n 0 (fun j => Lumen.one (a j))) *
      ∏ j, MvPolynomial.X (a j)) =
      PowerSeries.coeff n (Jets.paste (fun x => q (Lumen.vector x))) := by
  rw [← WilsonMovingTaylorConvention.coefficient, WilsonMovingTaylorConvention.tensor]
  apply Finset.sum_congr rfl
  intro a _
  congr 2
  change Tensor.coeff q n 0 _ = Tensor.coeff (q ∘ (tint G I)) n 0 _
  have d := (tint G I).iteratedFDerivWithin_comp_right q uniqueDiffOn_univ
    (x:=0) (Set.mem_univ _) n
  simp only [Set.preimage_univ, iteratedFDerivWithin_univ, map_zero] at d
  simp only [Tensor.coeff, d, smul_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    Function.comp_apply, ContinuousLinearEquiv.coe_coe, unit]

variable {G : Gauge} {I : Type} [Fintype I] (J : I → Lamp G)

def slot {n : Side} (o : I → Site n) (u : Wire G (Slice J)) : Primary n G :=
  (((legs J o u.1).1, Exterior.coord (legs J o u.1).2),u.2)

def shape (part : Bool) (w : Slice J → G.Color) : ℝ :=
  look part (exhibit J (fun i => G.lieExp (w i)))

theorem field {n : Side} (o : I → Site n) (part : Bool) (x : Positions (Primary n G)) :
    shape J part (Lumen.vector (x ∘ slot J o)) =
      look part (tally J o (represent ((tint G (Body 1 n)) x))) := by
  rw [← exhibition J o]
  unfold shape
  apply congrArg (fun z => look part (exhibit J z))
  funext i
  exact (Work.F03.represent_link ((tint G (Body 1 n)) x) (legs J o i)).symm

/-- All independent physical directions and both real components of the
original signed source; a coincidence of two sites causes the original
variable rename, without deleting either insertion. -/
theorem issued {n : Side} (o : I → Site n) (part : Bool) (p : ℕ)
    (smooth : ContDiffAt ℝ ∞ (shape J part) 0) :
    MvPolynomial.rename (slot J o)
      (∑ a : Fin p → Wire G (Slice J),
        MvPolynomial.C (Tensor.coeff (shape J part) p 0 (fun j => Lumen.one (a j))) *
          ∏ j, MvPolynomial.X (a j)) =
      PowerSeries.coeff p (Jets.paste (fun x : Positions (Primary n G) =>
        look part (tally J o (represent ((tint G (Body 1 n)) x))))) := by
  rw [tensor]
  have h : ContDiffAt ℝ ∞ (fun x => shape J part (Lumen.vector x)) 0 := by
    change ContDiffAt ℝ ∞ ((shape J part) ∘ (tint G (Slice J))) 0
    apply ContDiffAt.comp
    · simpa using smooth
    · fun_prop
  rw [← WilsonMovingTaylorConvention.coefficient]
  rw [WilsonMovingTaylorConvention.occupied (slot J o) _ h]
  simp_rw [field]

end YM.Integration.WilsonMovingLampCoordinates
end
