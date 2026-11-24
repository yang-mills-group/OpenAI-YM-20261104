import YM.Integration.WilsonRunFormalMarkedStep
import YM.Comparison.RG02.Order.Vacancy

/-! A primitive finite comparison of the two marked coefficient prescriptions.
The input to the physical logarithm contains its unaltered finite vacuum
polynomial. The independent conditional uses the common vacuum of all the
translated input tests; its numerator is evaluated before taking that quotient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMarkedFiniteWickDefect
open FormalBulk08 FormalBulk08.Reef FormalBulk08.Flat Lattice Laurent Bloch Exterior Wilson
open FormalBulk08.Orb FormalBulk08.Wick FormalBulk08.Series FormalBulk08.Jets
open Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision Stationary
open FormalBulk08.Mesa FormalBulk08.Kemp FormalBulk08.Lava
open Planned.PrimaryIntegral295 Place Film Carrier Source Labels
open Tree Marker Multi Comparison.RG02 Comparison.RG02.Order Primitives.GCC.Anchor
open Extra.Trajectories (connected pass_add part_sub)
open scoped BigOperators Classical

variable {G : Gauge} {K : KernelChoices} {D j t : ℕ}
variable (P : Flight j t) (L : Lodge P.patch) (W : Pot G) (ρ : ChartRatio G)
    (branches : P.patch.Branches K G) (block : 2 ≤ P.L.val)

/-- On each finite torus all translated source tests share one vacuum. After
multiplying by it the independently computed conditional is an explicit sum of
finite Gaussian Wick numerators; no division, period limit, or hypothesis on
the marked numerator enters this identity. -/
theorem numerator (Y : Anthem D G) (h l : ℕ) (f : Dawn.Studio D)
    (n : Side) (tag : (primary P.patch K n).Choices)
    (ratio : LocalRatio ρ) (order : 4 ≤ t)
    (leading : coeff 0 (Mesa.stone W (n*P.L)) = crunch (kernelP G K.penalty P.wing _)) :
    let H := Reef.ferry P branches L n
    let F := Reef.floor K P L n
    let U := Reef.flush F tag ρ (Mesa.stone W _)
    Orb.vocal H U * WilsonFormalMarkedCubature.finiteTransfer P L W ρ branches block Y h l f n tag =
      PowerSeries.C (MvPolynomial.C (Kemp.aven P.L h)) *
        ∑ x : Site P.L, Series.beam (Orb.variation H.saddle _).call
          (Series.expan (Orb.positive H U) *
           Orb.toInk H (Reef.seat F (Kemp.resite (wrap _ (lift x))
              (Kemp.banner l (Y (Dawn.throughW x D block f)) _)))) := by
  intro H F U
  have solved := Reef.consolidate P ρ branches L n ratio tag (Mesa.stone W _) leading order
  unfold WilsonFormalMarkedCubature.finiteTransfer
  rw [mul_left_comm,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  exact Orb.normalization H U solved _

section
variable {V : Type} [Fintype V] [DecidableEq V] (I : Census V) (p : ℕ)

/-- The original one-mark target in the very same external and coupling
coordinates as the physical prescription. `a` includes the required
change to threshold coordinates, independently of the Gaussian field. -/
def column (v : V) (a : ℂ) (q : ℕ → ℝ) : Grade I p :=
  Order.series I p (PowerSeries.mk fun e => Poly.send (I.fire v) (a * (q e : ℂ)))

theorem column_quiet (v : V) (a : ℂ) (q : ℕ → ℝ) :
    (column I p v a q).part (Board I p).quiet = 0 := by
  have no : I.quiet ≠ I.fire v := fun h =>
    Finset.singleton_ne_empty v (congrArg Subtype.val h.symm)
  change (column I p v a q).part (Join.pair I.quiet (indices p).quiet) = 0
  rw [column,Order.polarization]
  simp [Poly.part_send,no]

theorem reads (v : V) (a : ℂ) (q : ℕ → ℝ) {e : ℕ} (he : e ≤ p) :
    (Order.observe I p (column I p v a q) e).part (I.fire v) = a * (q e : ℂ) := by
  rw [column,Order.observation _ _ _ he,PowerSeries.coeff_mk,Poly.part_send,if_pos rfl]

/-- Multiply the independently prescribed marked polynomial by the physical
vacuum, including every pure coupling term, before subtracting from the physical
unnormalized moment. -/
def debt (x y : Grade I p) := x - Order.denominator x * Poly.pass y

/-- The exact signed defect of the physical normalized logarithm against an
independently fixed one-mark target, written in terms of their unnormalized
moment difference. -/
theorem logarithm (x y : Grade I p) (hx : UnitLeading x)
    (hy : y.part (Board I p).quiet = 0) :
    Order.logMarked x = y + connected
      (1 + (Poly.pass (-y) * inverseMass (Order.denominator x)) * debt I p x y) := by
  have hy' : (-y).part (Board I p).quiet=0 := by simpa using congrArg Neg.neg hy
  have revert : Order.denominator x * inverseMass (Order.denominator x) = 1 :=
    right_inverse ((Order.bottom_quiet x).trans hx)
  have forward : Poly.pass (-y)*Poly.pass y=1 := by
    rw [←pass_add hy' hy,neg_add_cancel,Extra.Trajectories.pass_zero]
  have rel : 1 + (Poly.pass (-y) * inverseMass (Order.denominator x)) * debt I p x y =
      Poly.pass (-y) * Order.ratio x := by
    unfold debt Order.ratio
    calc
      _ = 1 + Poly.pass (-y)*(x*inverseMass (Order.denominator x)) -
          (Poly.pass (-y)*Poly.pass y)*(Order.denominator x*inverseMass (Order.denominator x)) := by ring
      _ = _ := by rw [forward,revert];ring
  rw [rel,Comparison.RG02.Cumulants.connected_mul (Poly.pass_part _ hy') (Order.ratio_quiet hx),
    Comparison.RG02.Cumulants.connected_pass hy']
  unfold Order.logMarked
  abel

end

section
open MeasureTheory PertExtension.Series Next.SectorChange
variable {V : Type} [Fintype V] [DecidableEq V] {I : Census V}
variable {c s : Side} {S : StepData c s} {clip : Clip} {A : PathData G} {ρ' : ChartRatio G}
    (kernel : Bulk.Kernel S clip A ρ') (forest : Forest S.ratio) (tag : S.Choices)
    (menu : Bulk.Colors I G s) (exterior : Bid.Dir G c) (p : ℕ)

/-- Every coefficient of the primitive discrepancy is an original integral
over the physical forest's free variables. This formula precedes the vacuum
division and retains all physical pure, marked, and mixed modes. -/
theorem physical (y : Grade I p) (s₀ : I.Mode) (u : Order.Index p) :
    (debt I p (Bulk.Fk kernel forest tag menu exterior p) y).part (Join.pair s₀ u) =
      (u.val.card.factorial : ℂ) *
        ∫ z, Assembly.rows (Assembly.expansions menu.power (Bulk.markFn S forest menu)
          (Bulk.geometric kernel forest tag menu)) s₀ u.val.card (Bulk.translated kernel forest exterior z)
          ∂Gaussian.cloud (kernel.covariance forest tag) -
      (Order.denominator (Bulk.Fk kernel forest tag menu exterior p) * Poly.pass y).part (Join.pair s₀ u) := by
  rw [debt,part_sub,Bulk.table]

/-- The physical normalized marked logarithm minus each coefficient of the
independent finite transfer (with a separately specified real test field and
threshold conversion) is an exact signed polynomial in the primitive Gaussian
moment discrepancy. Both vacua can therefore be compared before normalization. -/
theorem observed (v : V) (a : ℂ) (q : ℕ → ℝ) {e : ℕ} (he : e ≤ p) :
    let x := Bulk.Fk kernel forest tag menu exterior p
    let y := column I p v a q
    (Order.observe I p (Order.logMarked x) e).part (I.fire v) - a * (q e : ℂ) =
      (Order.observe I p (connected (1 + (Poly.pass (-y) * inverseMass (Order.denominator x)) *
        debt I p x y)) e).part (I.fire v) := by
  intro x y
  have eqn := logarithm I p x y (Bulk.fk_unit ..) (column_quiet I p v a q)
  rw [eqn,Order.observe_add,Poly.part_plus,reads I p v a q he]
  abel

end
section
open ConnectedActivityE6 FormalBulk08.City Filter FormalBulk08.Pose FormalBulk08.Roof PhysicalNext PhysicalNext.Repeat
variable {V : Type} [Fintype V] [DecidableEq V] {I : Census V} {d : ℕ}

/-- The exact numerical change from coupling field coordinates to the
threshold coordinates of the represented Wilson density on this mesh. -/
def scale (R : Legato.Run G) (N i per : ℕ) : ℝ :=
  (R.family.path.rep N per i).p.threshold / Coat.gStep (R.family.path.rep N per i).beta

/-- The independent finite normalized conditional at a specified physical
step and actual observing period. The same threshold-scaled field is sent to
the physical stationary integral below; the original input column and affine
pullback tests come from the same fixed ultraviolet section. -/
def finite (R : Legato.Run G)
    (L : ∀ i, Lodge ((R.alloy.B.a.clock.op i 0).patch)) (a : hue G) (depth : d < D)
    (N i per : ℕ) (tag : (R.family.path.levels.clock.op i per).Choices)
    (letter : Letter (R.family.labels.level d)) (f : Dawn.Studio D)
    (b : Stationary.Link G (R.family.S.side i per)) (e : ℕ) : ℝ := by
  let P := destination R.family.path.levels N i
  let W := Dove.model R.family.path.levels L (fun k => (R.family.path.levels.blocks k 0).branches)
    R.metals.O a N (i+1)
  let y := WilsonRunFormalMarkedStep.graph R L a depth N (i+1)
  let B := scale R N i per • b
  exact MvPolynomial.eval (fun k => B k) (coeff e
    (WilsonFormalMarkedCubature.finiteTransfer P (L i) W R.metals.O
      (R.family.path.levels.blocks i 0).branches (Elm.growL R.family.path.levels i)
      (y letter) d (slots (R.family.labels.level d) letter) f (R.family.S.side i per) tag))

/-- Exact finite signed residual at the real physical step, before the
adjacent reset and before passage to the cover. The two calculations read the
same block, forest construction, branch tag and threshold-scaled coarse field.
The argument of the logarithm uses the entire original vacuum polynomial.
The input division is the inverse diagonal on the incoming external column. -/
theorem onRun (R : Legato.Run G)
    (L : ∀ i, Lodge ((R.alloy.B.a.clock.op i 0).patch)) (a : hue G) (depth : d < D)
    (N i per : ℕ) (hi : i < N) (tag : (R.family.path.levels.clock.op i per).Choices)
    (letter : Letter (R.family.labels.level d)) (f : Dawn.Studio D)
    (b : Stationary.Link G (R.family.S.side i per))
    (menu : Bulk.Colors I G (R.family.S.side (i+1) per)) (v : V) (p : ℕ) {e : ℕ} (he : e ≤ p) :
    let K := (RunFormalChain.fromRun R).step N i per hi
    let F := Lodge.forest (S := R.family.path.levels.clock.op i per) (L i)
    let x := Bulk.Fk K F tag menu (Stationary.arm G _ 1 (scale R N i per • b)) p
    let q := finite R L a depth N i per tag letter f b
    let c₀ : ℂ := ((scale R N (i+1) per : ℂ) ^ slots (R.family.labels.level d) letter)⁻¹
    let y := column I p v c₀ q
    (Order.observe I p (Order.logMarked x) e).part (I.fire v) - c₀ * (q e : ℂ) =
      (Order.observe I p (connected (1 + (Poly.pass (-y) * inverseMass (Order.denominator x)) *
        debt I p x y)) e).part (I.fire v) := by
  exact observed _ _ _ _ _ p _ _ _ he

end
end YM.Integration.WilsonMarkedFiniteWickDefect


