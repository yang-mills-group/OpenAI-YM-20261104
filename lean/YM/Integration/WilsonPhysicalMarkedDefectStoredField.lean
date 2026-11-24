import YM.Integration.FilteredWilsonProduct
import YM.Integration.IntrinsicProductLinearity
import YM.RG16.Unmasked.Bind

/-! The original cutoff field of the reporting coefficient, resolved into
the actual placed physical basis stencils. In particular, a product takes
the complete occupied subset at birth. The same stored Wilson coefficient
is evaluated pointwise, before any thermal estimate or absolute value. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalMarkedDefect.StoredField

open Function Finset Lattice Wilson RG Cells Source Labels
open Extra.Histories Relay Bid RG16.Literal Trace.Physical.GermGraph
open OPE OPE.Orbits OPE.Cards StressFlux.Matching Frontier6.Road
open EngineeringWeightedReadout WilsonWholeLimit ActualFoundryDetectorSource
open Trace.Pilot MultilinearCellCapture FilteredIntrinsicGramReadout IntrinsicGramReadout
open scoped Classical BigOperators Topology

variable {G : Gauge} (C : Family G) (N p : ℕ)

/-- The specified UV amplitude, including the actual terminal inverse of
the calibrated family, the physical threshold and the lattice spacing. -/
def amplitude {k : ℕ} (v : C.label k) (j : (C.labels.level k).Index) : ℂ :=
  ((C.S.a N : ℂ)^k)⁻¹ * ((C.labels.level k).scaled (C.path.levels.clock.threshold N)⁻¹
    ((C.factory k N p).terminal.symm v)) j

theorem placed {k : ℕ} (v : C.label k) (o : Site (C.side N p)) (U : Config G (C.side N p)) :
    C.O N p v o U = ∑ j : (C.labels.level k).Index, amplitude C N p v j *
      (C.localSection k).places (Pi.single j 1) o U := by
  let a := (C.labels.level k).scaled (C.path.levels.clock.threshold N)⁻¹ ((C.factory k N p).terminal.symm v)
  let evalu : (C.labels.level k).Coeff →ₗ[ℂ] ℂ :=
    (MvPolynomial.aeval (entry (S:=(C.localSection k).stencil) (expandAt o U))).toLinearMap.comp (C.localSection k).evalC
  have ea : (∑ j, a j • Pi.single j (1:ℂ)) = a := by
    ext j
    simp [Pi.smul_apply,Pi.single_apply]
  change ((C.S.a N : ℂ)^k)⁻¹ * evalu a = _
  nth_rw 1 [← ea]
  simp only [map_sum,map_smul,smul_eq_mul,Finset.mul_sum]
  exact sum_congr rfl fun j _ => (mul_assoc _ _ _).symm

variable {I : Type} [Fintype I] {d : I → ℕ}
abbrev AxisAt (k : ℕ) := (t : Fin (k+1)) × (C.labels.level t.val).Index
abbrev Choice (d : I → ℕ) := (i : I) → AxisAt C (d i)
abbrev Grades (d : I → ℕ) := (i : I) → (t : Fin (d i+1)) → C.label t.val

def weight (q : Grades C d) (a : Choice C d) : ℂ := ∏ i, amplitude C N p (q i (a i).1) (a i).2

def basisProduct (o : I → Site (C.side N p)) (a : Choice C d) (U : Config G (C.side N p)) : ℂ :=
  ∏ i, (C.localSection (a i).1.val).places (Pi.single (a i).2 1) (o i) U

def product (q : Grades C d) (o : I → Site (C.side N p)) (U : Config G (C.side N p)) : ℂ :=
  ∏ i, ∑ j : Fin (d i+1), C.O N p (q i j) (o i) U

theorem expand (q : Grades C d) (o : I → Site (C.side N p)) :
    product C N p q o = ∑ a : Choice C d, weight C N p q a • basisProduct C N p o a := by
  funext U
  simp only [product,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,weight,basisProduct,← Finset.prod_mul_distrib]
  let term (i : I) (z : AxisAt C (d i)) := amplitude C N p (q i z.1) z.2 *
    (C.localSection z.1.val).places (Pi.single z.2 1) (o i) U
  change (∏ i, ∑ j, C.O N p (q i j) (o i) U) = ∑ a : Choice C d, ∏ i, term i (a i)
  rw [← Fintype.prod_sum term]
  refine prod_congr rfl fun i _ => ?_
  rw [Fintype.sum_sigma]
  exact sum_congr rfl fun j _ => placed C N p _ (o i) U

theorem basis_continuous (o : I → Site (C.side N p)) (a : Choice C d) :
    Continuous (basisProduct C N p o a) := continuous_finsetProd _ fun _ _ => SectionData.continuous_places ..

/-- The true signed, normalized readout of the very same stored, paid Q.
No total signal is assigned to any individual forced spectator. -/
theorem bank {h b J : ℕ} (law : C.Makes) (q : Grades C d) (o : I → Site (C.side N p))
    (hj : J ≤ b) (hb : b ≤ N) (w : Site (C.side J p) → ℝ) (Q : store C h p b) {fare : ℝ}
    (admitted : reads h N p b Q fare)
    (issued : Fleet C N p h b J (product C N p q o) (hj.trans hb) w Q hb) :
    ∀ U, Q.density 0 (C.localSection h) (C.path.rep N p b) U / ((C.path.rep N p b).eval U : ℂ) =
      ∑ a : Choice C d, weight C N p q a * (credit C N p h (basisProduct C N p o a) b hb U /
        ((C.path.rep N p b).eval U : ℂ)) := by
  have hfield : Continuous (product C N p q o) := continuous_finsetProd _ fun i _ =>
    continuous_finsetSum _ fun j _ => C.continuousO N p _ (q i j) (o i)
  have same := Fleet.keeps C N p h b J law (product C N p q o) hfield hj hb w Q admitted issued
  rw [expand,IntrinsicProductLinearity.credit_sum C N p h b hb _ _ (basis_continuous C N p o)] at same
  intro U
  rw [← show (∑ a : Choice C d, weight C N p q a • credit C N p h (basisProduct C N p o a) b hb) U =
      Q.density 0 (C.localSection h) (C.path.rep N p b) U from congrFun same U,
    Finset.sum_apply,Finset.sum_div]
  exact sum_congr rfl fun a _ => mul_div_assoc ..

variable {C} {S : Table C.book} {order : Extraction.Order}

/-- The specified cutoff product has exactly these grades and the actual
original source locations. The declaration is independent of the Q reported
at a later stop and includes arbitrary physical input colors. -/
theorem specified (F : Spec.Final C order S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (v : (i : I) → (Climb.Bel C.book).Field (d i))
    (t : ℝ) (j : ℕ) (x : I → Cover) :
    FilteredWilsonProduct.field F R J v t j x (N,p) =
      product C N p (d:=d) (fun i u => S.representative _ (R.cutTest u.val (d i) (J t (d i) (v i))))
        (fun i => location C.S j N p (x i)) := by
  funext U
  simp only [FilteredWilsonProduct.field,product,Finset.prod_apply,Finset.sum_apply]

end YM.Integration.WilsonPhysicalMarkedDefect.StoredField

