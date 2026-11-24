import YM.Integration.WilsonMaxwellThermometerNominatedGroundWeights
import YM.Integration.WilsonCenteredCompactBooking

/-! Within-cell integrals use the authentic three independently sampled Wilson
sites. Each face is evaluated on the same field before any posterior is taken. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerNominatedGroundCell
open Set Finset Function Filter MeasureTheory Lattice Wilson Labels RG Source PhysicalNext.Repeat.Legato RG17
open OPE Table Spec PhysMS PhysMS.Frame Maxwell Maxwell.Free XSpace XSpace.Rose
open Marker QuadraticLocal Primitives.GCC.Anchor WilsonThermometerCenteredAlgebra
open WilsonMaxwellThermometerNominatedGroundPurse WilsonMaxwellThermometerNominatedGroundWeights
open WilsonCenteredPhysicalPanel
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G)
local notation "J₀" => Stock.census (Fin 3)

def mode (s:Finset (Fin 3)):(J₀).Mode:=⟨s,Finset.mem_univ _⟩

def modes:Finset (Fin 3)≃(J₀).Mode where
  toFun:=mode
  invFun:=fun s=>s.val
  left_inv:=fun _=>rfl
  right_inv:=fun _=>rfl

theorem taken (φ:Test 3) {T:Type} [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
    (χ:Points 3→T) (hc:Measurable χ) (Y:T→Finset (Fin 3)→ℂ):
    φ.applyTo (fun x=>∑s:Finset (Fin 3),WilsonThermometerCenteredAlgebra.weight (policy R x) (mode s)*Y (χ x) s)=
      ∑o:T,∑s:Finset (Fin 3),payment R φ χ o (mode s)*Y o s:=by
  let item (o:T) (s:Finset (Fin 3)) (x:Points 3):=(χ ⁻¹' {o}).indicator
    (fun t=>φ t*WilsonThermometerCenteredAlgebra.weight (policy R t) (mode s)) x
  have ok (o:T) (s:Finset (Fin 3)):Integrable (item o s):=
    (φ.smearing (regular R (mode s))).indicator (hc (measurableSet_singleton _))
  have split (x:Points 3):φ x*(∑s:Finset (Fin 3),WilsonThermometerCenteredAlgebra.weight (policy R x) (mode s)*Y (χ x) s)=
      ∑o:T,∑s:Finset (Fin 3),item o s x*Y o s:=by
    rw [Finset.sum_eq_single (χ x),Finset.mul_sum]
    · apply Finset.sum_congr rfl
      intro s _
      rw [show item (χ x) s x=φ x*WilsonThermometerCenteredAlgebra.weight (policy R x) (mode s) by
        exact Set.indicator_of_mem (show x∈χ ⁻¹' {χ x} from rfl) _]
      ring
    · intro o _ hn
      exact Finset.sum_eq_zero fun s _=>by
        rw [show item o s x=0 by exact Set.indicator_of_notMem (show x∉χ ⁻¹' {o} from fun h=>hn (Eq.symm h)) _,zero_mul]
    · intro h;exact (h (Finset.mem_univ _)).elim
  change (∫x,φ x*_)=_
  simp_rw [split]
  rw [integral_finsetSum _ (fun o _=>integrable_finsetSum _ (fun s _=>(ok o s).mul_const (Y o s)))]
  refine Finset.sum_congr rfl fun o _=>?_
  rw [integral_finsetSum _ (fun s _=>(ok o s).mul_const (Y o s))]
  exact Finset.sum_congr rfl fun s _=>integral_mul_const _ _

local notation "sites" => WilsonCenteredCompactBooking.site
local notation "μ" => WilsonCenteredCompactBooking.mass

theorem actual (φ:Test 3):
    ∃ψ:Test 3,∃B:ℝ,1≤B ∧ (∀x:Points 3,ψ x=(‖ψ x‖:ℂ) ∧ ‖φ x‖≤‖ψ x‖) ∧
      ∀(r:ℝ)(z:ℕ×ℕ),
        let c:=fun (o:Sites R z 3) (s:Finset (Fin 3))=>ratio R φ ψ (sites R r z) o (mode s)
        (∀o,∑s,‖c o s‖≤8*B) ∧
        ∀Y:Sites R z 3→Finset (Fin 3)→ℂ,
        φ.applyTo (fun x=>∑s:Finset (Fin 3),WilsonThermometerCenteredAlgebra.weight (policy R x) (mode s)*Y (sites R r z x) s)=
          ∑o,μ R ψ r z o*(∑s,c o s*Y o s):=by
  obtain ⟨ψ,B,bill,cover,bought⟩:=WilsonMaxwellThermometerNominatedGroundWeights.original R φ
  refine ⟨ψ,B,bill,cover,fun r z=>?_⟩
  have legal:Measurable (sites R r z:Points 3→Sites R z 3):=by
    apply measurable_to_countable
    intro o
    exact WilsonCenteredCompactBooking.measurable_cell R r z (sites R r z o)
  have eq (o:Sites R z 3):
      WilsonSeparatedOriginalThermometerCells.weight ψ (sites R r z) o=μ R ψ r z o:=
    integral_indicator (WilsonCenteredCompactBooking.measurable_cell R r z o)
  refine ⟨fun o=>?_,fun Y=>?_⟩
  · exact (Equiv.sum_comp modes (fun s=>‖ratio R φ ψ (sites R r z) o s‖)).le.trans ((bought _ legal o).2)
  · rw [taken R φ _ legal Y]
    refine Finset.sum_congr rfl fun o _=>?_
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [←mul_assoc,←eq,(bought _ legal o).1 (mode s)]

end YM.Integration.WilsonMaxwellThermometerNominatedGroundCell
