import YM.Integration.WilsonMaxwellThermometerReflectedFirstPrice
import YM.Integration.WilsonOriginalObservedRoseBornGalopNodes

/-! The two centered chiral energies on the actual finite prescription.
Their common reflected bump is elected before the cutoff-dependent signed
upper coefficients. The last first-incidence error is evaluated on this board. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalChiralPairReading
open Function Filter Set Finset MeasureTheory Lattice RG Wilson Maxwell Maxwell.Free
open XSpace XSpace.Cirrus XSpace.Normalize XSpace.Structure1 XSpace.Rose XSpace.Photo
open WilsonMaxwellThermometerLowerPointGram WilsonMaxwellThermometerLowerGramPrice
open WilsonMaxwellThermometerReflectedIncidence Table.Pairing
open WilsonMaxwellThermometerReflectedFirstPrice (filed)
open WilsonMaxwellThermometerPublicStation (aperture granted)
open WilsonMaxwellThermometerSignedWallet (board)
open Trace Trace.Pilot FVA2 FVA2.Register Spec Extraction OPE PhysicalNext.Repeat.Legato MS MS.WilsonBridge.Coupling
open scoped Classical BigOperators Topology
variable {G:Gauge}(Z:WilsonPrescription G)(a:Axis)(x:E4){I:Type}[Fintype I](b:I→Sec G 6)

def Paid (B:Bulb (site x) a)(C:ℝ)(D:I→ℝ)(M:Mesh):Prop:=
  ∀c∈M.Box,∀α:I→ℂ,
    let top:=∑i,α i • filed a x Z.scheme Z.store B (b i) M c
    ‖top‖≤∑i,‖α i‖*D i ∧ ∀z:occupied G a x,∀y:Bool→ℂ,∀fee:ℝ,
      ‖(y-top)-reassemble a x (Gram a x Z.scheme Z.store B M c) z‖≤fee →
        ‖token a x z‖≤C*(‖y‖+(∑i,‖α i‖*D i)+fee)

theorem original (hx:0<x a):
    ∃B:Bulb (site x) a,∃C:ℝ,∃D:I→ℝ,0<C ∧ (∀i,0≤D i) ∧
      ∀ᶠ M in Front,Paid Z a x b B C D M:=by
  classical
  obtain ⟨B,C,hC,gram⟩:=WilsonMaxwellThermometerReflectedIncidence.original a x Z.scheme Z.store hx
  choose D hD price using fun i=>WilsonMaxwellThermometerReflectedFirstPrice.bounded a x Z.scheme Z.store B (b i)
  refine ⟨B,C,D,hC,hD,?_⟩
  filter_upwards [gram,eventually_all.2 price] with M inverse bounds
  intro c hc α top
  have topPrice:‖top‖≤∑i,‖α i‖*D i:=by
    change ‖∑i,α i • filed a x Z.scheme Z.store B (b i) M c‖≤_
    apply (norm_sum_le ..).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (bounds i c hc) (norm_nonneg _)
  refine ⟨topPrice,?_⟩
  intro z y fee delta
  apply (inverse c hc z).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  calc
    _≤‖y-top‖+‖(y-top)-reassemble a x (Gram a x Z.scheme Z.store B M c) z‖:=by
      simpa only [sub_sub_cancel] using norm_sub_le (y-top)
        ((y-top)-reassemble a x (Gram a x Z.scheme Z.store B M c) z)
    _≤_:=add_le_add ((norm_sub_le ..).trans (add_le_add le_rfl topPrice)) delta

theorem hearing (R:Run G)(hx:0<x a)(o:Extraction.Order)(U:Filter (ℕ×ℕ))(prior:U≤o.fuse)
    (s:ℝ→ℕ)(small:Tendsto (aperture R s) trail (𝓝 0)):
    ∃B:Bulb (site x) a,∃C:ℝ,∃D:I→ℝ,0<C ∧ (∀i,0≤D i) ∧
      ∀ᶠ w:ℝ×(ℕ×ℕ) in trail.curry U,
      let M:=board R (s w.1) w.1 w.2.2
      Z.store.Meets Z.scheme M 6 ∧ Paid Z a x b B C D M:=by
  obtain ⟨B,C,D,hC,hD,bill⟩:=original Z a x b hx
  have mesh:=WilsonSeparatedOriginalThermometerDetectorMesh.reporting R trail o U prior s
    (aperture R s) (granted R s) small
  have fits:∀ᶠ M in Front,Z.store.Meets Z.scheme M 6:=
    (Z.store.nested_solution Z.scheme 6 Cirrus.frontier).2.mono fun _ h=>h.1
  exact ⟨B,C,D,hC,hD,mesh.eventually (fits.and bill)⟩

end YM.Integration.WilsonPhysicalChiralPairReading
