import YM.Integration.WilsonThermometerRegisteredCenteredSelfWeight
import YM.Integration.WilsonThermometerRegisteredCenteredSelfComponents

/-! The two signed withdrawals use at most 23 units and the true reflected components
use at most six times their largest individual tariff in the original units. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredCenteredSelfBound
open Finset Marker Primitives.GCC.Anchor WilsonThermometerCenteredScalar WilsonThermometerCenteredAlgebra
open WilsonThermometerRegisteredCenteredInvoice WilsonThermometerRegisteredCenteredSelfComponents
open Lattice PhysicalNext.Repeat.Legato XSpace Extraction WilsonSeparatedOriginalThermometerCells
open scoped BigOperators Classical
local notation "J" => Stock.census (Fin 3)

theorem duty (w:Fin 3→ℝ) (pos:∀v,0<w v) (cap:∀v,w v≤1) (F:Poly J) (means:∀v:Fin 3,‖read F {v}‖≤1):
    let d:ℂ:=restoration w F 1
    ‖d‖+‖1-d‖≤23:=by
  intro d
  let b:=restoration w F 1
  have lower:(1:ℝ)≤b:=by
    dsimp only [b,restoration]
    have nn:=Poly.nonnegative pos (properInvoice F 1-1)
    linarith
  have upper:b≤12:=by
    apply (WilsonThermometerRegisteredCenteredSelfWeight.price w pos F (S:=1) _).trans_eq (by norm_num)
    intro v
    exact (mul_le_mul_of_nonneg_right (cap v) (norm_nonneg _)).trans (by simpa only [one_mul] using means v)
  change ‖(b:ℂ)‖+‖(1:ℂ)-(b:ℂ)‖≤23
  rw [←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg (zero_le_one.trans lower),abs_of_nonpos (sub_nonpos.mpr lower)]
  linarith

def largest (price:(J).Mode→ℝ):ℝ:=Finset.univ.sup' ⟨(J).quiet,mem_univ _⟩ (fun s=>|price s|)

theorem six (F:Poly J) (means:∀v:Fin 3,‖read F {v}‖≤1) (price:(J).Mode→ℝ):
    ∑s:(J).Mode,‖WilsonThermometerNominatedConnectedStop.coefficients (properInvoice F 1) s‖*price s≤6*largest price:=by
  have bound(s:(J).Mode):|price s|≤largest price:=Finset.le_sup' (fun u=>|price u|) (mem_univ s)
  have up:∑s:(J).Mode,‖WilsonThermometerNominatedConnectedStop.coefficients (properInvoice F 1) s‖≤(6:ℝ):=by
    convert total F means using 1;norm_num
  calc
    _≤∑s:(J).Mode,‖WilsonThermometerNominatedConnectedStop.coefficients (properInvoice F 1) s‖*largest price:=
      Finset.sum_le_sum (fun s _=>mul_le_mul_of_nonneg_left ((le_abs_self _).trans (bound s)) (norm_nonneg _))
    _≤_:=by rw [←Finset.sum_mul];exact mul_le_mul_of_nonneg_right up ((abs_nonneg _).trans (bound (J).quiet))

theorem blank {G:Gauge} (R:Run G) (z:ℕ×ℕ) (r:ℝ) (profile:Test 3):
    WilsonThermometerFiniteConnectedCells.reference R z r profile (fun _=>(1:Poly J))=0:=by
  have mute(a:Finset (Fin 3)) (nz:a.Nonempty):read (1:Poly J) a=0:=by
    change (1:Poly J).part (face a)=0
    rw [Poly.one_part,if_neg (fun h=>by have h':a=∅:=congrArg Subtype.val h;exact nz.ne_empty h')]
  have zero:WilsonPositionThermometerConnected.value (read (1:Poly J))=0:=by
    unfold WilsonPositionThermometerConnected.value
    simp only [mute _ (show (univ:Finset (Fin 3)).Nonempty by decide),mute _ (show ({0,1}:Finset (Fin 3)).Nonempty by decide),
      mute _ (show ({0,2}:Finset (Fin 3)).Nonempty by decide),mute _ (show ({1,2}:Finset (Fin 3)).Nonempty by decide),
      mute _ (singleton_nonempty 0),mute _ (singleton_nonempty 1),mute _ (singleton_nonempty 2)]
    ring
  simp only [WilsonThermometerFiniteConnectedCells.reference,zero,Test.applyTo,mul_zero,MeasureTheory.integral_zero]

end YM.Integration.WilsonThermometerRegisteredCenteredSelfBound
