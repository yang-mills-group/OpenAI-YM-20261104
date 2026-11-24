import YM.Integration.WilsonOriginalObservedRoseBornMeasured
import YM.Integration.WilsonOriginalObservedRoseBornGround
import YM.Integration.WilsonOriginalObservedRoseKineticGround

/-! Separate the physical engineering multiplier from the accuracy of the appointed independent ground and slope. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseBornMeter
open Finset Filter PowerSeries Lattice Wilson Maxwell XSpace XSpace.Rose XSpace.Structure1 XSpace.Cirrus XSpace.Normalize
open FVA2 FVA2.Register FVA2.Scale MS MS.WilsonBridge.Coupling
open WilsonOriginalObservedRoseBornLedger (center debit truncation)
open WilsonOriginalObservedRoseBornMeasured (mismatch)
open WilsonOriginalObservedRoseBornPosition (Balance)
open WilsonOriginalObservedRoseBornSlope (ground coefficient)
open WilsonMaxwellThermometerFiniteTangent (credit)
open WilsonMaxwellThermometerOriginal (lower)
open scoped Classical
variable {G:Gauge}(Z:WilsonPrescription G){Y:Type}[Fintype Y](μ:Y→ℂ)(r:ℝ)(points:Y→Sample 3)(rows:Y→Badge→ℂ)
    (m:Mesh)(u:Sec G 6)(P Q:Module.End ℂ (Sec G 4))
local notation "a₀"=>credit Z.scheme Z.criterion m u (P (lower G)) (Q (lower G))
local notation "a₁"=>coeff 1 (Detector Z.scheme Z.criterion m)
local notation "s₀"=>ground Z μ points
local notation "s₁"=>coefficient Z μ points

theorem original (δ:ℝ)(g:ℕ→ℝ)(N last:ℕ)(live:last≤N)(raw:ℂ)(earned:ℝ)
    (book:Balance Z μ r points g N rows raw earned)(positive:0<g last)(small:‖(g last:ℂ)‖≤1)
    (refunded:‖(a₀)/(g last:ℂ)‖≤2*δ)(slope:‖(a₁)-((c_T Z.criterion:ℝ):ℂ)‖≤δ):
    let t:=g last
    let fee:=truncation Z.scheme (V:=Z.store) μ points (tag G) 1 (t:ℂ)
    |raw.re-(c_T Z.criterion:ℝ)*t-mismatch Z μ r points rows m u P Q t|≤earned+fee+3*δ*t:=by
  intro t fee
  let d:=debit Z.scheme (V:=Z.store) μ r points (tag G) 1 (t:ℂ) rows
  let c:=center Z.scheme (V:=Z.store) μ points (tag G) 1 (t:ℂ)
  have bound:|raw.re-c.re-d.re|≤earned+fee:=by
    have h:= (book 1 last live small).1
    exact (Complex.abs_re_le_norm (raw-c-d)).trans h
  have centered:c.re=(s₀).re+t*(s₁).re:=by
    have e:=(WilsonOriginalObservedRoseBornSlope.original Z μ points m t).2
    have finite:WilsonMaxwellThermometerKineticCoordinate.printed Z m 1 t=
        WilsonMaxwellThermometerKineticCoordinate.ground Z m+(a₁).re*t:=by
      simp [WilsonMaxwellThermometerKineticCoordinate.printed,WilsonMaxwellThermometerKineticCoordinate.ground,
        Fin.sum_univ_two]
    rw [finite] at e
    change c.re-_= _ at e
    linarith only [e]
  have pay:|(a₀).re|≤2*δ*t:=by
    rw [norm_div,Complex.norm_real,Real.norm_of_nonneg positive.le] at refunded
    exact (Complex.abs_re_le_norm _).trans ((div_le_iff₀ positive).mp refunded)
  have unit:|(a₁).re-(c_T Z.criterion:ℝ)|≤δ:=(Complex.abs_re_le_norm ((a₁)-((c_T Z.criterion:ℝ):ℂ))).trans slope
  have paidSlope:|t*((a₁).re-(c_T Z.criterion:ℝ))|≤t*δ:=by
    rw [abs_mul,abs_of_pos positive]
    exact mul_le_mul_of_nonneg_left unit positive.le
  have exact:raw.re-(c_T Z.criterion:ℝ)*t-mismatch Z μ r points rows m u P Q t=
      (raw.re-c.re-d.re)+(a₀).re+t*((a₁).re-(c_T Z.criterion:ℝ)):=by
    change _-(d.re+_+_) = _
    rw [centered]
    ring
  rw [exact]
  calc
    _≤(|raw.re-c.re-d.re|+|(a₀).re|)+|t*((a₁).re-(c_T Z.criterion:ℝ))|:=
      (abs_add_le ..).trans (add_le_add_left (abs_add_le ..) _)
    _≤((earned+fee)+2*δ*t)+t*δ:=add_le_add (add_le_add bound pay) paidSlope
    _= _ :=by ring

end YM.Integration.WilsonOriginalObservedRoseBornMeter
