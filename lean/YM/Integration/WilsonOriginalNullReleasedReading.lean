import YM.Integration.WilsonOriginalNullReleasedStation
import YM.Integration.WilsonOriginalNullReleasedFrame
import YM.Integration.WilsonOriginalAdjacentMicroscopicPrice
import YM.Integration.WilsonPositionThermometerStationTransport

/-! The full true page of a fixed original cutoff field at a finer reporting
station, beginning from its measured original coordinate at the enrolled station. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullReleasedReading
open Function Filter Finset Lattice RG Wilson Labels Source Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open QuadraticLocal QuadraticLocal.Advent ConnectedActivityE6 Next.Rank.Price
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(d:ℕ)
local notation "C₀"=>R.family
local notation "Fr"=>R.family.labels.level d
local notation "levels"=>R.family.path.levels


/-- The stored section at the same star is exactly the engineering-weighted awake column. -/
theorem stored (k N p:ℕ)(v:(C₀).label d):
    ((C₀).S.a k:ℂ)^d • awake C₀ d k N p v = columns C₀ d k N p v:=by
  have nz:(((C₀).S.a k:ℝ):ℂ) ≠ 0:=Complex.ofReal_ne_zero.mpr ((C₀).S.a_pos k).ne'
  rw [awake,smul_smul,mul_inv_cancel₀ (pow_ne_zero _ nz),one_smul]

/-- The exact full fitted datum differs from the stored column only by the genuine
finite-period projection bill. Its coefficient is independent of the upper cutoff. -/
theorem reading {k N p:ℕ}(home:Opened C₀ d k p)(live:k≤N)
    (W:Rep G ((C₀).side k p))(tier:W.p=(levels).budget k)(beta:W.beta=((C₀).path.rep N p k).beta)
    (v:(C₀).label d):
    let raw:=((C₀).factory d N p).terminal.symm v
    let M:=fitting (C:=C₀) d N p k R.makes home live
    let t:=Coat.gStep W.beta/W.p.threshold
    (Fr).coeffSize ((Fr).scaled t (M raw) - ((C₀).S.a k:ℂ)^d • (Fr).scaled t (awake C₀ d k N p v)) ≤
      (2:ℝ)^WilsonOriginalAdjacentMicroscopicPrice.height R d*
        invoice (C:=C₀) d k p*stock C₀ k*(C₀).S.a k^d*(Fr).coeffSize (awake C₀ d k N p v):=by
  intro raw M t
  let cols:=columns C₀ d k N p v
  have paid:=measured_diff d N p k R.makes home.post live
    (entryOk d N p k R.makes home.post live raw)
  change (Fr).coeffSize (M raw-cols) ≤ invoice (C:=C₀) d k p*(stock C₀ k*(Fr).coeffSize cols) at paid
  have cap:=WilsonOriginalNullReleasedStation.gauge R live W tier beta
  have fee:=(WilsonOriginalNullReleasedStation.scale R d cap.1 cap.2 (M raw-cols)).trans
    (mul_le_mul_of_nonneg_left paid (by positivity))
  have eqn:((C₀).S.a k:ℂ)^d • awake C₀ d k N p v=cols:=stored R d k N p v
  have size:(Fr).coeffSize cols=(C₀).S.a k^d*(Fr).coeffSize (awake C₀ d k N p v):=by
    rw [←eqn]
    simp only [Frame.coeffSize,Pi.smul_apply,norm_smul,norm_pow,Complex.norm_real,Real.norm_of_nonneg ((C₀).S.a_pos k).le,
      Finset.mul_sum]
  rw [map_sub,←eqn,map_smul] at fee
  rw [←eqn] at size
  rw [size] at fee
  exact fee.trans_eq (by ring)

/-- The signed coordinate after solving, in physical units. The solver error is
retained separately from the finite-volume correction. -/
theorem original {k N p:ℕ}(home:Opened C₀ d k p)(live:k≤N)
    (W:Rep G ((C₀).side k p))(tier:W.p=(levels).budget k)(beta:W.beta=((C₀).path.rep N p k).beta)
    (v c:(C₀).label d)(r E:ℝ)(positive:0≤r):
    let raw:=((C₀).factory d N p).terminal.symm v
    let M:=fitting (C:=C₀) d N p k R.makes home live
    let t:=Coat.gStep W.beta/W.p.threshold
    let fee:=(2:ℝ)^WilsonOriginalAdjacentMicroscopicPrice.height R d*
        invoice (C:=C₀) d k p*stock C₀ k*(C₀).S.a k^d*(Fr).coeffSize (awake C₀ d k N p v)
    (Fr).coeffSize (c-(Fr).scaled t (M raw))≤E →
    ∀j:(Fr).Index,‖(((r/(C₀).S.a k)^d:ℝ):ℂ)*c j -
      ((r^d*t^((Fr).grades j).2:ℝ):ℂ)*(awake C₀ d k N p v) j‖ ≤
        (r/(C₀).S.a k)^d*(E+fee):=by
  intro raw M t fee close j
  let low:=(Fr).scaled t (M raw)
  let goal:=((C₀).S.a k:ℂ)^d • (Fr).scaled t (awake C₀ d k N p v)
  have axis (x:(C₀).label d):‖x j‖ ≤ (Fr).coeffSize x:=
    Finset.single_le_sum (f:=fun i=>‖x i‖) (fun i _=>norm_nonneg _) (Finset.mem_univ j)
  have aa:‖c j-low j‖ ≤ E:=(axis (c-low)).trans close
  have bb:‖low j-goal j‖ ≤ fee:=(axis (low-goal)).trans (reading R d home live W tier beta v)
  have tri:‖c j-goal j‖≤‖c j-low j‖+‖low j-goal j‖:=by
    simpa only [dist_eq_norm] using dist_triangle (c j) (low j) (goal j)
  have cc:=tri.trans (add_le_add aa bb)
  have trade:(r/(C₀).S.a k)^d*((C₀).S.a k)^d=r^d:=by
    rw [←mul_pow,div_mul_cancel₀ r ((C₀).S.a_pos _).ne']
  calc
    _ = ‖(((r/(C₀).S.a k)^d:ℝ):ℂ)*(c j-goal j)‖:=by
      change ‖_ - _‖=‖_*(_-(((C₀).S.a k:ℂ)^d)*
        (((t^((Fr).grades j).2:ℝ):ℂ)*(awake C₀ d k N p v) j))‖
      rw [mul_sub,←trade,Complex.ofReal_mul,Complex.ofReal_mul,Complex.ofReal_pow]
      congr 1
      simp only [Complex.ofReal_pow]
      ring
    _ ≤ _:=by
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg (div_nonneg positive ((C₀).S.a_pos _).le) d)]
      exact mul_le_mul_of_nonneg_left cc (pow_nonneg (div_nonneg positive ((C₀).S.a_pos _).le) d)
end YM.Integration.WilsonOriginalNullReleasedReading
