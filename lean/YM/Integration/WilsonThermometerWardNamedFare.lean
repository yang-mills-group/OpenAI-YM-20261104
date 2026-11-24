import YM.Integration.WilsonThermometerWardNamedProgram
import YM.Integration.WilsonThermometerNominatedSourceSalary

/-! The three before-cutoff numerical receipts restore the occupied
source bill in one more fixed coupling power on the selected close interval. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerWardNamedFare
open Filter Finset Function Real Lattice Wilson RG Source Labels Marker QuadraticLocal
open PhysMS Extraction Table Trace Trace.Pilot AllOrder AllOrder.Floe Pert Pert.Asymptotics
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato RG05Readout
open WilsonCapturedPrimaryActiveArms WilsonCapturedPrimaryWardGapAperture
open WilsonThermometerOwnOffsetField WilsonThermometerOffsetTrajectory
open WilsonPositionThermometerCapStation WilsonOriginalThermometerPalette
open WilsonPositionThermometerGradedSource
open MergeProof RG16 QuadraticLocal.Advent PhysicalNext RG05Readout.Address Cells XSpace XSpace.Normalize XSpace.Rose
open QuadraticLocal.Earn QuadraticLocal.Affinity WilsonPositionThermometerReading
open Tree Earn Sunrise QuadraticLocal.Affinity FVA1 Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G)
local notation "C" => R.family
local notation "H" => R.alloy.B.a.clock.hatBeta
local notation "fees" => WilsonThermometerMarchReference.fee (C)
local notation "salary" => max 1 (WilsonOriginalStarSceneRent.wallet R levels 0)
local notation "J" => Stock.census (Fin 3)

private theorem rise (simple:G.Simple):Monotone H:=by
  intro i j h
  unfold Calendar.hatBeta
  rw [add_le_add_iff_left]
  exact mul_le_mul_of_nonneg_left ((Ribbons.bob (C).S).monotone h) (Gauge.slopeConstant_pos simple).le

theorem heat (simple:G.Simple) (d:ℕ) (cap:ℝ):
    ∀ᶠ b:ℕ in atTop,∀j≤b,PaceR.Close R d cap j b → ∀ N p, b<N →∀ℓ≤b,
      0<regulatorRun (C) N p (j+1) ∧ regulatorRun (C) N p (j+1)*(H ℓ^((1:ℝ)/6))^3≤2:=by
  filter_upwards [PaceR.covers_hat R simple d cap] with b wine
  intro j jb close N p after ℓ below
  let β:=(C).path.β N p (j+1)
  have lo:H (j+1)/2≤β:=(R.makes.wilson.represents N p (j+1) (by omega)).band.1
  have pos:0<β:=by linarith only [R.alloy.B.a.fits.delayed (j+1),lo]
  have four:H ℓ≤4*β:=by linarith only [rise R simple below,wine j j le_rfl jb close,rise R simple (Nat.le_succ j),lo]
  have base:0≤H ℓ:=(zero_le_one.trans (R.alloy.B.a.fits.delayed ℓ).le)
  have graded:(H ℓ^((1:ℝ)/6))^3=Real.sqrt (H ℓ):=by
    rw [←Real.rpow_natCast,←Real.rpow_mul base,Real.sqrt_eq_rpow]
    norm_num
  have limit:Real.sqrt (H ℓ)≤2*Real.sqrt β:=by
    nlinarith only [four,Real.sq_sqrt base,Real.sq_sqrt pos.le,Real.sqrt_nonneg (H ℓ),Real.sqrt_nonneg β]
  have root:0<Real.sqrt β:=Real.sqrt_pos.mpr pos
  change 0<(Real.sqrt β)⁻¹ ∧ (Real.sqrt β)⁻¹*_≤2
  refine ⟨inv_pos.mpr root,?_⟩
  rw [graded]
  calc
    _ ≤ (Real.sqrt β)⁻¹*(2*Real.sqrt β):=mul_le_mul_of_nonneg_left limit (inv_nonneg.mpr root.le)
    _ = 2:=by field_simp

def stageFee (E:ℝ) (s:Badge):ℝ:=
  2*3^40*(((1+E*∑i,fees s i)*salary*36^3)^3*3)

private theorem restored {ℓ:ℕ} {g E:ℝ} (solvent:0<g)
    (finance:g*(H ℓ^((1:ℝ)/6))^3≤2) {s:Badge}
    (y:(i:Fin 3)→Palette (C) (levels i)) (earn:∀i,size (y i)≤E*H ℓ^((1:ℝ)/6)*fees s i)
    (c:(J).Mode→ℂ) (w:Fin 3→ℝ)
    (old:g^40*WilsonGeometricSignedCapture.weightBill c w ≤ (3:ℝ)^40*((∑a,‖c a‖)*
      (((1+∑i,size (y i))*salary*36^3)^3*3))) :
    g^41*WilsonGeometricSignedCapture.weightBill c w ≤ (∑a,‖c a‖)*stageFee R E s:=by
  let A:=H ℓ^((1:ℝ)/6)
  have one:1≤A:=Real.one_le_rpow (R.alloy.B.a.fits.delayed ℓ).le (by norm_num)
  have S:1+∑i,size (y i)≤A*(1+E*∑i,fees s i):=by
    have total:∑i,size (y i)≤E*A*∑i,fees s i:=by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum (fun i _=>earn i)
    linarith only [one,total]
  let h:=(1+E*∑i,fees s i)*salary*36^3
  let mass:=∑a,‖c a‖
  have mon:0 ≤ salary*36^3:=by have :=le_max_left 1 (WilsonOriginalStarSceneRent.wallet R levels 0);positivity
  have receipt:((1+∑ i,size (y i))*salary*36^3)^3≤(A*h)^3:=by
    apply pow_le_pow_left₀
    · have each:0≤∑ i,size (y i):=Finset.sum_nonneg fun i _=>size_ge _
      rw [mul_assoc];exact mul_nonneg (by linarith only [each]) mon
    · dsimp [h]; linarith only [mul_le_mul_of_nonneg_right S mon]
  have hh:0≤h:=by
    have total:0≤(1+∑i,size (y i))*salary*36^3:=by
      rw [mul_assoc];exact mul_nonneg (by have q:0≤∑i,size (y i):=Finset.sum_nonneg fun i _=>size_ge _;linarith only [q]) mon
    have zero:0≤A*h:=by dsimp [h];linarith only [total,mul_le_mul_of_nonneg_right S mon]
    exact nonneg_of_mul_nonneg_right zero (zero_lt_one.trans_le one)
  have positive:0≤((3:ℝ)^40*mass*h^3*3):=by dsimp [mass];positivity
  calc
    _ =g*(g^40*WilsonGeometricSignedCapture.weightBill c w):=by ring
    _ ≤g*((3:ℝ)^40*(mass*(((1+∑i,size (y i))*salary*36^3)^3*3))):=mul_le_mul_of_nonneg_left old solvent.le
    _ ≤g*((3:ℝ)^40*(mass*((A*h)^3*3))):=by gcongr
    _ =(g*A^3)*((3:ℝ)^40*mass*h^3*3):=by ring
    _ ≤2*((3:ℝ)^40*mass*h^3*3):=mul_le_mul_of_nonneg_right finance positive
    _ =mass*stageFee R E s:=by unfold stageFee; dsimp [h]; ring

theorem original (simple:G.Simple) (degree:ℕ) (cap:ℝ) :
    ∀ᶠ b:ℕ in atTop,∀j≤b,PaceR.Close R degree cap j b → ∀N p, b<N → ∀k (o:Positions (Fin 3) ((C).side N p))
      (S:Shelf (N:=N) (p:=p) R k levels o.origin) (live:k≤N) (Z:Group (C) 6),
      Z.station.k≤b → ∀E:ℝ,
      WilsonThermometerNominatedSourceSalary.owns Z k N p live univ S.route (E*H Z.station.k^((1:ℝ)/6)) →
      ∃y:(i:Fin 3)→Palette (C) (levels i),
        WilsonCapturedPrimaryNamedReturn.primary R (p:=p) levels S.route live (WilsonThermometerWardNamedProgram.axis R Z N p) y ∧
        ∀ (c:(J).Mode→ℂ)(w:Fin 3→ℝ),let g:=regulatorRun (C) N p (j+1)
        g^40*WilsonGeometricSignedCapture.weightBill c w≤(3:ℝ)^40*((∑a,‖c a‖)*(((1+∑i,size (y i))*salary*36^3)^3*3)) →
        g^41*WilsonGeometricSignedCapture.weightBill c w≤(∑a,‖c a‖)*stageFee R E univ:=by
  filter_upwards [heat R simple degree cap] with b warm
  intro j jb close N p after k o S live Z below E priced
  obtain ⟨y,literal⟩:=priced
  obtain ⟨gp,finance⟩:=warm j jb close N p after Z.station.k below
  refine ⟨y,?_,fun c w old=>restored R gp finance y (fun i=>(literal i).2) c w old⟩
  intro i
  let a:=((C).S.a k:ℂ)^(levels i)
  have non:a≠0:=pow_ne_zero _ (Complex.ofReal_ne_zero.mpr ((C).S.a_pos _).ne')
  let t:=( (C).factory (levels i) N p).terminal (finer (S.route i) live (y i) (primaryLetter (levels i)))
  have line:a • t=WilsonThermometerWardNamedProgram.axis R Z N p i:=(literal i).1
  have cancel:a⁻¹ • (a • t)=t:=inv_smul_smul₀ non t
  exact cancel.symm.trans (congrArg (a⁻¹ • ·) line)

end YM.Integration.WilsonThermometerWardNamedFare
