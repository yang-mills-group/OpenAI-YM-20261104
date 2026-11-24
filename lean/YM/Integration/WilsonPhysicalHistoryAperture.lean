import YM.Integration.WilsonPhysicalHistoryFormalPayoff
import YM.Integration.WilsonPhysicalHistoryBirthClock
import YM.FormalBulk08.Kemp.Sink

/-! The actual paid spatial aperture for fixed-order fields: explicit
radius in the genuine original positive Knoxville width, valid on the
whole moving cutoff interval, including its far endpoint. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryAperture

open Filter Real Lattice RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Exterior Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp
open Pose Glide Bank Dawn Wine Rial Roof Dove Series Trellis Aster Borough Elm Dove.Lab
open PhysicalNext.Repeat.Legato WilsonPhysicalExteriorMeshStops
open RG16 RG16.Literal RG16.Guarding Pert.Asymptotics Trace.Physical
open scoped Classical Topology ENNReal BigOperators

variable {G : Gauge}

def width (C : Family G) (i : ℕ) : ℝ := (Primer.FamilyWindow C).width (C.path.levels.clock.J i)

def radius (C : Family G) (p i : ℕ) : ℕ :=
  ⌈((p+1:ℕ):ℝ)*RG16.Lambda C.path.levels i/width C i⌉₊

theorem width_pos (C : Family G) (i : ℕ) : 0<width C i := (Primer.FamilyWindow C).pos _

theorem width_paid (R : Run G) {u : ℕ→ℕ} (grant : WilsonWindowFormalPurchase.Canonical u R.kit)
    (i : ℕ) : (width R.family i)⁻¹ ≤ ageZ (R.family.path.levels.clock.hatBeta i) := by
  obtain ⟨B,_,paid,Q⟩ := (WilsonWindowFormalAnnouncement.on_run R grant).power.payment i
  have t := Q.header _ (R.family.path.levels.fits.mono (Nat.le_succ i))
  exact ((le_abs_self _).trans ((le_add_of_nonneg_right (abs_nonneg _)).trans t)).trans paid

theorem age (C : Family G) (i : ℕ) : ageZ (C.path.levels.clock.hatBeta i) ≤ RG16.Lambda C.path.levels i := by
  have bl := Real.log_pos (C.path.levels.fits.delayed i)
  have low := Real.log_le_sub_one_of_pos bl
  change 1+Real.log (Real.log (C.path.levels.clock.hatBeta i)) ≤ 2+Real.log (C.path.levels.clock.hatBeta i)
  linarith

/-- The requested radius is at most a fixed quadratic in the physical
clock at k, uniformly before all steps of its real first-crossing window. -/
theorem size (R : Run G) (simple : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    {u : ℕ→ℕ} (grant : WilsonWindowFormalPurchase.Canonical u R.kit) {c : ℝ} (hc : 1≤c) (p : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ i, k ≤ i → i ≤ ultraviolet R.family c k →
      (radius R.family p i : ℝ) ≤ (4*(p+1:ℕ)+1:ℝ)*(RG16.Lambda R.family.path.levels k)^2 := by
  let C := R.family
  let Z := RG16.Lambda C.path.levels
  filter_upwards [WilsonPhysicalHistoryBirthClock.temperatures R simple slow hc] with k heat i _ stop
  have b0 : 0<C.path.levels.clock.hatBeta k := zero_lt_one.trans (C.path.levels.fits.delayed k)
  have hpos : 0<C.path.levels.clock.hatBeta i := zero_lt_one.trans (C.path.levels.fits.delayed i)
  have temp := Real.log_le_log hpos (heat le_rfl stop)
  change Real.log (C.path.levels.clock.hatBeta i) ≤Real.log (2*C.path.levels.clock.hatBeta k) at temp
  rw [Real.log_mul (by norm_num) b0.ne'] at temp
  have two : Real.log 2≤1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<2)]
  have upper : Z i ≤ 2*Z k := by
    have zk := lambda_up C k
    change 2+Real.log (C.path.levels.clock.hatBeta i) ≤ 2*(2+Real.log (C.path.levels.clock.hatBeta k))
    change 2<2+Real.log (C.path.levels.clock.hatBeta k) at zk
    linarith
  have Z0 := (lambda_pos C i).le
  have W0 := width_pos C i
  have W1 := (width_paid R grant i).trans (age C i)
  have q0 : 0≤((p+1:ℕ):ℝ)*Z i/(width C i) := by positivity
  have aperture := (Nat.ceil_lt_add_one q0).le
  change (radius C p i:ℝ) ≤ ((p+1:ℕ):ℝ)*Z i/width C i+1 at aperture
  have core : Z i*(width C i)⁻¹≤(2*Z k)^2 :=
    (mul_le_mul_of_nonneg_left W1 Z0).trans (by rw [←sq]; exact pow_le_pow_left₀ Z0 upper 2)
  have zk1 : 1≤Z k := by linarith [lambda_up C k]
  have extra : 1≤(Z k)^2 := one_le_pow₀ zk1
  calc
    _ ≤ ((p+1:ℕ):ℝ)*(Z i*(width C i)⁻¹)+1 := by simpa only [div_eq_mul_inv,mul_assoc] using aperture
    _ ≤ ((p+1:ℕ):ℝ)*(2*Z k)^2+(Z k)^2 := add_le_add (mul_le_mul_of_nonneg_left core (by positivity)) extra
    _ = _ := by push_cast; ring

/-- The actual aperture buys the desired exponential before any test or
cutoff is read. The right hand side is the real regulated finite coupling. -/
theorem exponential (R : Run G) (p N per i : ℕ) (live : i≤N) :
    Real.exp (-(width R.family i)*(radius R.family p i:ℝ)) ≤
      (regulatorRun R.family N per i)^(p+1) := by
  let C := R.family
  let W := width C i
  let z := RG16.Lambda C.path.levels i
  have w := width_pos C i
  have rz := (div_le_iff₀ w).mp (Nat.le_ceil (((p+1:ℕ):ℝ)*z/W))
  have base : Real.exp (-z) ≤ regulatorRun C N per i := by
    apply le_trans _ (g_band C R.makes (p:=per) live).1
    change Real.exp (-z) ≤ Real.exp 1*Real.exp ((-(1:ℝ)/2)*z)/2
    have down : Real.exp (-z)≤Real.exp ((-(1:ℝ)/2)*z) := Real.exp_le_exp.mpr (by linarith [lambda_pos C i])
    have two : (2:ℝ)≤Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
    have pos := Real.exp_pos ((-(1:ℝ)/2)*z)
    nlinarith [mul_nonneg (sub_nonneg.mpr two) pos.le]
  calc
    _ ≤ Real.exp (-z)^(p+1) := by rw [←Real.exp_nat_mul]; apply Real.exp_le_exp.mpr; change ((p+1:ℕ):ℝ)*z ≤ (radius C p i:ℝ)*W at rz; linarith
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le base _

/-- Weighted all-chain Knoxville seminorm controls the actual spatial tail. -/
def mass {X : Type} {r : ℕ} (D : Reach X) (o : X) (A : ℕ) (T : Tile X r) : ℝ≥0∞ :=
  ∑' v : chain X r, if A≤Gorge.wide D (Fin.cons o v) then ‖T v‖ₑ else 0

theorem tail {X : Type} {r : ℕ} {D : Reach X} {η C : ℝ} {o : X} {T : Tile X r}
    (h : Knoxville D η o T C) (hp : 0≤η) (A : ℕ) :
    mass D o A T ≤ ENNReal.ofReal (Real.exp (-η*A)*C) := by
  let w := ENNReal.ofReal (Real.exp (-η*A))
  have each (v : chain X r) : (if A≤Gorge.wide D (Fin.cons o v) then ‖T v‖ₑ else 0) ≤
      w*(Gorge.shine η (Gorge.wide D (Fin.cons o v))*‖T v‖ₑ) := by
    by_cases inside : A≤Gorge.wide D (Fin.cons o v)
    · rw [if_pos inside,←mul_assoc]
      apply le_mul_of_one_le_left' 
      change 1≤ ENNReal.ofReal (Real.exp (-η*A))*ENNReal.ofReal (Real.exp (η*(Gorge.wide D (Fin.cons o v):ℝ)))
      rw [←ENNReal.ofReal_mul (Real.exp_pos _).le,←Real.exp_add,←ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      apply Real.one_le_exp
      have hmul := mul_le_mul_of_nonneg_left (show (A:ℝ)≤(Gorge.wide D (Fin.cons o v):ℝ) by exact_mod_cast inside) hp
      linarith
    · simp [inside]
  calc
    _ ≤ ∑' v : chain X r,w*(Gorge.shine η (Gorge.wide D (Fin.cons o v))*‖T v‖ₑ) := ENNReal.tsum_le_tsum each
    _ = w*(∑' v : chain X r,Gorge.shine η (Gorge.wide D (Fin.cons o v))*‖T v‖ₑ) := ENNReal.tsum_mul_left
    _ ≤ w*ENNReal.ofReal C := mul_le_mul_right h.2 _
    _ = _ := (ENNReal.ofReal_mul (Real.exp_pos _).le).symm

end YM.Integration.WilsonPhysicalHistoryAperture

