import YM.Integration.WilsonCapturedPrimaryCourse

/-! All tests of the enrolled finite field panel fit the same funded
reporting interval on every cutoff and every allowed period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryReporter
open Function Filter Finset Set Labels Lattice Wilson RG Source Push.Local
open Next.Foundations PhysicalNext.Repeat.Legato Pert.Asymptotics
open Planned.AtomRegular WilsonCapturedPrimaryAngles WilsonCapturedPrimaryAperture
open WilsonCapturedPrimaryPaid WilsonCapturedPrimaryCollar WilsonCapturedPrimaryEstimate
open scoped Classical Topology
variable {G : Gauge} {d : ℕ}

private theorem location (R : Run G) (simple : G.Simple) (A : Hol G) (p : Probe G d)
    (T P v : ℕ) (extra : 1≤v) :
    ∀ᶠ i : ℕ in atTop, ∀ N per : ℕ, i+1≤N →
      let b := R.family.path.levels.budget i
      let g := regulatorRun R.family N per (i+1)
      let r := radius b (cutoff b g T)
      let t := g^gap P v
      1≤b.supportExponent →
      0<g ∧ g≤1 ∧ b.threshold*(1+(r:ℝ))^2≤1 ∧ 2*t≤1 ∧
      2*t*wallet A p r≤aperture G*b.threshold ∧
      WilsonCapturedPrimaryRough.price G (p.2.val+1) (wallet A p r) ≤ g⁻¹ := by
  let k := p.2.val+1
  let l := d*k
  let C := 1+|panelFee A p|
  let D := patterns k*baseCost G k*C^k
  let H := max (4*C/aperture G) D
  have ap := positive G
  have c0 : 0<C := by unfold C; positivity
  have b0 : 0 ≤ patterns k*baseCost G k := mul_nonneg (patterns_nonneg _) (baseCost_nonneg ..)
  have h0 : 0≤H := (div_nonneg (by positivity) ap.le).trans (le_max_left ..)
  filter_upwards [WilsonCapturedPrimaryCourse.original R simple T l h0 (ε:=1) zero_lt_one] with i quote
  intro N per hi b g r t support
  obtain ⟨gp,half,floor,wide,radial⟩ := quote N per hi support
  have h1 : g≤1 := half.trans (by norm_num)
  have gx : g^gap P v ≤ g^2 :=
    pow_le_pow_of_le_one gp.le h1 (by unfold gap;omega)
  have one : 1 ≤ 1+(r:ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have leg : d≤l := by simpa only [l,k] using Nat.le_mul_of_pos_right d (Nat.zero_lt_succ p.2.val)
  have cover : wallet A p r ≤ C*(1+(r:ℝ))^d := by
    unfold wallet C
    rw [add_mul,one_mul]
    exact add_le_add (one_le_pow₀ one) (mul_le_mul_of_nonneg_right
      (le_abs_self _) (pow_nonneg (zero_le_one.trans one) _))
  have t1 : 2*t≤1 := by
    have x := gx.trans (show g^2≤g by simpa [pow_two] using mul_le_of_le_one_right gp.le h1)
    change 2*(g^gap P v)≤1;linarith only [x,half]
  have cmp : g*(1+(r:ℝ))^d ≤ g*(1+(r:ℝ))^l :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ one leg) gp.le
  have fit : (4*C/aperture G)*(g*(1+(r:ℝ))^d) ≤ 1 := by
    calc
      _ ≤ H*(g*(1+(r:ℝ))^l) := mul_le_mul (le_max_left ..) cmp
        (mul_nonneg gp.le (by positivity)) h0
      _ ≤ _ := by simpa only [mul_assoc] using radial
  have four : 4*g*wallet A p r ≤ aperture G := by
    apply (mul_le_mul_of_nonneg_left cover (show 0≤4*g by positivity)).trans
    calc
      4*g*(C*(1+(r:ℝ))^d) = (4*C/aperture G*(g*(1+(r:ℝ))^d))*aperture G := by field_simp
      _ ≤ _ := mul_le_of_le_one_left ap.le fit
  have tsmall : 2*t*wallet A p r ≤ aperture G*b.threshold := by
    calc
      _ ≤ 2*g^2*wallet A p r := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left gx
        (by norm_num)) (zero_le_one.trans (wallet_one A p r))
      _ = (4*g*wallet A p r)*(g/2) := by ring
      _ ≤ _ := mul_le_mul four (by linarith only [floor]) (by positivity) ap.le
  have gross : WilsonCapturedPrimaryRough.price G k (wallet A p r) ≤ D*(1+(r:ℝ))^l := by
    unfold WilsonCapturedPrimaryRough.price D l
    calc
      _ = (patterns k*baseCost G k)*(wallet A p r)^k := by ring
      _ ≤ (patterns k*baseCost G k)*(C*(1+(r:ℝ))^d)^k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans (wallet_one A p r)) cover _) b0
      _ = _ := by rw [mul_pow,pow_mul];ring
  have product : WilsonCapturedPrimaryRough.price G k (wallet A p r)*g≤1 :=
    calc
      _ ≤ (D*(1+(r:ℝ))^l)*g := mul_le_mul_of_nonneg_right gross gp.le
      _ ≤ (H*(1+(r:ℝ))^l)*g := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity)) gp.le
      _ ≤ 1 := by convert radial using 1;ring
  exact ⟨gp,h1,wide,t1,tsmall,by rw [←one_div];exact (le_div_iff₀ gp).mpr product⟩

theorem panel (R : Run G) (simple : G.Simple) (F : Labels.Frame G d) (A : Hol G)
    (T P v : ℕ) (extra : 1≤v) :
    ∀ᶠ i : ℕ in atTop, ∀ p∈tests F, ∀ N per : ℕ, i+1≤N →
      let b := R.family.path.levels.budget i
      let g := regulatorRun R.family N per (i+1)
      let r := radius b (cutoff b g T)
      let t := g^gap P v
      1≤b.supportExponent →
      0<g ∧ g≤1 ∧ b.threshold*(1+(r:ℝ))^2≤1 ∧ 2*t≤1 ∧
      2*t*wallet A p r≤aperture G*b.threshold ∧
      WilsonCapturedPrimaryRough.price G (p.2.val+1) (wallet A p r) ≤ g⁻¹ :=
  (Filter.eventually_all_finset (tests F)).2 (fun p _ => location R simple A p T P v extra)

end YM.Integration.WilsonCapturedPrimaryReporter
