import YM.Integration.OriginalSourceJetAddresses
import YM.WilsonCoeffUV.Marked.Paths.Vector
import YM.WilsonCoeffUV.Marked.Bounds.Independent

/-! The presold primitive curvature/address rows as actual cover operators.
A genuine Haar-colour row supplies the invariant path polynomial. A calibrated
native test derivative supplies a point functional at the original physical
block address. Their product has a certified finite heat tower on every torus. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalMarkedSourceComet
open Function Set Finset Lattice Wilson RG Source Labels Marker Stationary
open WilsonCoeffUV WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank
open WilsonCoeffUV.Soil WilsonCoeffUV.Blue WilsonCoeffUV.Fountain WilsonCoeffUV.Bank.Mosaic.Near
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open ActualRunCalibrationTests ActualRunCurvaturePackets NativeCurvatureTensor
open scoped Classical BigOperators ContDiff

variable {ι : Type} [DecidableEq ι] {G : Gauge} {r : ℕ}

/-- The physical ratio and independently prescribed site determine the atom's
position in the compact native test cell, including even periods. -/
def place {n f : Side} (R : Ratio n f) (a : Site R.count) : Chamber :=
  ⟨coordinates.symm (RG05Readout.Flatten.placeR R a), by
    rw [Metric.mem_closedBall,dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : 0 ≤ (2:ℝ)⁻¹)).mpr
    intro i
    have hp : (0:ℝ) < R.count.val := by exact_mod_cast R.count.pos
    obtain ⟨ha,hb⟩ := lift_centers a i
    have h1 : -(R.count.val : ℝ) < 2*(lift a i : ℝ) := by exact_mod_cast ha
    have h2 : 2*(lift a i : ℝ) ≤ (R.count.val : ℝ) := by exact_mod_cast hb
    change |(R.count.val : ℝ)⁻¹*(lift a i : ℝ)| ≤ (2:ℝ)⁻¹
    rw [abs_mul,abs_of_pos (inv_pos.mpr hp),← div_eq_inv_mul,div_le_iff₀ hp]
    apply abs_le.mpr
    constructor <;> linarith⟩

/-- The actual underlying complex Mood is tested through any of its real
linear projections, with every undivided derivative order unchanged. -/
def project (U : Orbit) (x : U.Mood) (L : ℂ →L[ℝ] ℝ) : Scroll U.D :=
  ⟨L ∘ x.val, L.contDiff.comp (U.admits x).choose_spec.orders⟩

theorem project_jet (U : Orbit) (x : U.Mood) (L : ℂ →L[ℝ] ℝ) {k : ℕ}
    (hk : k ≤ U.D) (w : OriginalSourceJetAddresses.Word k) (p : Chamber) :
    crease (project U x L) w p.val = L (OriginalSourceJetAddresses.jet k w p.val x.val) := by
  change iteratedFDeriv ℝ k (L ∘ x.val) p.val _ = _
  rw [ContinuousLinearMap.iteratedFDeriv_comp_left L (U.admits x).choose_spec.orders.contDiffAt (Nat.cast_le.mpr hk)]
  rfl

/-- The open-foreground path fields and Haar contraction are exactly those of
the independently read original curvature token. The source scalar can have
any complex phase, and the same real projection is used on every colour. -/
def colour (path : Fin r → RG.Slot) (c : Fin r → G.ColorIndex) (a : ℂ)
    (L : ℂ →L[ℝ] ℝ) : RG.Atom G r :=
  ⟨path,fun j => L (a*NativeCurvatureTensor.coefficient c j)⟩

theorem colour_poly (path : Fin r → RG.Slot) (c : Fin r → G.ColorIndex) (a : ℂ)
    (L : ℂ →L[ℝ] ℝ) (v : Fin r → G.Color) :
    (colour path c a L).poly v = L (a*NativeCurvatureTensor.value c v) := by
  rw [NativeCurvatureTensor.value, Finset.mul_sum,map_sum,RG.Atom.poly]
  apply Finset.sum_congr rfl
  intro j _
  let b : ℝ := ∏ i, v i (j i)
  rw [show a*((b : ℂ)*NativeCurvatureTensor.coefficient c j)=b • (a*NativeCurvatureTensor.coefficient c j) by
    simp only [Complex.real_smul]; ring, map_smul]
  exact mul_comm _ _

theorem invariant (path : Fin r → RG.Slot) (c : Fin r → G.ColorIndex) (a : ℂ)
    (L : ℂ →L[ℝ] ℝ) : (colour path c a L).Invariant := by
  intro u v
  rw [colour_poly,colour_poly,NativeCurvatureTensor.value_invariant]

/-- Tensor the invariant geometric path row with one genuine point derivative. -/
def current {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (P : RG.Atom G r) (d : V) : Comet G V r := ⟨P.leg,fun j => P.coeff j • d⟩

private theorem current_poly {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (P : RG.Atom G r) (d : V) (L : V →L[ℝ] ℝ) (v : Fin r → G.Color) :
    (dip (current P d) L).poly v = L d * P.poly v := by
  rw [RG.Atom.poly,RG.Atom.poly,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change L (P.coeff j • d)*_ = _
  rw [map_smul,smul_eq_mul]
  ring

private theorem current_invariant {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (P : RG.Atom G r) (h : P.Invariant) (d : V) : shadeStar (current P d) := by
  intro L u v
  rw [current_poly,current_poly,h]

/-- One certified physical input era.  The head grade is `e = r - fieldRank`
when the native packet carries its registered negative Laurent power. -/
def source (D : ι → ℕ) (o : ι) (P : RG.Atom G r) (k : Knob (D o))
    (a : Chamber) (e : ℕ) (p : Cover) : Era G (Pen D {o}) :=
  cn D o (volumeR (current P (claim (D o) k a)) e) p

theorem certified (D : ι → ℕ) (o : ι) (P : RG.Atom G r) (hP : P.Invariant)
    (k : Knob (D o)) (a : Chamber) (e h : ℕ) (hr : r ≤ h+e) (p : Cover) :
    Auth h (source D o P k a e p) :=
  ((aug_auth _ (current_invariant _ hP _) hr).tuft (petal D o)).shifted p

theorem funded (D : ι → ℕ) (o : ι) (P : RG.Atom G r) (k : Knob (D o))
    (a : Chamber) (e : ℕ) (z : ι → Cover) {w : ℝ} (hw : 0 < w) (i j : ℕ) :
    Wig terrain z (steep w) (integerP (current P (claim (D o) k a)) w * flour G (steep w) r j)
      {o} ((source D o P k a e (z o)).2 i j) :=
  Budges D o _ (by exact (div_pos hw (by norm_num)).le) z (volume_price _ hw _ _ _)

/-- At the genuine fine forest field the current reads the real projection
of the original Haar-colour polynomial times the indexed source derivative. -/
theorem paired (D : ι → ℕ) (o : ι) (path : Fin r → RG.Slot) (c : Fin r → G.ColorIndex)
    (scalar : ℂ) (L : ℂ →L[ℝ] ℝ) {k : ℕ} (hk : k ≤ D o) (w : Fin k → Axis)
    (p : Chamber) (f : ∀ i, Scroll (D i)) {n : Side} (U : Wilson.Config G n) (x : Site n) :
    let slot := claim (D o) ⟨⟨k,Nat.lt_succ_of_le hk⟩,w⟩ p
    let C := current (colour path c scalar L) (petal D o slot)
    (dip C (touch (fun i => page _ (f i)) {o})).unmasked U x =
      crease (f o) w p.val * L (scalar*NativeCurvatureTensor.value c (fun i => (path i).atSite U x)) := by
  intro slot C
  change (dip C _).poly _ = _
  rw [current_poly,petal_hit,colour_poly]
  rfl

end YM.Integration.OriginalMarkedSourceComet
end
