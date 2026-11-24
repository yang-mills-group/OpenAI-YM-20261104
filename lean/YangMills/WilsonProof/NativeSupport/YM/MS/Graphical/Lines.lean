import YM.MS.Graphical.Lines
import YM.MS.Dock.Dance
import YM.MS.Swirl.LandLine

/-!
# Rules for a scale-ordered Wick edge

Here a momentum in sector `m` has **4+2m real axes** (`SectorP m`), `z=-ε`,
loop calculation uses `D=4+2z`.

* The line filter is `1-H(u)`, `H(u)=(1+u) exp(-u)`,
  `u=(IR length)^2 * p.sq` (Euclidean sum of squares). A line in a scale-ordered graph is integrated
  in logarithmic length. The lines are Landau AA and the two cK orientations,
  **already in the coupling-scaled convention**; include the colour delta. More
  precisely use (before halving and filtering) `Swirl.Near.Tail` (AA transverse
  projector / `p.sq`, **both** ghost--anti lines `+i p_j/p.sq`, zero at `p=0`).
  Here `c` is `Landau.ghost` and `K_j` is `Landau.anti j`; no `gaugeC` line.
* For a bridge line, split the external word with `Koszul.scatter` (choose left/right
  for each *slot*, keep order, Koszul sign). The flowing momentum is fixed by
  conservation on the first side (unmarked). A marked row is read with source
  momentum implicit (negative of the net), a bulk row as multiplying its
  conservation delta. Our off-conservation extension where needed (`Mob` etc.)
  uses this *same* routing, and doesn't include the multiplying delta.
* Closing a line in one component, use the Arc dimensional integration rule
  (one loop variable). Tag both ends in order and pay **half** the line. This is
  a sum over all such assignments; no prohibition against closing on the same
  vertex. We use the integral itself, NOT a choice of linear extension of a
  map on a function space. In `radialClose` the real integral uses the plane
  `Px m` through `carpet`. In the formal complement of dimension `2*(z-m)`
  only a radial integration remains, with powers analytically continued as
  in `Arc.gage`/`Arc.pruning` (integration by parts prescription). In `wing`,
  `Wtr` is the open-index Wick contraction: use the actual momentum in the
  one-higher sector (extends by **two axes**), sum over leg types,
  polarisations and colour including the `2*(z-(m+1))` extra diagonal copies.
  This last rule is important. No four-dimensional reduction of evanescent
  terms prior to extracting Laurent coefficients. The integration domain
  in z here is `Town` (`2 z.re + 1 > 0`); see `DeepRadial.lean` et seq. for
  pushing it farther left for the common-cut UV limit. In addition to
  specifying the rule at noninteger dimension, we check its agreement with
  ordinary loop integration on the integer sectors. `y` is the MS-bar
  convention **log mass parameter**, i.e. with shifted scale as in
  `Train/MeasureD.lean` (y = log μ + (γ_E - log(4π))/2). The definition below
  works with *any* `y`. `feeD` pays the (2π) factor and undoes the Arc
  density factor `Gamma(z+1)/π^z`; `tenorK` includes the mass factor per loop
  (`exp(-2*y*z)`) as well.
-/

set_option autoImplicit false
noncomputable section
namespace YM.MS.Graphical
open Filter Function Finset MeasureTheory
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color
open Shine Hem Mell Pearl Train Book Convolve Garment.Wick Dock
open scoped Topology ContDiff Interval

variable {G : Gauge} {b : Bool} {m n k ℓ : ℕ} {x z : ℂ} {F H : Mob G} {V : Flats G}
variable (s cut : ℝ) (i j : Cfield G m) (p : SectorP m)

/-- Half the propagator through the indicated length, with IR filter and colour delta. -/
def halfCov (s : ℝ) : Rip G := fun _ => Landau.choir (Swirl.Near.Fuel (Real.exp s)) id


theorem halfD_eq (G : Gauge) (s : ℝ) : halfD s = A0 G s := by
  funext m i j p
  unfold halfD A0; simp only [Landau.choir]; split
  · rw [← City.brushed, Complex.real_smul]
  simp

lemma propagator_derivative : HasDerivAt (fun s => halfCov s m i j p) (halfD s m i j p) s := by
  unfold halfD halfCov Landau.choir
  split
  · exact (Swirl.Near.swing i.1 j.1).scomp s (Real.hasDerivAt_exp s)
  rw [smul_zero]
  exact hasDerivAt_const _ _

lemma length_recovers_line : (∫ t in cut..s, halfD t m i j p) =
    halfCov s m i j p - halfCov cut m i j p := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t => halfCov t m i j p) (fun t _ => propagator_derivative t i j p)
  apply Continuous.intervalIntegrable
  unfold halfD
  apply Continuous.smul Real.continuous_exp
  simp only [Landau.choir]; split
  · rcases i with ⟨⟨_|a,_|_⟩,v⟩ <;> rcases j with ⟨⟨_|a,_|_⟩,w⟩ <;>
      simp only [City.L0, City.brush] <;> fun_prop
  exact continuous_const

lemma halfCov_zero_UV : Tendsto (fun s => halfCov s m i j p) atBot (𝓝 0) := by
  unfold halfCov Landau.choir; split
  · have hc := ((Swirl.Near.swing (A := Arts.L m) (t:=0) (p:=p) i.1 j.1).continuousAt.tendsto).comp
      Real.tendsto_exp_atBot
    simpa [Function.comp_def, Swirl.Near.Fuel, Swirl.Near.ohLow] using hc
  exact tendsto_const_nhds



theorem bridging_eq (s : ℝ) (F H : Mob G) : bridging s F H = arbor (A0 G s) F H := by
  funext m w
  unfold bridging arbor tree
  apply scatter_congr; intro a c he
  unfold bridgeTerm
  rw [convertR (reverse_a G s m), halfD_eq]; rfl


theorem bridgeForce_eq (V W : Flats G) : bridgeForce V W = drive0 G V W := by
  unfold drive0 TreeN bridgeForce
  rw [explodeL]
  simp_rw [bridging_eq]
  rfl


lemma radialClose_eq_ocean (U : Rip G) (z : ℂ) (y : ℝ) (F : Mob G) :
    radialClose U z y F = tenorK z y • ocean z U F := rfl

/-- Cycle shell integrals are not defaulting. Even the evaluations along the whole
external ray used inside the pruning prescription work. -/
lemma cycle_integrals_exist {U : Rip G} (hf : Form0 b F) (hu : Knot b U)
    (hz : z ∈ Town) (w : Legs (Shore G m)) :
    let K := wing z U F (ray w)
    (∀ (t r : ℝ), Integrable (fun p : SectorP m => K ((p,t), r)) (Px m)) ∧
    ∀ j, ContDiff ℝ ∞ (pruning j (carpet (Px m) K)) ∧
       ∀ r : ℝ, IntegrableOn (fun t : ℝ =>
         ((t:ℂ)^(2*z+1)) * pruning j (carpet (Px m) K) (t,r)) (Set.Ioi (0:ℝ)) := by
  intro K
  have hp := carpet_test hf.price hu.price (ray w) z
  have hv : Arc.Reflect (carpet (Px m) K) :=
    mirror_r _ (wing_mirror hf.token hu.token z (ray w))
  refine ⟨fun t r => ?_, fun j => ⟨((pruned hp (fun _=>hv) j).1).smooth (), fun r => ?_⟩⟩
  · exact (Arc.Q.Gmajor (Px m) (exact_test hf.price hu.price (ray w) z) ()).values (t,r)
  exact meets ((pruned hp (fun _=>hv) j).1) hz r

/-- Test the integration on integer dimensions, including lifting all the
external data, and retaining the `tenorK*pitch` normalisation. -/
theorem radialClose_integer {U : Rip G} (hf : Form0 b F) (hu : Knot b U) (he : m ≤ n)
    (y : ℝ) (w : Legs (Shore G m)) :
    radialClose U n y F m w = tenorK n y * ((pitch n : ℂ) *
      ∫ q, ∑ i : Cfield G n, ∑ j : Cfield G n,
        U n i j q * F n ((i,q)::(j,-q)::Arts.lift he w) ∂(Px n)) := by
  simp_rw [← Flux.at_trc]
  rw [radialClose_eq_ocean, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
      reg_proj hf.price hu.price hf.token hu.token he w, Complex.real_smul]

lemma integer_integrable {U : Rip G} (hf : Form0 b F) (hu : Knot b U) (w : Legs (Shore G m)) :
    Integrable (fun q => ∑ i : Cfield G m, ∑ j : Cfield G m,
        U m i j q * F m ((i,q)::(j,-q)::w)) (Px m) := by
  simp_rw [← Flux.at_trc]
  exact theory hf.price hu.price m w

/-- No change of convention per loop. At D=4+2n this is exactly the fee for one
loop, including the measure factor `(2π)^(-4-2n)` in the chosen ν convention. -/
lemma pitch_normalization (n : ℕ) (y : ℝ) :
    tenorK n y * (pitch n : ℂ) =
      Complex.exp (-(y:ℂ)*2*(n:ℕ)) * (((((2*Real.pi)^ (4+2*n))⁻¹):ℝ):ℂ) := by
  rw [restore_tape, feeD, Complex.Gamma_nat_eq_factorial, Complex.exp_nat_mul]
  rw [show ∀ a : ℝ, Complex.exp (a:ℂ)= Real.exp a from fun a => (Complex.ofReal_exp a).symm,
      Real.exp_sub, Real.exp_log Real.pi_pos,
      show Real.exp (2*Real.log (2*Real.pi)) = (2*Real.pi)^2 from ?_]
  swap
  · rw [two_mul,Real.exp_add, Real.exp_log (by positivity),pow_two]
  let u := Complex.exp (-(y:ℂ)*2*(n:ℕ))
  have hp : Real.pi ≠ 0 := Real.pi_pos.ne'
  let v : ℝ := 2*Real.pi; have hv : v ≠ 0 := mul_ne_zero (by norm_num) hp
  have hw : (↑(n.factorial) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have he : room * (Real.pi/(v^2))^n / (↑(n.factorial):ℝ) * pitch n = (v^(4+2*n))⁻¹ := by
    unfold pitch
    rw [show room = (v^4)⁻¹ from rfl, pow_add, pow_mul, div_pow, inv_pow]
    field_simp
  have hH : (room:ℂ) * (↑(Real.pi/(v^2)):ℂ)^n / (n.factorial:ℂ) * (pitch n : ℂ) =
      (((v^(4+2*n))⁻¹:ℝ):ℂ) := by exact_mod_cast he
  change _ * u * _ = u * _
  rw [mul_comm _ u, mul_assoc, hH]


lemma toner0 (z : ℂ) : tenorK z 0 = feeD z := by simp [restore_tape]

theorem closeForce_eq (V : Flats G) (hv : Moony b V) : Pact (closeForce V) (step0 G V) := by
  intro ℓ
  unfold closeForce step0 CycleN
  rw [blap, Finsupp.sum_apply, Finsupp.sum_apply]
  unfold Finsupp.sum
  filter_upwards [hv.sunup, high0] with z hz hw
  simp only [Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.single_apply, Finsupp.single_apply]; split
  · rw [swamp_spec (c_bo 0) (hz i) hw]
    dsimp only
    rw [radialClose_eq_ocean, toner0, halfD_eq]
  rfl

/-- These are integrations with one common upper length. Rescaling the unit
pages in the bridge/cycle rules is *exactly* the Feynman shell against the
child graphs with this same length, still at z. -/
theorem bridge_common (s y : ℝ) (h : ℕ) (z : ℂ) (a d : ℕ) (F H : Mob G) :
    hikeP z h (a+d) y s (bridging 0 F H) =
      bridging s (hikeP z 4 a y s F) (hikeP z h d y s H) := by
  simp only [bridging_eq]
  rw [tree_bind z (reverse_a G 0) F H (d:= (4:ℂ)) (a := 4) (b := h) (by push_cast; ring), pA]

lemma cycle_common {F : Mob G} (hz : z ∈ Town) (hf : Form0 false F)
    (s y : ℝ) (h a : ℕ) :
    hikeP z h (a+1) y s (radialClose (halfD 0) z 0 F) =
      radialClose (halfD s) z y (hikeP z h a y s F) := by
  let f : Coat G := fun _ => F
  have hx : Form0 false (hikeP z h a y s F) := (fseed hf _ _).smul _
  simp only [halfD_eq, radialClose_eq_ocean, toner0]
  rw [show (feeD z • ocean z (A0 G 0) F) = swamp (A0 G 0) f z from
       (swamp_spec (c_bo 0) (show Form0 false (f z) from hf) hz).symm,
      cycle_bind (a := 4) z hz (c_bo 0) hf (by ring), pA]
  simp only [unitC, LinearMap.smul_apply, show f z = F from rfl, Wave.port_spec hz _ (c_bo s) hx]

theorem close_common (V : Flats G) (hv : Moony b V) (h : ℕ) :
    ∀ᶠ z in dotty, ∀ y s : ℝ,
      Parade (closeForce V) h y s z = radialClose (halfD s) z y (Parade V h y s z) := by
  have hb := Moony.sunup (all0 hv)
  filter_upwards [hb, high0, took (closeForce_eq V hv), (all0 hv).march h] with z hx hz ht hy
  intro y t
  rw [show Parade _ h y t z = Parade (step0 G V) h y t z from ?_, step0,
      length_at hz (c_bo 0) (F := V) hx (a := 4) (by ring) t y, pA, halfD_eq,
      radialClose_eq_ocean, unitC, LinearMap.smul_apply, Wave.port_spec hz _ (c_bo t) (hy y t)]
  let S := (closeForce V).support ∪ (step0 G V).support
  rw [Page S Finset.subset_union_left, Page S Finset.subset_union_right]
  simp_rw [Finset.sum_apply, ht]

end YM.MS.Graphical
