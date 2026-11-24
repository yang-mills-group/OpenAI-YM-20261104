import YM.FVA2.Slice.Coordinates
import YM.PertExtension.GaussianIBP
/-!
# Landau-gauge density at the regulator

Uses counting measure / 2 on Site both for real links and the ghosts. We suppose torus n Even
when using this prescription as the orbifold LPT. In particular for ghosts the mean is zero with
respect to this choice, involving also every fixed site. The FP matrix computed by differentiating
the analytic gauge action with this choice of modes is used in the finite diagram calculation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Slice
open Function Set Filter Finset Lattice MeasureTheory
open MS MS.Koszul MS.Cylinder MS.Cylinder.Taylor MS.City MS.Orbit MS.Tone MS.Landau
open MS.Native MS.Native.Chart MS.Bare
open Pert Orb PertExtension.Series PertExtension.GaussianScore
open scoped BigOperators Matrix Topology ContDiff InnerProductSpace
variable {G : Gauge} {n : Side}
local notation "C" => G.ColorIndex
local notation "T" => Site n
local notation "L" => Transverse G n
local notation "Z" => SiteGhost G n

/-- Counting half the periodic action on equivariant real transverse links. This is the positive
action. -/
def W (G : Gauge) (n : Side) (a : Transverse G n) := Wilson.energy (nation (includeA G n a))/2

/-- Real formula for each color and plaquette convention agrees with `Original_W`. -/
lemma W_rent (a : L) : Chart.rent (drive n) (includeA G n a)= -2 * W G n a := by
  rw [Chart.original_W, W]; ring

def incCL (G : Gauge) (n : Side) : Transverse G n →L[ℝ] Chart.City G (Site n) where
  toLinearMap := includeA G n
  cont := continuous_subtype_val.comp continuous_subtype_val

lemma W_smooth (G : Gauge) (n : Side) : germ (W G n) := by
  let inc : Transverse G n →L[ℝ] Chart.City G (Site n) := incCL G n
  rw [show W G n = (-(1/2):ℝ) • (Chart.rent (drive n) ∘ inc) from funext fun x => by
    change _ = (-(1/2):ℝ)* (Chart.rent _ (includeA G n x)); rw [W_rent]; ring]
  have he : ContDiffAt ℝ ω (Chart.rent (drive n)) (inc 0) := (inc.map_zero).symm ▸ rent_s (drive n)
  exact (he.comp (f:=inc) 0 (ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=Transverse G n) (F:=Chart.City G (Site n)) inc).contDiffAt).const_smul (-(1/2):ℝ)

lemma W_eq (a : L) : W G n a = action G n a.val := by
  have H (x : T) : takeDiv x a.val = 0 := congr_fun (div_none a) x
  rw [action, fixing]; simp only [H,norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero, zero_div, add_zero]
  unfold W wilson; congr 1
  unfold Wilson.energy; rw [Fintype.sum_prod_type (α₁:=Site n)]
  apply Finset.sum_congr rfl; intro i _
  let f (p : Axis × Axis) := G.price (plaquette a.val i p.1 p.2)
  calc
    _ = ∑ q : PlaqAxes, f q.val := Finset.sum_congr rfl (fun q _ => by
      rw [← Chart.plaza]; apply congr_arg G.price
      simp only [plaquette,Chart.atCart, Function.comp_apply,Chart.loadC]; simp; rfl )
    _ = ∑ p : Axis × Axis with p.1 < p.2, f p :=
      (Finset.sum_subtype _ (by simp) f).symm
    _ = _ := by rw [Finset.sum_filter,Fintype.sum_prod_type]

/-- Hessian of the Landau W in this linear gauge; F03 calculation against the same Wilson
log-link chart. -/
def P (G : Gauge) (n : Side) : Transverse G n →ₗ[ℝ] Module.Dual ℝ (Transverse G n) :=
  let s := (LinearMap.ker (dLin (G:=G) (n:=n))).subtype
  LinearMap.mk₂ ℝ (fun x y => formL G n (s x) (s y)) (fun x y z => by simp) (fun c x y => by simp)
    (fun x y z => by simp) (fun c x y=> by simp)

lemma limit_W (v : L) : Tendsto (fun t:ℝ => W G n (t • v) / t^2) (𝓝[≠] 0) (𝓝 (P G n v v /2)) := by
  simp_rw [W_eq]; exact limit_action v.val

lemma sym_P (v z : L) : P G n v z=P G n z v := form_symm ..
lemma W_origin (G : Gauge) (n : Side) : W G n 0=0 ∧ fderiv ℝ (W G n) 0=0 ∧
    ∀ (v z : Transverse G n), iteratedFDeriv ℝ 2 (W G n) 0 ![v,z]=P G n v z := Work.F03.hessian_of_limit ((W_smooth G n).of_le le_top) limit_W (by intro x y z; simp) sym_P

lemma jet_W (v : L) : Radial.jet (W G n) 2 v=P G n v v/2 := by
  unfold Radial.jet
  rw [show (fun _ : Fin 2 => v) = ![v,v] from funext (fun i => by fin_cases i <;> rfl), (W_origin G n).2.2]
  norm_num [Nat.factorial]; ring
lemma pin_P (v : L)(h:v≠0) : 0<P G n v v := form_pos (fun h' => h (Subtype.ext h'))
lemma jet_pos (v:L)(h:v≠0) : 0<Radial.jet (W G n) 2 v := by rw [jet_W]; exact half_pos (pin_P v h)

def gaussian (G : Gauge) (n : Side) : Law (Transverse G n) where
  P := P G n
  turns := sym_P
  slope := by
    obtain ⟨c,hc,ht⟩ := Radial.quadratic_min (W G n) jet_pos
    simp_rw [jet_W] at ht; exact ⟨c,hc,ht⟩
  smooth := by
    -- use continuity of continuous multilinear form from jet
    rw [show (fun x:Transverse G n => P G n x x)= fun x:Transverse G n => (2:ℝ) * Radial.jet (W G n) 2 x from funext (fun x => by rw [jet_W]; ring)]
    unfold Radial.jet
    exact continuous_const.mul (continuous_const.mul ((iteratedFDeriv ℝ 2 (W G n) 0).coe_continuous.comp (continuous_pi fun _=> continuous_id)))
lemma gaussian_kernel : Radial.kernel (W G n) = (gaussian G n).kern := by
  funext x; unfold Law.kern Radial.kernel; rw [jet_W]; congr 1; rw [neg_div]; rfl

-- Density and FP
/-- Real log density excluding FP, from Haar in the actual log chart. -/
def haar (G : Gauge) (n : Side) (x : Transverse G n) := Chart.totalH (includeA G n x) / 2
lemma haar_smooth (G : Gauge) (n : Side) : germ (haar G n) := by
  let inc : Transverse G n →L[ℝ] Chart.City G (Site n) := incCL G n
  have h : ContDiffAt ℝ ω totalH (inc 0) := inc.map_zero.symm ▸ nice_totalH
  exact ((h.comp (f:=inc) 0 (ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=Transverse G n) (F:=Chart.City G (Site n)) inc).contDiffAt).div_const _ :
    germ (fun x => (totalH ∘ inc) x /2))
lemma haar_zero : haar G n 0 = 0 := by simp [haar,totalH,Maurer.lac,LocalH.spin_zero]

/-- Link scalar product (also used to define the Landau condition). -/
def linkPair (X Y : Chart.City G T) := (∑ x : Edge T, inner ℝ (X x) (Y x))/2
/-- Gauge-sector vertex; it will be used for column ghosts `c` and row antighosts (variables
unnormalized here). Denominator is the FP det at zero field. -/
def pair (v : L) (a b : Z) : ℝ := linkPair (gM a).val (Chart.roam (drive n) (includeA G n v) b.val)
lemma roam_analytic (b : Lot G T) : germ (fun a : L => Chart.roam (drive n) (includeA G n a) b) := by
  -- all chart letters
  apply contDiffAt_pi.mpr
  intro i
  let m := Maurer.volts (Chart.route (drive n) i b)
  let c : L →L[ℝ] G.Color := ContinuousLinearMap.proj i ∘L incCL G n
  exact ((c.map_zero.symm ▸ Maurer.home (Chart.route (drive n) i b) : ContDiffAt ℝ ω m (c 0)).comp (f:=c) 0 (ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=Transverse G n) (F:=G.Color) c).contDiffAt)
lemma pair_smooth (a b : Z) : germ (fun v:L => pair v a b) := by
  unfold pair linkPair
  refine (ContDiffAt.sum (fun x _=> ?_)).div_const _
  exact contDiffAt_const.inner ℝ (contDiffAt_pi.mp (roam_analytic (G:=G) (n:=n) b.val) x)
lemma roam_zero (b : Lot G T) : roam (drive n) (0:Chart.City G T) b = -(grad b) := by
  funext i; change Maurer.volts _ 0 = _; rw [Maurer.volt_zero]; change _-_ = -(b i.1 - b _); rw [neg_sub]; rfl
lemma pair_zero (a b : Z) : pair (0:L) a b= -linkPair (gM a).val (gM b).val := by
  rw [pair, map_zero, roam_zero]; unfold linkPair; simp only [Pi.neg_apply, inner_neg_right, Finset.sum_neg_distrib, neg_div]; rfl
end YM.FVA2.Slice
