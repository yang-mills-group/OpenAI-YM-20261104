import YM.Comparison.RG02.Algebra.Series

/-!
# Actual vs. jet arithmetic -- division costs

Keep the quotient/log of one entire polynomial. First estimate is a truncation bill with
an actual denominator bound (only useful in ports which can pay for it; doesn't claim
uniformly applicable in extensive unnormalized variables). Second is the *connected*
remaining marker cost after an additive output model has been taken out multiplicatively;
this form needn't Taylor-estimate an extensive scalar before taking its logarithm.

No norm other than explicit weighted coefficient cost used here. `%norm` in estimates below
on real/complex numbers is the ordinary absolute value/modulus.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Comparison.RG02
open Marker PowerSeries Finset
open scoped BigOperators

variable {V : Type*} [DecidableEq V] {R : Census V}

/-- Normalize by the unmarked coefficient. Use with hypothesis! -/
def normalizeMass (x : Poly R) : Poly R := (x.part R.quiet)⁻¹ • x

lemma normalizeMass_quiet {x : Poly R} (h : x.part R.quiet ≠ 0) :
    (normalizeMass x).part R.quiet = 1 := by rw [normalizeMass, Poly.part_smul, inv_mul_cancel₀ h]

lemma normalizeMass_product (x y : Poly R) :
    normalizeMass (x*y) = normalizeMass x * normalizeMass y := by
  unfold normalizeMass
  rw [smul_mul_assoc, mul_smul_comm, Poly.quiet_mul, mul_inv, smul_smul]

lemma normalizeMass_fixed {x : Poly R} (h : x.part R.quiet=1) :
    normalizeMass x = x := by unfold normalizeMass; rw [h, inv_one, one_smul]

lemma normalizeMass_maps {W : Type*} [DecidableEq W] {T : Census W} (x : Poly R)
    (F : Poly R →ₐ[ℂ] Poly T) (h : (F x).part T.quiet=x.part R.quiet) :
    F (normalizeMass x) = normalizeMass (F x) := by unfold normalizeMass; rw [map_smul,h]

def massLog [Fintype V] (x : Poly R) : Poly R := Extra.Trajectories.connected (normalizeMass x)

lemma massLog_product [Fintype V] {x y : Poly R} (hx : x.part R.quiet≠0) (hy : y.part R.quiet≠0) :
    massLog (x*y) = massLog x + massLog y := by
  unfold massLog; rw [normalizeMass_product]; exact connected_product (normalizeMass_quiet hx) (normalizeMass_quiet hy)

lemma massLog_pass [Fintype V] {x : Poly R} (hx : x.part R.quiet=0) :
    massLog x.pass = x := by rw [massLog,normalizeMass_fixed (Poly.pass_part ..), connected_pass hx]; exact hx

lemma massLog_maps {W : Type*} [DecidableEq W] {T : Census W} [Fintype V] [Fintype W]
    (F : Poly R →ₐ[ℂ] Poly T) (H : ∀ x, (F x).part T.quiet = x.part R.quiet) {x : Poly R}
    (hx : x.part R.quiet ≠ 0) : F (massLog x)=massLog (F x) := by
  unfold massLog; rw [connected_maps _ H (normalizeMass_quiet hx), normalizeMass_maps _ F (H x)]

lemma massLog_entry [Fintype V] {x : Poly R} (h : x.part R.quiet ≠ 0) :
    (massLog x).part R.quiet=0 := Extra.Trajectories.connected_quiet (normalizeMass_quiet h)

namespace Tape

def approx (x : Tape R) (n : ℕ) (z : ℂ) := through (RingHom.id _) x n (Poly.bead R z)

def spill (x y : Tape R) (n : ℕ) (z : ℂ) := overflow (RingHom.id _) x y n (Poly.bead R z)

lemma approx_sum (x : Tape R) (n : ℕ) (z : ℂ) :
    x.approx n z = ∑ i ∈ Finset.range (n+1), z^i • coeff i x := by
  unfold approx through; simp_rw [RingHom.id_apply, ← map_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm, Poly.product_bead]

lemma approx_part (x : Tape R) (n : ℕ) (t : ℂ) (p : R.Mode) :
    (x.approx n t).part p = ∑ j∈Finset.range (n+1), t^j*(coeff j x).part p := by
  rw [approx_sum,Poly.part_sum]; simp only [Poly.part_smul]

lemma approx_congr {x y : Tape R} {n : ℕ} (h : sameThrough n x y) (t : ℂ) :
    approx x n t=approx y n t := by
  rw [approx_sum,approx_sum]
  exact Finset.sum_congr rfl fun i hi => congr_arg (fun a : Poly R => t^i • a) (h i (Nat.le_of_lt_succ (mem_range.mp hi)))

lemma approx_product (x y : Tape R) (n : ℕ) (z : ℂ) :
    approx x n z * approx y n z = approx (x*y) n z + z^(n+1) • spill x y n z := by
  unfold approx spill
  rw [through_product,mul_comm (overflow ..), ← map_pow, Poly.product_bead]

lemma approx_scalar_only (x : Tape R) (n : ℕ) (z : ℂ) :
    approx (fixScalar _ (scalar _ x)) n z = Poly.bead R ((approx x n z).part R.quiet) := by
  ext p; rw [approx_part]
  change (∑ _ ∈ _, _) = (Poly.send R.quiet _).part p
  rw [Poly.part_send]; split
  next h => simp_rw [h, fixScalar_part, scalar_part]; exact (approx_part ..).symm
  next h => simp [fixScalar_part,h]

lemma approx_hotLog_quiet [Fintype V] {x : Tape R} (hx : x.entryOne) (n : ℕ) (z : ℂ) :
    (approx (hotLog x) n z).part R.quiet=0 := by
  rw [approx_part]; simp_rw [← scalar_part,scalar_hotLog hx,map_zero,mul_zero,sum_const_zero]

end Tape
open Tape

/-- Product overflow survives even with perfect input expansions.
`f` is the modeled expansion after exact known scalars factored. -/
def quotientDefect (f : Tape R) (n : ℕ) (t : ℂ) (r : Poly R) :=
    r - (r.part R.quiet) • (approx f.normal n t) -
      t^(n+1) • spill (fixScalar _ (scalar _ f)) f.normal n t

/-- Identity in the *evaluated* algebra, not in the quotient by g truncation. -/
theorem quotient_rule (x r : Poly R) (hz : x.part R.quiet ≠ 0)
    (f : Tape R) (hF : entryOne f) (n : ℕ) (t : ℂ) (h : x=approx f n t + r) :
    normalizeMass x - approx f.normal n t =
      (x.part R.quiet)⁻¹ • quotientDefect f n t r := by
  have he := approx_product (fixScalar _ (scalar _ f)) f.normal n t
  rw [normal_mul hF, approx_scalar_only, Poly.product_bead] at he
  have hI : x - (x.part R.quiet) • approx f.normal n t = quotientDefect f n t r := by
    rw [h, Poly.part_plus, add_smul, he]; unfold quotientDefect; abel
  calc
    _ = (x.part R.quiet)⁻¹ • (x - (x.part R.quiet) • approx f.normal n t) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hz, one_smul, normalizeMass]
    _ = _ := by rw [hI]

/-- If working with reweighted K or small systems this can be applied to
propagate an estimate. No automatic application to extensive vacuum factors.
Use exact expression `quotientDefect` BEFORE taking prices if cancellations matter. -/
theorem quotient_rule_price {x r : Poly R} {μ : ℝ} (hμ : 0 < μ) (hx : μ ≤ ‖x.part R.quiet‖)
    (f : Tape R) (hF : entryOne f) (n : ℕ) (t : ℂ) (h : x=approx f n t+r)
    (w : V → ℝ) (hw : ∀ i,0<w i) :
    Poly.price w (normalizeMass x-approx f.normal n t) ≤
      μ⁻¹ * Poly.price w (quotientDefect f n t r) := by
  rw [quotient_rule _ r (norm_pos_iff.mp (hμ.trans_le hx)) _ hF n t h,
    Poly.adapted, norm_inv]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ hμ hx) (Poly.nonnegative hw _)

lemma price_minus {p : Poly R} {w : V → ℝ} : Poly.price w (-p)=Poly.price w p := by simp only [Poly.price, Poly.part_neg,norm_neg]

private lemma cost_sub (p q : Poly R) {w : V → ℝ} (hw : ∀ i,0<w i) :
    Poly.price w (p-q) ≤ Poly.price w p + Poly.price w q := by
  rw [sub_eq_add_neg]; exact (Poly.addition hw ..).trans_eq (by rw [price_minus])

-- Relative pressure bound; prefer this over an isolated absolute partition estimate.
def relativeMarked (x : Poly R) := x - Poly.bead _ (x.part R.quiet)

def factors (n : ℕ) (B : ℝ) := ∑ i∈Finset.range n, ((i+1:ℕ):ℝ)⁻¹ * B^i

lemma normalize_relative (x : Poly R) (h : x.part R.quiet ≠ 0) :
    normalizeMass x - 1 = (x.part R.quiet)⁻¹ • relativeMarked x := by
  unfold relativeMarked; rw [smul_sub, Algebra.smul_def (x.part R.quiet)⁻¹ (Poly.bead R (x.part R.quiet))]
  rw [show algebraMap ℂ (Poly R) = Poly.bead R from rfl, ← map_mul, inv_mul_cancel₀ h,map_one]; rfl

lemma relative_cumulant_cost [Fintype V] (x : Poly R) (h : x.part R.quiet ≠ 0)
    {w : V → ℝ} (hw : ∀ i,0<w i) (B : ℝ) (hb : Poly.price w (relativeMarked x) ≤ ‖x.part R.quiet‖ * B) :
    Poly.price w (massLog x) ≤ B * factors (Fintype.card V) B := by
  have hh : Poly.price w (normalizeMass x-1) ≤ B := by
    rw [normalize_relative x h, Poly.adapted,norm_inv]
    exact (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq (by rw [inv_mul_cancel_left₀]; exact norm_ne_zero_iff.mpr h)
  have hp := Poly.nonnegative hw (normalizeMass x-1)
  rw [massLog, ← logTerms_eq (normalizeMass x) (normalizeMass_quiet h)]
  unfold logTerms factors
  refine (Poly.batch hw ..).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Poly.adapted, norm_div, norm_pow]
  have hm : ‖(↑(i+1:ℕ) : ℂ)‖ = ((i+1:ℕ) : ℝ) := by norm_cast
  simp only [hm,norm_neg,norm_one,one_pow,one_div]
  refine le_trans (mul_le_mul_of_nonneg_left ((Poly.powers hw ..).trans (pow_le_pow_left₀ hp hh _)) (by positivity)) ?_
  exact le_of_eq (by rw [pow_succ]; ring)

-- One example of a finite-order payment making no smoothness assumptions and using
-- literal weighted costs. The estimates on extensive quantities are NOT hypotheses asserted
-- in the comparison; hence no uniform constant from this automatically.
theorem rplus_price {x e : Poly R} {μ U Vc W D : ℝ} (hμ : 0 < μ) (hx : μ ≤ ‖x.part R.quiet‖)
    (f : Tape R) (hF : entryOne f) (n : ℕ) (z : ℂ) (h : x=approx f n z+e)
    (w : V → ℝ) (hw : ∀ i,0<w i) (hb : Poly.price w e ≤ U*‖z‖^(n+1))
    (hc : ‖e.part R.quiet‖ ≤ Vc*‖z‖^(n+1))
    (hd : Poly.price w (approx f.normal n z) ≤ D)
    (hW : Poly.price w (spill (fixScalar _ (scalar _ f)) f.normal n z) ≤ W) :
    Poly.price w (normalizeMass x-approx f.normal n z) ≤
      μ⁻¹ * (U+Vc*D+W) * ‖z‖^(n+1) := by
   let a := e.part R.quiet
   let d := approx f.normal n z
   let y := spill (fixScalar _ (scalar _ f)) f.normal n z
   have hj : Poly.price w (quotientDefect f n z e) ≤ (U+Vc*D+W)*‖z‖^(n+1) := by
     refine (cost_sub (e - a • d) (z^(n+1) • y) hw).trans ((add_le_add_left (cost_sub e (a • d) hw) _).trans ?_)
     rw [Poly.adapted,Poly.adapted,norm_pow]
     have he' : ‖a‖*Poly.price w d≤ Vc*‖z‖^(n+1)*D := mul_le_mul hc hd (Poly.nonnegative hw _) ((norm_nonneg _).trans hc)
     exact (add_le_add (add_le_add hb he') (mul_le_mul_of_nonneg_left hW (by positivity))).trans_eq (by ring)
   exact (quotient_rule_price hμ hx f hF n z h w hw).trans ((mul_le_mul_of_nonneg_left hj (by positivity)).trans_eq (by ring))

end YM.Comparison.RG02
