import YM.RGReadout.Capture.Charge
import YM.Pert.Asymptotics.RawAxis
import YM.OPE.Log.Fees
import YM.OPE.Levy.Invoice
import YM.Planned.PRIMARY_INTEGRAL_295.Stain

/-!
# Coupling and literal normalized fields at every reporting level

Top fields are actual `C.O`, transformed (uniformly in location) by the
inverse projection of their exact charge at 0 through level i. This
literal scheme uses `runProbe` from full lifted radial `Hol.testLinks`;
winding terms not discarded. Converts threshold to coupling coordinates at
the requested level. No test derivatives here (intermediate literal
scheme).
-/

set_option autoImplicit false
noncomputable section
namespace YM.RGReadout.Literal
open Filter Function MeasureTheory Wilson Lattice RG Source Extra.Histories
open MergeProof MergeProof.Accent MergeProof.Ribbons Trace.Physical Trace.Physical.GermGraph
open Work.G08 Bid Next.Rank Next.UVStress Price OPE
open Planned.PrimaryIntegral295 PPX
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical

variable {G : Gauge} (C : Family G) (H : C.Makes) (d k N p : ℕ)

theorem shrink_ledger (k N p : ℕ) : Price.shrink C k N p =
    Pert.Asymptotics.regulatorRun C N p k / C.path.levels.clock.threshold k := rfl

/-- Threshold to g conversion is `symm` of this. -/
def toThreshold (hp : k ≤ N) : C.label d ≃ₗ[ℂ] C.label d :=
  { toLinearMap := (C.labels.level d).scaled (Price.shrink C k N p)⁻¹
    invFun := (C.labels.level d).scaled (Price.shrink C k N p)
    left_inv := (C.labels.level d).scaled_inv (Price.shrink_pos C H hp p).ne'
    right_inv := fun x => by
      change (C.labels.level d).scaled (Price.shrink C k N p)⁻¹ ((C.labels.level d).scaled _ x) = x
      simpa only [inv_inv] using (C.labels.level d).scaled_inv (inv_ne_zero (Price.shrink_pos C H hp p).ne') x }

/-- The actual normalized fields between reference and k. -/
def meter (h : Opened C d k p) (hp : k ≤ N) : C.label d ≃ₗ[ℂ] C.label d :=
  let T := fitting d N p k H h hp
  let U := toThreshold C H d k N p hp
  let S := LinearEquiv.smulOfNeZero ℂ (C.label d) (spacing C k d) (spacing_ne C k d)
  ((U.trans S).trans T.symm).trans (C.factory d N p).terminal

theorem reads_meter (h : Opened C d k p) (hp : k ≤ N) (x : C.label d) :
    measuring C d N p k ((C.factory d N p).terminal.symm (meter C H d k N p h hp x)) =
      spacing C k d • (C.labels.level d).scaled (Price.shrink C k N p)⁻¹ x := by
  unfold meter
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  apply LinearEquiv.apply_symm_apply (fitting d N p k H h hp)

theorem charge_meter (h : Opened C d k p) (hp : k ≤ N) (x : C.label d) :
    HasProjection C N p d k hp (C.O N p (meter C H d k N p h hp x) 0)
      (spacing C k d • (C.labels.level d).scaled (Price.shrink C k N p)⁻¹ x) := by
  let B := (C.factory d N p).terminal
  let y := meter C H d k N p h hp x
  have hQ := entryOk d N p k H h.post hp (B.symm y)
  refine ⟨_,⟨_,hQ⟩,?_,(reads_meter C H d k N p h hp x).symm⟩
  have hh := cylinder_charges (p:=p) C H h.post hp (B.symm y)
  rw [show (C.factory d N p).terminal (B.symm y)=y from B.apply_symm_apply y] at hh
  exact hh.symm

/-- The vector in k's literal reporting coordinates from matching at an
older stop u, using exactly u's fitted full germ. Only used when the
terminal projection is available. -/
def report (u : ℕ) (hu : Opened C d u p) (hk : Opened C d k p)
    (h : u ≤ N) (hp : k ≤ N) (f : Config G (C.side N p) → ℂ) : C.label d :=
  let z := projection C N p d u h f
  (meter C H d k N p hk hp).symm
    ((C.factory d N p).terminal ((fitting d N p u H hu h).symm z))

lemma report_exact (u : ℕ) (hu : Opened C d u p) (hk : Opened C d k p)
    (h : u ≤ N) (hp : k ≤ N) (f : Config G (C.side N p) → ℂ) :
    measuring C d N p u ((C.factory d N p).terminal.symm (meter C H d k N p hk hp
      (report C H d k N p u hu hk h hp f))) = projection C N p d u h f := by
  unfold report
  simp only [LinearEquiv.symm_apply_apply,LinearEquiv.apply_symm_apply]
  apply LinearEquiv.apply_symm_apply (fitting d N p u H hu h)

def lensPrice (d i : ℕ) := (2*C.path.levels.clock.monitor i)^d

lemma lensPrice_pos (d i : ℕ) : 0 < lensPrice C d i :=
  pow_pos (mul_pos zero_lt_two (Real.exp_pos _)) _

lemma shrunk_cost (hp : k ≤ N) (x : C.label d) :
    (C.labels.level d).coeffSize (toThreshold C H d k N p hp x) ≤
      lensPrice C d k * (C.labels.level d).coeffSize x := by
  let a := Price.shrink C k N p
  let w := C.path.levels.clock.monitor k
  let F := C.labels.level d
  have he : a⁻¹ ≤ 2*w := Price.shrink_min C H hp p
  have ha : 0 < a := Price.shrink_pos C H hp p
  change F.coeffSize (F.scaled a⁻¹ x) ≤ (2*w)^d * F.coeffSize x
  unfold Labels.Frame.coeffSize
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Labels.Frame.scaled_apply,norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have h : 1 ≤ w := Real.one_le_exp (sq_nonneg _)
  exact (pow_le_pow_left₀ (by positivity) he _).trans
    (pow_le_pow_right₀ (by linarith) (Film.second_fits F i))

lemma meter_paid (h : Opened C d k p) (hp : k ≤ N) (x : C.label d) :
    Spindle.paid C d k N p (meter C H d k N p h hp x) ≤
      2*lensPrice C d k * (C.labels.level d).coeffSize x := by
  let U := meter C H d k N p h hp x
  let F := C.labels.level d
  let v := (C.factory d N p).terminal.symm U
  have he : fitting d N p k H h hp v = spacing C k d • toThreshold C H d k N p hp x :=
    reads_meter C H d k N p h hp x
  have ht := (size_gap d N p k H h hp v).2
  change _ ≤ 2*F.coeffSize (fitting d N p k H h hp v) at ht
  rw [he, Size.smul,spacing,norm_pow,Complex.norm_real,Real.norm_of_nonneg (C.S.a_pos _).le] at ht
  apply le_of_mul_le_mul_left _ (pow_pos (C.S.a_pos k) d)
  rw [Log.obey_quota]
  apply ht.trans
  linarith only [mul_le_mul_of_nonneg_left (shrunk_cost C H d k N p hp x) (pow_pos (C.S.a_pos k) d|>.le)]

lemma monitor_rate (hG : G.Simple) : RateIs atTop C.S.scale C.path.levels.clock.monitor 0 := by
  have hm : RateLE atTop C.S.scale C.path.levels.clock.monitor 0 :=
    (Levy.station_monitor C hG 1).congr (Eventually.of_forall fun _ => Real.rpow_one _)
  exact RateIs.of_sandwich (RateIs.const C.S.divergent one_pos) hm
    (Eventually.of_forall fun i => Real.one_le_exp (sq_nonneg _))
    (Eventually.of_forall fun _ => le_rfl) C.S.divergent
lemma lens_price_rate (hG : G.Simple) (d : ℕ) : Note C.S (lensPrice C d) 0 :=
  let h : RateIs atTop C.S.scale (lensPrice C d) 0 :=
    (((RateIs.const C.S.divergent zero_lt_two).mul (monitor_rate C hG)).power d).swap (by ring)
  ⟨lensPrice_pos C d,h.rate⟩

variable {C : Family G}
lemma Opens.meta_cost (H : C.Makes) (d k N p : ℕ) (h : Opened C d k p)
    (hp : k ≤ N) (x : C.label d) :
    ‖x‖ ≤ outward C d k * (2*(C.labels.level d).coeffSize
      (measuring C d N p k ((C.factory d N p).terminal.symm x))) := by
  exact ((Size.norm_le ..).trans (at_current C H h.post hp p x)).trans
    (mul_le_mul_of_nonneg_left (size_gap d N p k H h hp ((C.factory d N p).terminal.symm x)).2
      (zero_le_one.trans (outward_nn C d k)))

end YM.RGReadout.Literal
