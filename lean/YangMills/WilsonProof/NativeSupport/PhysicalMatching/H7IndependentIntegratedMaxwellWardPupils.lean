import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneFourSmearedWardReadings
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

noncomputable section
open Set Filter Metric MeasureTheory YangMills
open scoped Topology ContDiff
namespace PhysicalMatching.H7IndependentIntegratedMaxwellWardPupils

def pole : Spacetime := PiLp.single 2 0 1
def centre : Points 2 := WithLp.toLp 2 ![0, pole]
def small {E : Type*} (c : E) : ContDiffBump c :=
  ⟨1 / 32, 1 / 16, by norm_num, by norm_num⟩
def outer : ContDiffBump (0 : Spacetime) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩
def mass : Points 2 → ℝ := (small centre).normed volume
def oneMass : Points 1 → ℝ := (small (0 : Points 1)).normed volume

theorem normalized : (∫ x, mass x) = 1 ∧ (∫ x, oneMass x) = 1 :=
  ⟨(small centre).integral_normed, (small (0 : Points 1)).integral_normed⟩

theorem nearFar {x : Points 2} (hx : x ∈ tsupport mass) :
    dist (x 0) 0 ≤ (1 : ℝ)/16 ∧ dist (x 1) pole ≤ (1 : ℝ)/16 := by
  have h : dist x centre ≤ (1 : ℝ)/16 := by
    change x ∈ tsupport ((small centre).normed volume) at hx
    rw [ContDiffBump.tsupport_normed_eq, mem_closedBall] at hx
    exact hx
  exact ⟨(PiLp.dist_apply_le x centre (0 : Fin 2)).trans h,
         (PiLp.dist_apply_le x centre (1 : Fin 2)).trans h⟩

theorem farFromFirst {x : Points 2} (hx : x ∈ tsupport mass) :
    (1 : ℝ)/2 < dist (x 1) 0 := by
  have h := (nearFar hx).2
  have tri := dist_triangle (0 : Spacetime) (x 1) pole
  have hp : dist (0 : Spacetime) pole = 1 := by simp [pole]
  rw [hp, dist_comm (0 : Spacetime) (x 1)] at tri
  linarith

theorem separatedOnSupport : tsupport mass ⊆ (separated 2 : Set (Points 2)) := by
  intro x hx
  have hn := (nearFar hx).1
  have hf := farFromFirst hx
  have hne : x 0 ≠ x 1 := by intro h; rw [h] at hn; linarith
  change Function.Injective x.ofLp
  intro i j he
  fin_cases i <;> fin_cases j
  · rfl
  · exact False.elim (hne he)
  · exact False.elim (hne he.symm)
  · rfl

theorem actualWindow {x : Points 2} (hx : x ∈ tsupport mass) :
    YangMills.Ward.Window x outer := by
  refine ⟨outer.contDiff, outer.hasCompactSupport, ?_, ?_⟩
  · have h : x 0 ∈ ball (0 : Spacetime) outer.rIn := by
      change dist (x 0) 0 < (1 : ℝ)/8
      linarith [(nearFar hx).1]
    filter_upwards [isOpen_ball.mem_nhds h] with y hy
    exact outer.one_of_mem_closedBall (ball_subset_closedBall hy)
  · intro i
    fin_cases i
    rw [ContDiffBump.tsupport_eq, mem_closedBall]
    change ¬ dist (x 1) 0 ≤ (1 : ℝ)/4
    linarith [farFromFirst hx]

theorem weightSupport (w : Points 2 → ℝ) :
    tsupport (fun x => ((mass x * w x : ℝ) : ℂ)) ⊆ tsupport mass := by
  apply closure_mono
  intro x hx
  change mass x ≠ 0
  intro he
  exact hx (by simp [he])

theorem weightSmooth (w : Points 2 → ℝ)
    (hw : ∀ x ∈ tsupport mass, ContDiffAt ℝ ∞ w x) :
    ContDiff ℝ ∞ (fun x => ((mass x * w x : ℝ) : ℂ)) := by
  have hreal : ContDiff ℝ ∞ (fun x => mass x * w x) := by
    apply contDiff_iff_contDiffAt.2
    intro x
    by_cases hx : x ∈ tsupport mass
    · exact ((small centre).contDiff_normed (μ := volume)).contDiffAt.mul (hw x hx)
    · have hz : ∀ᶠ y in 𝓝 x, y ∉ tsupport mass := isClosed_closure.isOpen_compl.mem_nhds hx
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [hz] with y hy
      have he : mass y = 0 := by
        by_contra he
        exact hy (subset_closure he)
      simp [he]
  exact Complex.ofRealCLM.contDiff.comp hreal

def weightedTest (w : Points 2 → ℝ)
    (hw : ∀ x ∈ tsupport mass, ContDiffAt ℝ ∞ w x) : SeparatedTest 2 where
  toFun x := ((mass x * w x : ℝ) : ℂ)
  contDiff' := weightSmooth w hw
  hasCompactSupport' := ((small centre).hasCompactSupport_normed (μ := volume)).of_isClosed_subset
    isClosed_closure (weightSupport w)
  tsupport_subset' := (weightSupport w).trans separatedOnSupport

def vacuum : SeparatedTest 1 where
  toFun x := (oneMass x : ℂ)
  contDiff' := Complex.ofRealCLM.contDiff.comp ((small (0 : Points 1)).contDiff_normed (μ := volume))
  hasCompactSupport' := by
    apply ((small (0 : Points 1)).hasCompactSupport_normed (μ := volume)).of_isClosed_subset
      isClosed_closure
    apply closure_mono
    intro x hx he
    exact hx (by simp [oneMass, he])
  tsupport_subset' := by
    intro x _
    change Function.Injective x.ofLp
    intro i j _
    exact Subsingleton.elim _ _

def actualPupils (c : Fin 2 → Fin 2 → Points 2 → ℝ) (t : Points 2 → ℝ)
    (hc : ∀ i j x, x ∈ tsupport mass → ContDiffAt ℝ ∞ (c i j) x)
    (ht : ∀ x ∈ tsupport mass, ContDiffAt ℝ ∞ t x) :
    H7StandaloneFourSmearedWardReadings.Pupils where
  vacuum := vacuum
  conservation i j := weightedTest (c i j) (hc i j)
  translation := weightedTest t ht
  cutoff := outer
  window := fun x hx => actualWindow (weightSupport t hx)


def displacement (i : Fin 4) (x : Points 2) : ℝ := (x 0) i - (x 1) i
def radial (x : Points 2) : ℝ := displacement 0 x ^ 2 + displacement 1 x ^ 2 +
  displacement 2 x ^ 2 + displacement 3 x ^ 2
def transverse (x : Points 2) : ℝ := displacement 2 x ^ 2 + displacement 3 x ^ 2
def numerator (x : Points 2) : ℝ := transverse x * (6 * displacement 0 x ^ 2 - radial x)
def common (K : ℝ) (x : Points 2) : ℝ :=
  -8 * K * displacement 0 x * (2 * numerator x - radial x ^ 2)
def crossing (K : ℝ) (x : Points 2) : ℝ :=
  -8 * K * displacement 0 x * (radial x - 2 * transverse x) * (radial x - 3 * transverse x)

theorem coordinateBounds {x : Points 2} (hx : x ∈ tsupport mass) (i : Fin 4) :
    |displacement i x + pole i| ≤ (1 : ℝ)/8 := by
  have a := (PiLp.dist_apply_le (x 0) (0 : Spacetime) i).trans (nearFar hx).1
  have b := (PiLp.dist_apply_le (x 1) pole i).trans (nearFar hx).2
  simp only [Real.dist_eq, PiLp.zero_apply, sub_zero] at a
  simp only [Real.dist_eq] at b
  have ha := abs_le.mp a
  have hb := abs_le.mp b
  apply abs_le.mpr
  dsimp [displacement]
  constructor <;> linarith

theorem bounds {x : Points 2} (hx : x ∈ tsupport mass) :
    displacement 0 x ≤ -(7 : ℝ)/8 ∧ (49 : ℝ)/64 ≤ radial x ∧
      0 ≤ transverse x ∧ transverse x ≤ (1 : ℝ)/32 ∧ displacement 0 x ^ 2 ≤ radial x := by
  have a := coordinateBounds hx 0
  have b := coordinateBounds hx 2
  have c := coordinateBounds hx 3
  have h20 : (2 : Fin 4) ≠ 0 := by decide
  have h30 : (3 : Fin 4) ≠ 0 := by decide
  norm_num [pole, PiLp.single_apply, h20, h30] at a b c
  have ar := (abs_le.mp a).2
  have br := abs_le.mp b
  have cr := abs_le.mp c
  have h0 : displacement 0 x ≤ -(7:ℝ)/8 := by linarith
  have q0 := mul_nonneg (show 0 ≤ -displacement 0 x - (7:ℝ)/8 by linarith)
    (show 0 ≤ -displacement 0 x + (7:ℝ)/8 by linarith)
  have q2 := mul_nonneg (show 0 ≤ (1:ℝ)/8 - displacement 2 x by linarith)
    (show 0 ≤ (1:ℝ)/8 + displacement 2 x by linarith)
  have q3 := mul_nonneg (show 0 ≤ (1:ℝ)/8 - displacement 3 x by linarith)
    (show 0 ≤ (1:ℝ)/8 + displacement 3 x by linarith)
  refine ⟨h0, ?_, ?_, ?_, ?_⟩ <;> dsimp [radial, transverse] <;>
    nlinarith [sq_nonneg (displacement 1 x), sq_nonneg (displacement 2 x), sq_nonneg (displacement 3 x)]

theorem safe {x : Points 2} (hx : x ∈ tsupport mass) :
    0 < radial x ∧ displacement 0 x < 0 ∧ 2 * numerator x < radial x ^ 2 ∧
    0 < radial x - 2 * transverse x ∧ 0 < radial x - 3 * transverse x := by
  obtain ⟨hr, hs, hu, humax, hr2⟩ := bounds hx
  have hp : 0 < radial x := by linarith
  have h10 : 10 * transverse x < radial x := by linarith
  have h10s := mul_lt_mul_of_pos_right h10 hp
  have htu := mul_nonneg hu (sub_nonneg.mpr hr2)
  refine ⟨hp, by linarith, ?_, by linarith, by linarith⟩
  unfold numerator
  nlinarith

def cweight (K : ℝ) (i j : Fin 2) (x : Points 2) : ℝ :=
  (![![radial x ^ 7, -(radial x ^ 7)], ![radial x ^ 5 * (numerator x - radial x ^ 2),
     radial x ^ 5 * numerator x]] : Fin 2 → Fin 2 → ℝ) i j / common K x
def tweight (K : ℝ) (x : Points 2) : ℝ := radial x ^ 7 / crossing K x

theorem denominators {K : ℝ} (hK : 0 < K) {x : Points 2} (hx : x ∈ tsupport mass) :
    common K x ≠ 0 ∧ crossing K x ≠ 0 := by
  obtain ⟨hs, hr, hv, h2, h3⟩ := safe hx
  have hlead : -8 * K * displacement 0 x ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) hK.ne') hr.ne
  exact ⟨mul_ne_zero hlead (sub_ne_zero.mpr hv.ne),
    mul_ne_zero (mul_ne_zero hlead h2.ne') h3.ne'⟩

theorem displacementSmooth (i : Fin 4) : ContDiff ℝ ∞ (displacement i) := by
  let site (j : Fin 2) : Points 2 →L[ℝ] Spacetime := PiLp.proj 2 _ j
  let component : Spacetime →L[ℝ] ℝ := PiLp.proj 2 _ i
  exact (component.contDiff.comp (site 0).contDiff).sub (component.contDiff.comp (site 1).contDiff)

theorem smoothWeights {K : ℝ} (hK : 0 < K) (x : Points 2) (hx : x ∈ tsupport mass) :
    (∀ i j, ContDiffAt ℝ ∞ (cweight K i j) x) ∧ ContDiffAt ℝ ∞ (tweight K) x := by
  have hr (i : Fin 4) := (displacementSmooth i).contDiffAt (x := x)
  have hs : ContDiffAt ℝ ∞ radial x := by
    exact ((((hr 0).pow 2).add ((hr 1).pow 2)).add ((hr 2).pow 2)).add ((hr 3).pow 2)
  have hu : ContDiffAt ℝ ∞ transverse x := ((hr 2).pow 2).add ((hr 3).pow 2)
  have ht : ContDiffAt ℝ ∞ numerator x := hu.mul ((contDiffAt_const.mul ((hr 0).pow 2)).sub hs)
  have hb : ContDiffAt ℝ ∞ (fun y => -8 * K * displacement 0 y) x := contDiffAt_const.mul (hr 0)
  have hd : ContDiffAt ℝ ∞ (common K) x := hb.mul ((contDiffAt_const.mul ht).sub (hs.pow 2))
  have he : ContDiffAt ℝ ∞ (crossing K) x := (hb.mul (hs.sub (contDiffAt_const.mul hu))).mul
    (hs.sub (contDiffAt_const.mul hu))
  obtain ⟨hd0, he0⟩ := denominators hK hx
  refine ⟨?_, (hs.pow 7).div he he0⟩
  intro i j
  fin_cases i <;> fin_cases j
  · exact (hs.pow 7).div hd hd0
  · exact (hs.pow 7).neg.div hd hd0
  · exact ((hs.pow 5).mul (ht.sub (hs.pow 2))).div hd hd0
  · exact ((hs.pow 5).mul ht).div hd hd0

def pupils (K : ℝ) (hK : 0 < K) : H7StandaloneFourSmearedWardReadings.Pupils :=
  actualPupils (cweight K) (tweight K)
    (fun i j x hx => (smoothWeights hK x hx).1 i j)
    (fun x hx => (smoothWeights hK x hx).2)

def gradBlock (K : ℝ) (x : Points 2) (j k : Fin 2) : ℝ :=
  (-8 * K * displacement 0 x / radial x ^ 5) *
    (![![numerator x / radial x ^ 2, 1], ![1 - numerator x / radial x ^ 2, 1]] :
      Fin 2 → Fin 2 → ℝ) j k

def translationDerivative (K : ℝ) (x : Points 2) : ℝ := crossing K x / radial x ^ 7

theorem exactTwoReadings {K : ℝ} (hK : 0 < K) {x : Points 2} (hx : x ∈ tsupport mass)
    (i k : Fin 2) : (∑ j : Fin 2, cweight K i j x * gradBlock K x j k) = if i = k then 1 else 0 := by
  obtain ⟨hs, hr, hv, _, _⟩ := safe hx
  have hden : 2 * numerator x - radial x ^ 2 ≠ 0 := sub_ne_zero.mpr hv.ne
  have hcommon := (denominators hK hx).1
  fin_cases i <;> fin_cases k <;> simp [Fin.sum_univ_succ, cweight, gradBlock] <;>
    field_simp [hcommon, hs.ne'] <;> unfold common <;> ring

theorem exactTranslation {K : ℝ} (hK : 0 < K) {x : Points 2} (hx : x ∈ tsupport mass) :
    tweight K x * translationDerivative K x = 1 := by
  have hs := (safe hx).1.ne'
  have hd := (denominators hK hx).2
  unfold tweight translationDerivative
  field_simp [hs, hd]

private theorem mass_off {x : Points 2} (hx : x ∉ tsupport mass) : mass x = 0 := by
  by_contra hn
  exact hx (subset_closure (show x ∈ Function.support mass from hn))

theorem integratedConservation {K : ℝ} (hK : 0 < K) (i k : Fin 2) :
    (∫ x : Points 2, mass x * (∑ j : Fin 2, cweight K i j x * gradBlock K x j k)) =
      if i = k then 1 else 0 := by
  have point (x : Points 2) :
      mass x * (∑ j : Fin 2, cweight K i j x * gradBlock K x j k) =
        mass x * (if i = k then 1 else 0) := by
    by_cases hx : x ∈ tsupport mass
    · rw [exactTwoReadings hK hx]
    · simp [mass_off hx]
  simp_rw [point]
  rw [MeasureTheory.integral_mul_const, normalized.1, one_mul]

theorem integratedTranslation {K : ℝ} (hK : 0 < K) :
    (∫ x : Points 2, mass x * (tweight K x * translationDerivative K x)) = 1 := by
  have point (x : Points 2) : mass x * (tweight K x * translationDerivative K x) = mass x := by
    by_cases hx : x ∈ tsupport mass
    · rw [exactTranslation hK hx, mul_one]
    · simp [mass_off hx]
  simpa only [point] using normalized.1

theorem integratedVacuum : (∫ x : Points 1, oneMass x) = 1 := normalized.2

end PhysicalMatching.H7IndependentIntegratedMaxwellWardPupils
