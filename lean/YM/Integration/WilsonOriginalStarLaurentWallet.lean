import YM.Integration.WilsonOriginalStarPrimaryCatalog
import YM.Integration.ActualRunKernelPackets

/-! Before-test receipts for each Laurent rank of the independent registered Wilson stencil. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalStarLaurentWallet
open Function Finset Lattice Wilson RG Source Labels PhysicalNext.Repeat.Legato
open PertExtension ActualRunCurvaturePackets NativeCurvatureTensor LocalComparison
open Pert.Asymptotics
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) (d : ℕ)
local notation "F_" => R.family.labels.level d
abbrev Socket := (i : (F_).Index) × ↥(((ofRun R d).data.shape i).support)
def lag (s : Socket R d) := ActualRunGradedKernels.rank R d s.1
def shape (s : Socket R d) := MvPolynomial.coeff s.2.val ((ofRun R d).data.shape s.1)
def length (s : Socket R d) := (⟨fun k=> (ofRun R d).data.columns s.1 (word s.2.val k).1,fun _=>0⟩ :
    Atom G (s.2.val.sum fun _ r=>r)).length

def coefficient (g τ : ℝ) (v : R.family.label d) (s : Socket R d) :=
  (((g/τ)^(lag R d s):ℝ):ℂ)*v s.1*shape R d s

def wallet (a : ℝ) (z : ℕ) :=
    ∑ s : Socket R d, if lag R d s=z then (2:ℝ)^z*‖shape R d s‖*Real.exp (a*length R d s) else 0

theorem normalized (g τ : ℝ) (hg : 0<g) (v : R.family.label d) (s : Socket R d) :
    ((g:ℂ)^(-((lag R d s):ℤ)))*coefficient R d g τ v s =
      (((τ⁻¹)^(lag R d s):ℝ):ℂ)*v s.1*shape R d s := by
  have nz : (g:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hg.ne'
  simp only [coefficient,Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_inv,
    zpow_neg,zpow_natCast,div_pow,inv_pow]
  field_simp

theorem quote (a : ℝ) (z : ℕ) {g τ : ℝ} (hg : 0≤g) (hτ : 0<τ) (rate : g≤2*τ)
    (v : R.family.label d) :
    (∑ s : Socket R d, if lag R d s=z then ‖coefficient R d g τ v s‖*Real.exp (a*length R d s) else 0) ≤
      wallet R d a z * (F_).coeffSize v := by
  rw [wallet,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro s _
  by_cases occupied : lag R d s=z
  · have exactPrice : ‖coefficient R d g τ v s‖=(g/τ)^z*‖v s.1‖*‖shape R d s‖ := by
      unfold coefficient
      rw [occupied,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg (div_nonneg hg hτ.le) z)]
    simp only [if_pos occupied,exactPrice]
    have entry : ‖v s.1‖ ≤ (F_).coeffSize v :=
      Finset.single_le_sum (f:=fun i=>‖v i‖) (fun _ _=>norm_nonneg _) (Finset.mem_univ _)
    have power : (g/τ)^z ≤ (2:ℝ)^z := pow_le_pow_left₀ (div_nonneg hg hτ.le) ((div_le_iff₀ hτ).mpr rate) _
    calc _ ≤ (((2:ℝ)^z*(F_).coeffSize v)*‖shape R d s‖)*Real.exp (a*length R d s) :=
           mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
             (mul_le_mul power entry (norm_nonneg _) (pow_nonneg (by norm_num) _)) (norm_nonneg _)) (Real.exp_nonneg _)
         _ = _ := by ring
  · simp [occupied]

theorem fine (N p k : ℕ) (upper : k≤N) (v : R.family.label d) (a : ℝ) (z : ℕ) :
    let g := regulatorRun R.family N p k
    let τ := (R.family.path.rep N p k).p.threshold
    (∑ s : Socket R d, if lag R d s=z then ‖coefficient R d g τ v s‖*Real.exp (a*length R d s) else 0) ≤
      wallet R d a z*(F_).coeffSize v := by
  intro g τ
  let β := R.family.path.β N p k
  let b := R.family.path.levels.clock.hatBeta k
  have hb : 0<b := zero_lt_one.trans (R.family.path.levels.fits.delayed k)
  have lower : b/2≤β := (R.makes.wilson.represents N p k upper).band.1
  have hβ : 0<β := (half_pos hb).trans_le lower
  have base : (Real.sqrt b)⁻¹ ≤ τ := by
    dsimp only [τ]
    have point : (R.family.path.rep N p k).p=R.family.path.levels.budget k := (R.makes.wilson.represents N p k upper).vac
    rw [point]
    exact le_mul_of_one_le_right (inv_nonneg.mpr (Real.sqrt_nonneg _)) (Real.one_le_exp (sq_nonneg _))
  apply quote R d a z (ActualRunKernelPackets.regulator_pos R N p k upper).le
    (R.family.path.rep N p k).p.threshold_pos _ v
  have rad : Real.sqrt b ≤ 2*Real.sqrt β := by nlinarith [Real.sq_sqrt hb.le, Real.sq_sqrt hβ.le,Real.sqrt_pos.mpr hβ]
  calc g ≤ (Real.sqrt b/2)⁻¹ := inv_anti₀ (half_pos (Real.sqrt_pos.mpr hb)) (by linarith)
       _ = 2*(Real.sqrt b)⁻¹ := by rw [inv_div]; ring
       _ ≤ 2*τ := by gcongr

end YM.Integration.WilsonOriginalStarLaurentWallet
