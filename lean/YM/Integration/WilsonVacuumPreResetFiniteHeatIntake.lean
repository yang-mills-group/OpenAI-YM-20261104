import YM.Integration.WilsonVacuumPreResetFiniteHeatBudget
import YM.Integration.WilsonVacuumPreResetWindingNodes

/-! Gross finite-side entries of the original affine drawing and of a
selected signed change in the fine action, before the connected heat sum. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetFiniteHeatIntake
open Function Filter Finset Lattice Wilson RG Precision Laurent
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Wheel WilsonCoeffUV.Winding
open scoped Classical BigOperators
variable {G:Gauge}{e:ℕ}{C:Arch G}

theorem predictor(p:ScrollV e C)(u:Woods G (p.n*C.P.L))(z:Woods G p.n):
    |p.cone u z| ≤ C.mass:=by
  have inc:=p.lights.bow
  have paid:=inc.2 (C.peg p.n u) z
  change |allotM (C.peg p.n) (Equiv.refl _) p.cone (C.peg p.n u) z| ≤ _ at paid
  simp only [allotM,Matrix.submatrix_apply,Equiv.symm_apply_apply,Equiv.refl_symm,Equiv.refl_apply] at paid
  apply paid.trans
  apply (mul_le_mul_of_nonneg_left _ inc.1).trans_eq (mul_one _)
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr C.h.le) (by positivity))

theorem noise(p:ScrollV e C)(u z:Joint G (p.n*C.P.L) p.n):
    |fillSlots (Woods G p.n) (mer (G:=G) C.P C.K p.H p.n) u z| ≤ C.mass:=by
  cases u with
  | inr a=>cases z <;> simpa [fillSlots] using zero_le_one.trans C.book
  | inl a=>
    cases z with
    | inr b=>simpa [fillSlots] using zero_le_one.trans C.book
    | inl b=>
      change |mer (G:=G) C.P C.K p.H p.n a b| ≤ C.mass
      have inc:=p.glow.bow
      have paid:=inc.2 (C.peg p.n a) (C.peg p.n b)
      change |allotM (C.peg p.n) (C.peg p.n) (mer (G:=G) C.P C.K p.H p.n) (C.peg p.n a) (C.peg p.n b)| ≤ _ at paid
      simp only [allotM,Matrix.submatrix_apply,Equiv.symm_apply_apply] at paid
      apply paid.trans
      apply (mul_le_mul_of_nonneg_left _ inc.1).trans_eq (mul_one _)
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr C.h.le) (by positivity))

theorem shifted(p:ScrollV e C)(u:Woods G (p.n*C.P.L))(v:Joint G (p.n*C.P.L) p.n):
    |camber G p.cone u v| ≤ C.mass:=by
  classical
  cases v with
  | inl z=>
    simp [camber,Matrix.mul_apply,rightFlag,leftFlag,Matrix.of_apply]
    split <;> simp_all [C.book,zero_le_one.trans C.book]
  | inr z=>
    simpa [camber,Matrix.mul_apply,rightFlag,leftFlag,Matrix.of_apply] using predictor p u z

/-- Applying a genuine unscaled field matrix to a tensor pays only the
coordinate count to its angular rank, even on a winding period. -/
theorem application {U V:Type}[Fintype U](K:Matrix U V ℝ)(P:Gen ℝ U)(r:ℕ)(M A:ℝ)
    (m:0 ≤ M)(a:0 ≤ A)(kernel:∀u v,|K u v| ≤ M)(input:∀x,|P r x| ≤ A)(y):
    |fade K P r y| ≤ ((Fintype.card U:ℝ)*M)^r*A:=by
  unfold fade
  simp only [smul_eq_mul]
  calc
    _ ≤ (Fintype.card (Fin r→U):ℝ)*(M^r*A):=by
      apply WilsonVacuumPreResetFiniteHeatBudget.sum _ _ (mul_nonneg (pow_nonneg m _) a) (by simp)
      intro x _
      rw [abs_mul,Finset.abs_prod]
      apply mul_le_mul _ (input x) (abs_nonneg _) (pow_nonneg m _)
      simpa using (Finset.prod_le_prod (s:=univ) (f:=fun j=>|K (x j) (y j)|)
        (g:=fun _=>M) (fun j _=>abs_nonneg _) (fun j _=>kernel _ _))
    _=_:=by simp [mul_pow,mul_assoc]

/-- The change of a fine action inside the original physical analytic intake.
The Haar and joint penalty cancel here at the same affine drawing. -/
theorem difference {c f:Side}(S:StepData c f)(O:ChartRatio G)(M:Matrix (Woods G f) (Woods G c) ℝ)
    (P D:PChart G f)(t:ℝ)(i r:ℕ)(x):
    casePW S O M (fun j=>P j+t•D j) i r x =
      casePW S O M P i r x - t*fade (camber G M) (scrub D i) r x:=by
  simp only [casePW,Pi.sub_apply,fade,smul_eq_mul,scrub]
  split
  · simp
  · simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_add,Finset.sum_add_distrib]
    simp_rw [mul_left_comm _ t,←Finset.mul_sum]
    ring

/-- Only the signed selected action consumes this gross change tariff. -/
theorem incoming(p:ScrollV e C)(P D:PChart G (p.n*C.P.L))(t:ℝ)(i r:ℕ)(x)
    (small:|t| ≤ 1)(input:∀y,|D i r y| ≤ 1):
    |casePW p.wheel C.R p.cone (fun a=>P a+t•D a) i r x| ≤
      |casePW p.wheel C.R p.cone P i r x| + ((Fintype.card (Woods G (p.n*C.P.L)):ℝ)*C.mass)^r:=by
  have coupon:∀y,|scrub D i r y| ≤ 1:=by intro y;by_cases hi:i=0 <;> simp_all [scrub]
  have paid:=application _ _ r C.mass 1 (zero_le_one.trans C.book) zero_le_one (shifted p) coupon x
  rw [difference]
  apply (abs_sub ..).trans
  rw [abs_mul]
  apply add_le_add le_rfl
  simpa only [one_mul,mul_one] using mul_le_mul small paid (abs_nonneg _) zero_le_one

end YM.Integration.WilsonVacuumPreResetFiniteHeatIntake
end
