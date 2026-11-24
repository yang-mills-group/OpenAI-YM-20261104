import YM.Integration.WilsonOriginalPublicPivotWeights
import YM.Integration.WilsonOriginalPublicFigureWickFaces
import YM.Integration.WilsonOriginalPublicFigureIncome
import YM.Integration.WilsonPositionProgramTrialCollarMesh
import YM.Integration.WilsonReflectedRelativeDate

/-! The filed numerical coefficients are projected into a basis of each actual
homogeneous on-shell grade. This rectangular map is applied at the planted mesh. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 500000
namespace YM.Integration.WilsonOriginalPublicPivotRoster
open Filter Finset Matrix Wilson RG Labels PhysicalNext.Repeat.Legato
open XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus XSpace.Structure1 Maxwell Maxwell.Wick
open WilsonOriginalPublicPivotWeights
open WilsonOriginalPublicFigureWick (project)
open WilsonOriginalPublicFigureWickCharge (coin)
open WilsonOriginalMicroscopicGuardedReporters (stretch)
open WilsonOriginalPublicTrialInput (vector fitted salary)
open scoped Classical BigOperators
variable {G:Gauge} {h n:ℕ}

abbrev Slot (G:Gauge) (h:ℕ) := (k:Fin (h+1)) × Fin (Module.finrank ℂ (On.Grade G k.val))
def weight (i:Slot G h) : ℕ:=i.1.val
def basis (k:ℕ) := Module.finBasis ℂ (On.Grade G k)
def pivot (i:Slot G h):Sec G h:=en (Nat.le_of_lt_succ i.1.isLt) (basis (G:=G) i.1.val i.2)
def coord (p:Sec G h) (i:Slot G h):ℂ:=(basis (G:=G) i.1.val).repr (part h i.1.val p) i.2
def change (W:Initialize G) (F:Labels.Frame G h) : Matrix (Slot G h) F.Index ℂ :=
  fun i b=>coord (coin W F b) i
def salaryOf (W:Initialize G) (F:Labels.Frame G h):ℝ:=∑i,∑b,‖change W F i b‖

theorem registered (W:Initialize G) (F:Labels.Frame G h) (v:F.Coeff) (i:Slot G h):
    coord (project W F v) i=∑b,change W F i b*v b:=by
  rw [WilsonOriginalPublicFigureWickCharge.deposited W F v]
  simp [coord,change,map_sum,map_smul,smul_eq_mul,mul_comm]

theorem decomposition (X:Sample n) (p:Sec G h):
    WilsonMaxwellThermometerPositionCurrency.received X 1 p=
      ∑i:Slot G h,((X.F.spacing:ℂ)^(weight i)*coord p i) • pivot i:=by
  rw [Fintype.sum_sigma]
  unfold WilsonMaxwellThermometerPositionCurrency.received
  apply sum_congr rfl
  intro k _
  simp only [Complex.ofReal_one,one_pow,div_one]
  nth_rw 1 [←(basis (G:=G) k.val).sum_repr (part h k.val p)]
  simp only [map_sum,Finset.smul_sum,map_smul,smul_smul,pivot,weight,coord]

theorem measured (W:Initialize G) (F:Labels.Frame G h) (v:F.Coeff) :
    ∑i:Slot G h,‖coord (project W F v) i‖ ≤ salaryOf W F*F.coeffSize v:=by
  rw [salaryOf,Finset.sum_mul]
  apply sum_le_sum;intro i _
  rw [registered W F v i,Finset.sum_mul]
  apply (norm_sum_le ..).trans
  apply sum_le_sum
  intro b _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (single_le_sum (f:=fun x=>‖v x‖) (fun x _=>norm_nonneg _) (mem_univ b)) (norm_nonneg _)

/-- This is the dose on both Figured prints after the own-horizon Wick change,
including the unit. The active map may have fewer columns than the raw map. -/
theorem returned (W:Initialize G) (F:Labels.Frame G h) (v:F.Coeff) (X:Sample n)
    {B:ℝ} (nn:0≤B) (U:Matrix (Slot G h) (Slot G h) ℂ) (paid:Paid X.F.spacing weight weight U B)
    (i:Slot G h):
    ‖∑j,U i j*((X.F.spacing:ℂ)^(weight j)*coord (project W F v) j)‖ ≤
      B*X.F.spacing^(weight i)*(salaryOf W F*F.coeffSize v):=
  (applied X.F.positive.le paid (coord (project W F v)) i).trans
    (mul_le_mul_of_nonneg_left (measured W F v) (mul_nonneg nn (pow_nonneg X.F.positive.le _)))

/-- Choose the already authorized positive unary tolerance after fixing the
collar width. The right side spends a single power for every collar depth. -/
theorem stretch_fee (R:Run G) {j K:ℕ} {η A g:ℝ} (ep:0≤η) (damp:η*A≤1)
    (pos:0<g) (small:g≤1) (age:R.family.S.scale K-R.family.S.scale j≤A*Real.log g⁻¹):
    stretch R η j K≤2*g⁻¹:=by
  have lg:0≤Real.log g⁻¹:=Real.log_nonneg (one_le_inv₀ pos|>.mpr small)
  have bound:η*(R.family.S.scale K-R.family.S.scale j)≤Real.log g⁻¹:=calc
    _ ≤ η*(A*Real.log g⁻¹):=mul_le_mul_of_nonneg_left age ep
    _ ≤ _:=by rw [←mul_assoc];simpa only [one_mul] using mul_le_mul_of_nonneg_right damp lg
  exact mul_le_mul_of_nonneg_left ((Real.exp_le_exp.mpr bound).trans_eq (Real.exp_log (inv_pos.mpr pos))) (by norm_num)

variable (R:Run G)(g j:Fin 3→ℕ)(K target:ℕ)(η:ℝ)(M:Fin 3→ℝ)
  (Y:∀a:Fin 3,ℕ×ℕ→R.family.label (g a))(before:∀a,j a≤K)
  (registered₀:WilsonOriginalMicroscopicGuardedPageSchool.Indexed R g j target η M Y)
local notation "F" a:max => R.family.labels.level (g a)
local notation "v" N:max p:max => vector R g j K target η M Y before registered₀ N p

theorem inlet (N p:ℕ)(top:K<N)(a:Fin 3):
    (F a).coeffSize ((v N p) a)≤2^(WilsonOriginalPublicFigureIncome.height R (g a))*salary R g j K η M a:=by
  have entry:=(WilsonOriginalPublicTrialInput.original R g j K target η M Y before registered₀ N p top).1 a
  rw [vector,if_pos top]
  exact (WilsonPositionProgramReportedField.purchased R (g a) K (N,p) top.le _).trans
    (mul_le_mul_of_nonneg_left entry.2 (by positivity))

end YM.Integration.WilsonOriginalPublicPivotRoster
end
