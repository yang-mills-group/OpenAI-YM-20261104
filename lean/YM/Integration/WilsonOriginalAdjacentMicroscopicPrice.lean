import YM.Integration.WilsonOriginalCoordinateBirthRadius
import YM.Integration.WilsonCoherentTerminalFrame
import YM.Integration.WilsonWindowReportingPace

/-! The complete microscopic group observable one true transfer above a
reporting coordinate. The price uses the backward inequality on the actual
calibrated factory and retains its engineering rescaling. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalAdjacentMicroscopicPrice
open Function Finset Filter Lattice RG Wilson Source Labels Next.Foundations FVA1 WilsonLimitConstruction PhysicalNext.Repeat
open PhysicalNext.Repeat.Legato Next.Rank.Price
open scoped Classical BigOperators
universe u
variable {G:Gauge} (R:Run G) (d:ℕ)
local notation "F" => R.family.labels.level d
local notation "A" => R.family.path.levels
local notation "S" => R.family.S
local notation "C" => R.family

def height:=univ.sup (fun i:(F).Index=>((F).grades i).2)

theorem group : ∃ c:ℝ,1≤c ∧ ∀ (N p:ℕ) (v:(C).label d) (o:Site ((C).side N p)) (U:Config G ((C).side N p)),
    ‖(C).O N p v o U‖ ≤ c*(F).coeffSize (WilsonCoherentTerminalFrame.coordinates R N p v):=by
  obtain ⟨c,hc,full⟩:=Next.Foundations.full_value_bound (G:=G) d
  refine ⟨c,hc,?_⟩
  intro N p v o U
  let z:=WilsonCoherentTerminalFrame.coordinates R N p v
  have form:(C).O N p v o U=∑j,z j*(localSection G d).places (Pi.single j 1) o U:=WilsonCoherentTerminalFrame.row R N p v o U
  rw [form]
  calc
    _ ≤ ∑j,‖z j‖*‖(localSection G d).places (Pi.single j 1) o U‖ := by simpa only [norm_mul] using norm_sum_le (s:=univ) (f:=fun j=>z j*(localSection G d).places (Pi.single j 1) o U)
    _ ≤ ∑j,‖z j‖*c :=sum_le_sum fun j _=>mul_le_mul_of_nonneg_left ((full j).2 _ o U) (norm_nonneg _)
    _ = _:=by rw [←sum_mul,mul_comm];rfl

private theorem scale (N p:ℕ) (ref:(C).ref d ≤ N) (v:(C).label d):
    (F).coeffSize (WilsonCoherentTerminalFrame.coordinates R N p v) ≤
       ((A).clock.hatBeta N)^height R d * (F).coeffSize (awake C d N N p v):=by
  let b:=(A).clock.hatBeta N
  let t:=(A).clock.threshold N
  have bp:1≤b:=(A).fits.delayed N |>.le
  have tp:0<t:=(A).budget N |>.threshold_pos
  have tb:t⁻¹≤b:=by
    change ((A).budget N).threshold⁻¹ ≤ (A).clock.hatBeta N
    rw [←min_eq_left ((A).budget N).threshold_le]
    exact WilsonOriginalCoordinateExposure.threshold R N
  have eq:WilsonCoherentTerminalFrame.coordinates R N p v = (F).scaled t⁻¹ (awake C d N N p v):=by
    let T:=(C).factory d N p
    have bare:(T.entries N (T.terminal.symm v)).x=T.terminal.symm v:= (R.makes.calibrated d N p ref).bare_coord _
    change (F).scaled t⁻¹ ((((S).a N:ℂ)^d)⁻¹ • T.terminal.symm v) = (F).scaled t⁻¹ ((((S).a N:ℂ)^d)⁻¹ • (T.entries N (T.terminal.symm v)).x)
    rw [bare]
  rw [eq,Frame.coeffSize,Frame.coeffSize,mul_sum]
  apply sum_le_sum
  intro i _
  change ‖((t⁻¹^((F).grades i).2:ℝ):ℂ)*awake C d N N p v i‖≤_
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr tp.le) _)]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact (pow_le_pow_left₀ (inv_nonneg.mpr tp.le) tb _).trans (pow_le_pow_right₀ bp (le_sup (f:=fun j:(F).Index=>((F).grades j).2) (mem_univ i)))

private theorem money (j N p:ℕ) (v:(C).label d) :
    (F).coeffSize (awake C d j N p v) = (((S).a j)^d)⁻¹*(F).coeffSize (columns C d j N p v):=by
  simp only [awake,Frame.coeffSize,Pi.smul_apply,norm_smul,←Finset.mul_sum,norm_inv,norm_pow,
    Complex.norm_real,Real.norm_of_nonneg ((S).a_pos j).le]

theorem backward (k N p:ℕ) (hi:k<N) (ref:(C).ref d ≤ k) (v:(C).label d) :
    (F).coeffSize (awake C d (k+1) N p v) ≤ (((S).block k).val:ℝ)^d*((A).params (k+1)).columns*
      (F).coeffSize (awake C d k N p v):=by
  let T:=(C).factory d N p
  let L:=((S).block k).val
  have inv:=(R.makes.calibrated d N p (ref.trans hi.le)).back k ref hi (T.terminal.symm v)
  have ax:(S).a k = (L:ℝ)*(S).a (k+1):=by rw [(S).a_step,mul_div_cancel₀ _ (by exact_mod_cast ((S).block k).property.ne')]
  rw [money,money]
  calc
    _ ≤ (((S).a (k+1))^d)⁻¹*(((A).params (k+1)).columns*(F).coeffSize (columns C d k N p v)) :=
      mul_le_mul_of_nonneg_left inv (inv_nonneg.mpr (pow_nonneg ((S).a_pos _).le _))
    _ = _:=by
      rw [ax,mul_pow]
      have hn:(L:ℝ)≠0:=by exact_mod_cast ((S).block k).property.ne'
      field_simp [hn,((S).a_pos (k+1)).ne']
      ring

theorem block (slow:WilsonWindowReportingPace.Slow R.kit) (k:ℕ):
    (((S).block k).val:ℝ) ≤ (A).clock.hatBeta (k+1):=by
  let b:=(A).clock.hatBeta (k+1)
  let L:=((S).block k).val
  have hp:1≤b:=((A).fits.delayed (k+1)).le
  have lp:1≤(L:ℝ):=by exact_mod_cast ((S).block k).property
  have pos:=((A).budget (k+1)).exponent_pos
  have forecast : RG16.PlentyGate A:=slow.1
  have cap:=forecast (k+1)
  have top: ((A).budget (k+1)).supportExponent+1≥1:=by linarith
  have cost:(((A).budget (k+1)).supportExponent+1)*((L:ℝ)^4) ≤ Real.sqrt b:=by
    change (((A).budget (k+1)).supportExponent+1)*(((S).block k).val:ℝ)^4 ≤ Real.sqrt ((A).clock.hatBeta (k+1))
    exact cap
  have roots:Real.sqrt b ≤ b:=by nlinarith [Real.sq_sqrt (zero_le_one.trans hp),Real.one_le_sqrt.mpr hp]
  calc
    _ ≤ (L:ℝ)^4 :=by simpa only [pow_one] using pow_le_pow_right₀ lp (by decide:1≤4)
    _ ≤ (((A).budget (k+1)).supportExponent+1)*((L:ℝ)^4):=le_mul_of_one_le_left (pow_nonneg (zero_le_one.trans lp) _) top
    _ ≤ Real.sqrt b:=cost
    _ ≤ b:=roots

theorem entry (simple:G.Simple) {δ:ℝ} {T:Campaign R} {W:Campaign.Pillars R T}
    (fund:FundedOriginalProperties.{u} simple δ W) (slow:WilsonWindowReportingPace.Slow R.kit) :
    ∃ c:ℝ,1≤c ∧ ∀ (k:ℕ),(C).ref d≤k → ∀(p:ℕ) (v:(C).label d) (o:Site ((C).side (k+1) p)) (U:Config G ((C).side (k+1) p)),
      ‖(C).O (k+1) p v o U‖ ≤ c*((A).clock.hatBeta (k+1))^(height R d+d+1)*(F).coeffSize (awake C d k (k+1) p v):=by
  obtain ⟨c,hc,give⟩:=group R d
  refine ⟨c,hc,?_⟩
  intro k ref p v o U
  let b:=(A).clock.hatBeta (k+1)
  let fine:=(F).coeffSize (awake C d (k+1) (k+1) p v)
  let seen:=(F).coeffSize (awake C d k (k+1) p v)
  have h0:0≤b:=((A).fits.delayed (k+1)).le.trans' zero_le_one
  have ss : 0 ≤ seen:=sum_nonneg fun _ _=>norm_nonneg _
  have order: (F).coeffSize (WilsonCoherentTerminalFrame.coordinates R (k+1) p v) ≤ b^height R d*fine:=
    scale R d (k+1) p (ref.trans k.le_succ) v
  have back:fine ≤ b^d*b*seen:=by
    exact (backward R d k (k+1) p k.lt_succ_self ref v).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) (block R slow k) _)
       (fund.2.1.logBudget.money.present (k+1)) (zero_le_one.trans ((A).params (k+1)).columns_ge) (pow_nonneg h0 _)) ss)
  calc
    _ ≤ c*(F).coeffSize (WilsonCoherentTerminalFrame.coordinates R (k+1) p v) :=give (k+1) p v o U
    _ ≤ c*(b^height R d*(b^d*b*seen)):= mul_le_mul_of_nonneg_left
      (order.trans (mul_le_mul_of_nonneg_left back (pow_nonneg h0 _))) (zero_le_one.trans hc)
    _ = _:=by rw [pow_succ,pow_add]; ring

end YM.Integration.WilsonOriginalAdjacentMicroscopicPrice
