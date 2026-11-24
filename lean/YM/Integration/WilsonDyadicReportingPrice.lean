import YM.Integration.WilsonReportingLength
import YM.Integration.WilsonPhysicalExteriorFrame
import YM.RG16.GaugeCredit.Lambda

/-! The change between the physical measuring length and its lattice spacing
costs a power of the logarithmic unit, uniformly before both regulators. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonDyadicReportingPrice
open Filter Function Set Lattice Wilson RG OPE PhysMS PhysMS.Frame Spec
open RG16 RG16.Literal RG16.Guarding Pert.Asymptotics
open scoped Topology Classical
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}

/-- A fixed logarithmic loss can always be paid with one further power of
the genuine coupling, before either cutoff is observed. -/
theorem reserve (gauge : G.Simple) (H : C.Makes) (K A ε : ℝ)
    (hK : 0 ≤ K) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ p N, m ≤ N →
      K*(Lambda C.path.levels m)^A*regulatorRun C N p m ≤ ε := by
  have hv := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero A (1/2:ℝ)
    (by norm_num)).comp (lambda_leads C gauge)).const_mul (K*(2*Real.exp 1))
  rw [mul_zero] at hv
  filter_upwards [hv.eventually (gt_mem_nhds hε)] with m hm p N hn
  have positive_unit := lambda_pos C m
  calc
    _ ≤ K*(Lambda C.path.levels m)^A*(2*Real.exp 1*coin C 1 m) :=
      mul_le_mul_of_nonneg_left (g_band C H hn).2 (mul_nonneg hK (Real.rpow_nonneg positive_unit.le _))
    _ = (K*(2*Real.exp 1))*((Lambda C.path.levels m)^A*
        Real.exp (-(1/2:ℝ)*(Lambda C.path.levels m))) := by unfold coin; ring_nf
    _ ≤ ε := hm.le

def steps (C : Family G) (B : ℝ) (m : ℕ) : ℕ :=
  ⌈B*Real.log (Lambda C.path.levels m)/Real.log 2⌉₊

theorem steps_interval (B : ℝ) (hB : 0 ≤ B) (m : ℕ) :
    B*Real.log (Lambda C.path.levels m)/Real.log 2 ≤ (steps C B m : ℝ) ∧
      (steps C B m : ℝ) < B*Real.log (Lambda C.path.levels m)/Real.log 2+1 := by
  have hl := Real.log_nonneg (one_le_two.trans (lambda_up C m).le)
  exact ⟨Nat.le_ceil _,Nat.ceil_lt_add_one (div_nonneg (mul_nonneg hB hl) (Real.log_nonneg one_le_two))⟩

/-- Transfer any signed measured-minus-prescribed field to the finer
normalization with the same two fields, mesh, cutoff, period, and coupling. -/
theorem measured (F : Final C f S) (gauge : G.Simple) (h : ℕ)
    (J : ℝ → tower S) (leading : Leading F J) (B : ℝ) (hB : 0 ≤ B)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ p N, m ≤ N → ∀ X Y : S.Field h,
      ‖(J (WilsonReportingLength.radius C B m) h).symm (X-Y)‖ ≤
        (regulatorRun C N p m)^(k+1) →
      ‖(J (C.S.a m) h).symm (X-Y)‖ ≤ ε*(regulatorRun C N p m)^k := by
  obtain ⟨K,hK,hf⟩ := WilsonPhysicalExteriorFrame.between F h J leading 1 one_pos
  have hh := reserve gauge F.room.cutoff K (B*((h:ℝ)+1)) ε (zero_le_one.trans hK) hε
  filter_upwards [(WilsonReportingLength.fine C B).eventually hf,hh] with m frame pay p N hm X Y cost
  let u := Lambda C.path.levels m
  have hu : 0 < u := lambda_pos C m
  have h1 : (1:ℝ) ≤ u := one_le_two.trans (lambda_up C m).le
  have hs : (u^(-B))∈Ioc (0:ℝ) 1 :=
    ⟨Real.rpow_pos_of_pos hu _,Real.rpow_le_one_of_one_le_of_nonpos h1 (neg_nonpos.mpr hB)⟩
  have ht : (u^(-B))*WilsonReportingLength.radius C B m = C.S.a m := by
    change (u^(-B))*(C.S.a m*u^B) = _
    rw [Real.rpow_neg hu.le, mul_comm (C.S.a m), ← mul_assoc,
      inv_mul_cancel₀ (Real.rpow_pos_of_pos hu B).ne',one_mul]
  have pow : (u^(-B))^(-(h:ℝ)-1) = u^(B*((h:ℝ)+1)) := by
    rw [← Real.rpow_mul hu.le]; congr 1; ring
  have result := frame (u^(-B)) hs (X-Y)
  rw [ht,pow] at result
  have hg := g_pos F.room.cutoff (p:=p) hm
  calc
    _ ≤ K*u^(B*((h:ℝ)+1))*(regulatorRun C N p m)^(k+1) :=
      result.trans (mul_le_mul_of_nonneg_left cost (mul_nonneg (zero_le_one.trans hK)
        (Real.rpow_nonneg hu.le _)))
    _ = (K*u^(B*((h:ℝ)+1))*regulatorRun C N p m)*(regulatorRun C N p m)^k := by rw [pow_succ]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (pay p N hm) (pow_nonneg hg.le _)

end YM.Integration.WilsonDyadicReportingPrice

