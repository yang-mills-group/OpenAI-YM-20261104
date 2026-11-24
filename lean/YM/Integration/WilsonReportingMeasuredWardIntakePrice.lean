import YM.Integration.WilsonReportingMeasuredWardIntake
import YM.Integration.WilsonReportingMeasuredWardFeePrice

/-! Uniform original price of the entire represented historical Ward source. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingMeasuredWardIntakePrice
open Filter Function Finset Lattice Wilson RG Source Labels MS.Local.Physical MS.Theater MS.Land
open PhysicalNext.Repeat.Legato Trace.Physical Trace.Physical.GermGraph
open WilsonReportingPrescribedOldFreeArms WilsonReportingPrescribedOldWardWallet
open WilsonReportingPrescribedOldWardTree WilsonReportingMeasuredWardFees
open WilsonReportingMeasuredWardSource WilsonReportingMeasuredWardSourceGerm WilsonReportingMeasuredWardIntake
open WilsonMatrixTicketLanesNativePrices
open scoped BigOperators Classical

variable {G:Gauge} {B:Deck G} (R:Run G) (Q:Prescription B)
local notation "F" => R.family.labels.level 4
local notation "I" => B.BIndex (4:ℤ) 2

private theorem fields (K:ℕ) (μ:ℝ):
    ∃C:ℝ,0<C ∧ ∃d:ℕ,∀t k,k ≤ K→∀ (z:Stock B) (n:Side) (o:Site n) (U:Config G n),
      ‖operand R Q z (μ-t) k n o U‖≤C*(1+‖t‖)^d*amount B z:=by
  obtain ⟨c,cp,e,cap⟩:=WilsonSeparatedOriginalSlabQArms.fixed R Q
    (WilsonReportingPrescribedOldAction.label B) K μ
  let C:=max 1 c
  have one:1≤C:=le_max_left ..
  refine ⟨C,zero_lt_one.trans_le one,e,?_⟩
  intro t k hk z n o U
  let A:=C*(1+‖t‖)^e
  have ap:1≤A:=one_le_mul_of_one_le_of_one_le one (one_le_pow₀ (by linarith [norm_nonneg t]))
  have hp:‖if k=0 then z.1 else 0‖≤A*‖z.1‖:=by
    calc _ ≤ ‖z.1‖:=by split <;> simp
         _ ≤ _:=le_mul_of_one_le_left (norm_nonneg _) ap
  unfold operand
  refine (norm_add_le ..).trans ?_
  change _≤A*(‖z.1‖+∑i,‖z.2 i‖)
  rw [mul_add,mul_sum]
  refine add_le_add hp ((norm_sum_le ..).trans (sum_le_sum fun i _=>?_))
  rw [norm_mul,mul_comm A]
  exact mul_le_mul_of_nonneg_left ((cap i k hk t n o U).trans
    (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity))) (norm_nonneg _)

private theorem geometry (z:Stock B) :
    let D:=∑i:I,‖(((ActualOriginalDictionary.dictionary R B).cylinder 4 2 i).O 1 0 1:ℂ)‖
    let E:=∑i:I,(F).coeffSize ((warehouse R).fits B 4 2 i)
    ‖stencil R z 1 0 1‖≤D*(∑i,‖z.2 i‖) ∧ (F).coeffSize (coordinates R z)≤E*(∑i,‖z.2 i‖):=by
  intro D E
  have coef:(F).coeffSize (coordinates R z)≤∑i:I,‖z.2 i‖*(F).coeffSize ((warehouse R).fits B 4 2 i):=by
    exact (Extra.Histories.Size.finite F univ (fun i:I=>z.2 i • (warehouse R).fits B 4 2 i)).trans_eq
      (sum_congr rfl fun i _=>Extra.Histories.Size.smul F (z.2 i) ((warehouse R).fits B 4 2 i))
  constructor
  · unfold stencil
    rw [mul_sum]
    exact (norm_sum_le ..).trans (sum_le_sum fun i _=>by
      rw [norm_mul,mul_comm D]
      exact mul_le_mul_of_nonneg_left (single_le_sum (f:=fun j:I=>‖(((ActualOriginalDictionary.dictionary R B).cylinder 4 2 j).O 1 0 1:ℂ)‖) (fun j _=>norm_nonneg _) (mem_univ i)) (norm_nonneg _))
  · rw [mul_sum]
    exact coef.trans (sum_le_sum fun i _=>by
      rw [mul_comm E]
      exact mul_le_mul_of_nonneg_left (single_le_sum (fun j _=>Work.G08.size_nonneg F _) (mem_univ i)) (norm_nonneg _))

theorem before (K:ℕ) (μ:ℝ):
    ∃C:ℝ,0<C ∧ ∃e:ℕ,∀m (t:ℝ) k,k ≤ K→∀z:Stock B,
      (F).coeffSize (bank R Q m z (μ-t) k)≤C*(1+‖t‖)^e*amount B z := by
  obtain ⟨c,cp,d,whole⟩:=fields R Q K μ
  obtain ⟨u,up,b,fees⟩:=WilsonReportingMeasuredWardFeePrice.before Q K μ
  let D:=∑i:I,‖(((ActualOriginalDictionary.dictionary R B).cylinder 4 2 i).O 1 0 1:ℂ)‖
  let E:=∑i:I,(F).coeffSize ((warehouse R).fits B 4 2 i)
  let I₀:=(F).coeffSize (F).e0
  have dp:0≤D:=sum_nonneg fun _ _=>norm_nonneg _
  have ep:0≤E:=sum_nonneg fun _ _=>Work.G08.size_nonneg F _
  have ip:0≤I₀:=Work.G08.size_nonneg F _
  refine ⟨1+(c+D*u)*I₀+E*u,by positivity,max d b,?_⟩
  intro m t k hk z
  let y:=projected Q (μ-t) k z
  let A:=(1+‖t‖)^(max d b)*amount B z
  have vp:0≤amount B z:=add_nonneg (norm_nonneg _) (sum_nonneg fun _ _=>norm_nonneg _)
  have ap:0≤A:=mul_nonneg (by positivity) vp
  have base:1≤1+‖t‖:=by linarith [norm_nonneg t]
  have cap:‖operand R Q z (μ-t) k 1 0 1‖≤c*A:=(whole t k hk z 1 0 1).trans (by
    dsimp only [A];rw [←mul_assoc];gcongr;exact le_max_left ..)
  have sump:(∑i,‖y.2 i‖)≤u*A:=(fees t k hk z).trans (by
    dsimp only [A];rw [←mul_assoc];apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ base (le_max_right ..)) up.le
    · exact le_add_of_nonneg_left (norm_nonneg _)
    · exact sum_nonneg fun _ _=>norm_nonneg _
    · positivity)
  have ⟨st,co⟩:=geometry R y
  have basis:‖scalar R Q z (μ-t) k‖≤(c+D*u)*A:=by
    unfold scalar
    exact (norm_sub_le ..).trans ((add_le_add cap (st.trans (mul_le_mul_of_nonneg_left sump dp))).trans_eq (by ring))
  let θ:=R.family.path.levels.clock.threshold m
  have θp:0≤θ:=(R.family.path.levels.budget m).threshold_pos.le
  have θu:θ≤1:=(R.family.path.levels.budget m).threshold_le
  have θsq:‖((θ^2:ℝ):ℂ)‖ ≤ 1:=by
    rw [Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
    simpa using pow_le_pow_left₀ θp θu 2
  calc
    _ ≤ ‖scalar R Q z (μ-t) k‖*I₀+‖((θ^2:ℝ):ℂ)‖*(F).coeffSize (coordinates R y):=by
      simpa only [bank,y,I₀,θ,Extra.Histories.Size.smul] using Extra.Histories.Size.add F
        (scalar R Q z (μ-t) k • (F).e0) (((θ^2:ℝ):ℂ) • coordinates R y)
    _ ≤ ((c+D*u)*A)*I₀+1*(E*(u*A)):=add_le_add (mul_le_mul_of_nonneg_right basis ip)
      (mul_le_mul θsq (co.trans (mul_le_mul_of_nonneg_left sump ep)) (Work.G08.size_nonneg F _) zero_le_one)
    _ ≤ (1+(c+D*u)*I₀+E*u)*A:=by nlinarith only [ap]
    _ = _:=by dsimp only [A];ring

end YM.Integration.WilsonReportingMeasuredWardIntakePrice
