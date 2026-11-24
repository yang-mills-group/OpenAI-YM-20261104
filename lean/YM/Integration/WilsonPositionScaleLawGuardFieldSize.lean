import YM.Integration.WilsonPositionScaleLawGuardGradeClock

/-! Uniform two-radius growth of each genuine field, in powers of its own positive kinetic coupling. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardFieldSize
open Function Filter Set Spec Table Extraction Climb PhysMS Trace.Pilot Maxwell Maxwell.Free XSpace XSpace.Normalize
open OPE OPE.Orbits PhysicalNext.Repeat.Legato MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionScaleLawHome (Ratio sweep)
open WilsonPositionScaleLawWholeHome (physical)
open WilsonPositionScaleLawKinetic (kinetic)
open WilsonPositionScaleLawGuardGradeClock (age)
open scoped Topology Classical Asymptotics

theorem shift (r:ℝ)(hr:0<r)(t:Ratio):age (t.val*r)≤age r+1:=by
  have ht:=WilsonPositionScaleLawNative.positive t
  have hlog:0<Real.log 2:=Real.log_pos (by norm_num)
  have short:-Real.log 2≤Real.log t.val:=calc
    _=Real.log (1/2:ℝ):=by rw [one_div,Real.log_inv]
    _≤_:=Real.log_le_log (by norm_num : 0<(1/2:ℝ)) t.property.1
  unfold age
  simp only [one_div,Real.log_inv,Real.log_mul ht.ne' hr.ne']
  have bill:-(Real.log t.val+Real.log r)/Real.log 2≤(-Real.log r)/Real.log 2+1:=by
    apply (div_le_iff₀ hlog).mpr
    rw [add_mul,div_mul_cancel₀ _ hlog.ne',one_mul];linarith
  linarith

theorem agePos {r:ℝ}(hr:0<r)(short:r≤1):0≤age r:=by
  have nr:1≤1/r:=(le_div_iff₀ hr).mpr (by simpa only [one_mul] using short)
  exact add_nonneg zero_le_one (div_nonneg (Real.log_nonneg nr) (Real.log_pos (by norm_num : 1<(2:ℝ))).le)

variable {G:Gauge}(Z:WilsonPrescription G){hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
    {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)
set_option quotPrecheck false
local notation "gθ"=>kinetic Z F J
include H in
theorem original (d:ℕ)(funded:Coupling G (kinetic Z F J))(law:WilsonPositionScaleLawGuardLittle.scale F J Z M ν d 2):
    ∃p:ℕ,∀O:S.Field d,∃C:ℝ,0≤C ∧ ∀ᶠr in trail,∀t:Ratio,‖physical F J Z d (t.val*r) O‖*|gθ r|^(2*p)≤C:=by
  obtain ⟨p,ρ,hρ,entries⟩:=WilsonPositionScaleLawGuardLog.original Z M H ν F J d funded law 1 one_pos
  let c:=G.slopeConstant⁻¹/Real.log 2
  let K:=|c|+1
  have hK:0≤K:=by dsimp only [K];positivity
  have prices:∀ᶠr in trail,age r*gθ r^2<K:=(tendsto_order.mp (WilsonPositionScaleLawGuardGradeClock.rate hG funded)).2 _ (lt_of_le_of_lt (le_abs_self c) (lt_add_one _))
  have vanishes:Tendsto (fun r=>gθ r^2) trail (𝓝 0):=by simpa only [zero_pow (by decide :2≠0)] using (funded.conforms hG).pow 2
  have near:∀ᶠr in trail,r∈Ioc 0 (min ρ 1):=mem_nhdsGT_iff_exists_Ioc_subset.mpr ⟨_,lt_min hρ one_pos,Subset.rfl⟩
  refine ⟨p,?_⟩;intro O;obtain ⟨B,hB,field⟩:=entries O
  refine ⟨B*(K+1)^p,mul_nonneg hB (pow_nonneg (by linarith) _),?_⟩
  filter_upwards [near,prices,(tendsto_order.mp vanishes).2 1 one_pos] with r small fee cap t
  have pos:=mul_pos (WilsonPositionScaleLawNative.positive t) small.1
  have home:t.val*r≤r:=mul_le_of_le_one_left small.1.le t.property.2
  have used:=field (t.val*r) pos (home.trans (small.2.trans (min_le_left _ _)))
  have entry:‖physical F J Z d (t.val*r) O‖≤B*age (t.val*r)^p:=(WilsonPositionScaleLawGuardOrbit.total R.family _).trans used
  have more:=mul_le_mul_of_nonneg_right (shift r small.1 t) (sq_nonneg (gθ r))
  have short:age (t.val*r)*gθ r^2≤K+1:=by linarith only [more,fee,cap]
  have paid:=pow_le_pow_left₀ (mul_nonneg (agePos pos (home.trans (small.2.trans (min_le_right _ _)))) (sq_nonneg _)) short p
  calc
    _≤(B*age (t.val*r)^p)*|gθ r|^(2*p):=mul_le_mul_of_nonneg_right entry (pow_nonneg (abs_nonneg _) _)
    _=B*(age (t.val*r)*gθ r^2)^p:=by rw [mul_pow,pow_mul,sq_abs];ring
    _≤_:=mul_le_mul_of_nonneg_left paid hB

end YM.Integration.WilsonPositionScaleLawGuardFieldSize
