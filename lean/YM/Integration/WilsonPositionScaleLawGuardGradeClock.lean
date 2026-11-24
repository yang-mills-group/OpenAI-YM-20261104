import YM.Integration.WilsonPositionScaleLawGuardAnnulus

/-! The measured kinetic coefficient converts every original lower-grade logarithmic bound into the corresponding full coupling order. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardGradeClock
open Function Filter Set Spec Table Extraction Climb PhysMS Trace.Pilot Maxwell Maxwell.Free XSpace XSpace.Normalize
open OPE OPE.Orbits PhysicalNext.Repeat.Legato MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionScaleLawWholeHome (physical)
open WilsonPositionScaleLawKinetic (kinetic)
open WilsonPositionScaleLawGrade (grade)
open scoped Topology Classical Asymptotics

def age (u:ℝ):ℝ:=1+Real.log (1/u)/Real.log 2
variable {G:Gauge}{g:ℝ→ℝ}

theorem rate (simple:G.Simple)(funded:Coupling G g):
    Tendsto (fun u=>age u*g u^2) trail (𝓝 (G.slopeConstant⁻¹/Real.log 2)):=by
  have zero:Tendsto (fun u=>g u^2) trail (𝓝 0):=by simpa only [zero_pow (by decide : 2≠0)] using (funded.conforms simple).pow 2
  have limit:=zero.add (funded.running.div_const (Real.log 2))
  rw [zero_add] at limit
  apply limit.congr
  intro u
  unfold age LogV
  rw [one_div]
  ring

theorem clock (simple:G.Simple)(funded:Coupling G g):∃a:ℝ,0<a ∧ ∀ᶠu in trail,a≤age u*g u^2:=by
  let b:=G.slopeConstant⁻¹/Real.log 2
  have pos:0<b:=div_pos (inv_pos.mpr (Gauge.slopeConstant_pos simple)) (Real.log_pos (by norm_num))
  exact ⟨b/2,half_pos pos,((tendsto_order.mp (rate simple funded)).1 _ (half_lt_self pos)).mono fun _ h=>h.le⟩

theorem price {a B w z x:ℝ}(m:ℕ)(pos:0<a)(low:a≤w*z^2)(value:0≤x)(cost:w^m*x≤B):x≤(B/a^m)*|z|^(2*m):=by
  have pm:=pow_pos pos m
  have earned:a^m*x≤B*|z|^(2*m):=calc
    _≤(w*z^2)^m*x:=mul_le_mul_of_nonneg_right (pow_le_pow_left₀ pos.le low m) value
    _=(w^m*x)*|z|^(2*m):=by rw [mul_pow,pow_mul,sq_abs];ring
    _≤_:=mul_le_mul_of_nonneg_right cost (pow_nonneg (abs_nonneg _) _)
  apply (mul_le_mul_iff_right₀ pm).mp
  calc
    _≤_:=earned
    _=a^m*((B/a^m)*|z|^(2*m)):=by field_simp

variable (Z:WilsonPrescription G){hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
    {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)
set_option quotPrecheck false
local notation "gθ"=>kinetic Z F J
variable (d:ℕ)(funded:Coupling G (kinetic Z F J))(law:∀q,WilsonPositionScaleLawGuardLittle.scale F J Z M ν d q)
include H funded law in
theorem original (i:Fin (d+1))(lower:i.val<d)(m:ℕ):∃ρ:ℝ,0<ρ ∧ ∀O:S.Field d,∃C:ℝ,0≤C ∧ ∀u:ℝ,0<u→u≤ρ→
    ‖grade R.family i (physical F J Z d u O)‖≤C*|gθ u|^(2*m):=by
  obtain ⟨s,hs,fields⟩:=WilsonPositionScaleLawGuardAnnulus.original Z M H ν F J d funded law 1 one_pos i lower m
  obtain ⟨a,ha,paid⟩:=clock hG funded
  obtain ⟨t,ht,bill⟩:=mem_nhdsGT_iff_exists_Ioc_subset.mp paid
  refine ⟨min s t,lt_min hs ht,?_⟩;intro O
  obtain ⟨B,hB,input⟩:=fields O
  refine ⟨B/a^m,div_nonneg hB (pow_pos ha m).le,?_⟩;intro u hu small
  exact price m ha (bill ⟨hu,small.trans (min_le_right _ _)⟩) (norm_nonneg _) (input u hu (small.trans (min_le_left _ _)))

end YM.Integration.WilsonPositionScaleLawGuardGradeClock
