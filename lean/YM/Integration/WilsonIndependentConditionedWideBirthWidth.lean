import YM.Integration.WilsonIndependentConditionedEarlierReflection
import YM.Integration.WilsonIndependentConditionedStoppedCalendar
import YM.OPE.Therm.Request

/-! Uniform smallness of the wider housing radius with the original field books kept at r. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedWideBirthWidth
open Filter Set Wilson Lattice RG PhysicalNext.Repeat.Legato
open scoped Topology
variable {G:Gauge}(R:Run G)
local notation "a" => R.family.S.a
local notation "H" => R.family.path.levels.clock.hatBeta
local notation "ν" => R.family.path.levels.clock.monitor
local notation "trail" => nhdsWithin (0:ℝ) (Set.Ioi 0)

theorem late (simple:G.Simple)(W L:ℕ):∀ᶠf:ℕ in atTop,
    ∀j≤f,∀{r lam:ℝ},0≤r → r≤(H f)^W*a f → lam≤r*(ν j)^L → lam≤(H f)^(W+2)*a f:=by
  obtain ⟨B,_,cost⟩:=WilsonIndependentConditionedEarlierReflection.monitor R simple L (by norm_num : (0:ℝ)<1)
  filter_upwards [(Next.Rank.Station.hat_rate R.family.path.levels simple).eventually_ge_atTop B] with f rich
  intro j jf r lam rp posted wide
  have heat:0≤H f:=(zero_lt_one.trans (R.family.path.levels.fits.delayed f)).le
  have zoom:(ν j)^L≤(H f)^2:=by
    calc _ ≤ B*(H f) := by simpa only [Real.rpow_one] using cost jf
         _ ≤ (H f)^2:=by simpa only [pow_two] using mul_le_mul_of_nonneg_right rich heat
  calc _≤r*((H f)^2):=wide.trans (mul_le_mul_of_nonneg_left zoom rp)
       _≤((H f)^W*a f)*((H f)^2):=mul_le_mul_of_nonneg_right posted (sq_nonneg _)
       _=(H f)^(W+2)*a f:=by rw [pow_add];ring

theorem original (simple:G.Simple)(W L:ℕ){P:ℝ→Prop}(p:∀ᶠlam in trail,P lam):
    ∀ᶠr in trail,∀f j:ℕ,a f≤r → r≤(H f)^W*a f → j≤f →
      ∀lam:ℝ,r≤lam → lam≤r*(ν j)^L → lam≤(H f)^(W+2)*a f ∧ P lam:=by
  obtain ⟨e,ep,inside⟩:=mem_nhdsGT_iff_exists_Ioc_subset.mp p
  have vanish:=OPE.Therm.ember_mul (K:=R.family.path.levels) simple (W+2)
  obtain ⟨k,income⟩:=eventually_atTop.mp ((late R simple W L).and (vanish.eventually_lt_const ep))
  filter_upwards [Ioc_mem_nhdsGT (R.family.S.a_pos k)] with r small
  intro f j near posted jf lam low wide
  have kf:k≤f:=le_of_not_gt fun bad=>(R.family.S.strictAnti bad).not_ge (near.trans small.2)
  have bought:lam≤(H f)^(W+2)*a f:=(income f kf).1 j jf small.1.le posted wide
  have lim:lam≤e:=bought.trans (by simpa only [mul_comm] using (income f kf).2.le)
  exact ⟨bought,inside (show lam∈Ioc (0:ℝ) e from ⟨small.1.trans_le low,lim⟩)⟩

end YM.Integration.WilsonIndependentConditionedWideBirthWidth
