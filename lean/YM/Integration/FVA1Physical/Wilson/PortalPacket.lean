import YM.Integration.FVA1Physical.Wilson.RoughExterior
import YM.Integration.FVA1Physical.Wilson.OrbitCollar
import YM.Integration.FVA1Physical.Wilson.FieldRowSchedule
import YM.Integration.FVA1Physical.Wilson.UncutHotel

/-! Rooted incoming Wilson packets may be read on the full physical Haar draw.
On its actual portal, replacing the arbitrary exterior by the analytic chamber
costs every inverse power, with onset before the torus, bank, forest and draw. -/
set_option autoImplicit false
set_option maxHeartbeats 950000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Set Finset MeasureTheory Lattice RG YM.Wilson Tree Precision Exterior
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock
open MSbar.Bout MSbar.Duel MSbar.Lis MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Rolling MSbar.CrossH
open MSbar.Bakery.Portal Push.Uniform MSbar.Midpoint MSbar.Bakery.Film MSbar.Bakery MSbar.Measuring MSbar.Jade
open scoped Classical Topology BigOperators
variable {G:Gauge}

theorem rendered_packet_collar (m s p:ℕ) (h u:ℝ) :
    ∀ᶠ y:ℝ in atTop,∀ {c f:Side} (S:StepData c f) (F:Forest S.ratio) (V:Voice G) (_cle:Clear G V)
      (b:Site f) (O:Config G c) (μ:Positions (Key F G)) {lo hi g:ℝ},lo ≤ hi → lensT y g → |g| ≤ 1 →
      ∀ T:Nesting G f,BankPaid b y s p m h T → ∀ N∈hotel F (boxX y b) (boxY y b) V O μ lo hi,
       |taste p (picture (chartLog g (canoe (S:=S) F N)) T) g -
        taste p (picture (chartLog g (chambers F (boxY y b) V O μ N)) T) g| ≤ y^u := by
  filter_upwards [rough_configuration_collar G m s h (1-u),eventually_ge_atTop ((p+1:ℕ):ℝ)] with y pay enough
  intro c f S F V cle b O μ lo hi g pad clock cap T bank N live
  let X:=boxX y b;let Y:=boxY y b
  let W:=canoe (S:=S) F N;let W':=chambers F Y V O μ N
  have enough':(p+1:ℕ) ≤ y:=enough
  have y0:0<y:=lt_of_lt_of_le (by exact_mod_cast Nat.zero_lt_succ p) enough'
  have same(e:Edge (Site f))(he:e.1∈X) : W e=W' e:=by
    have xy:X⊆Y:=halo_subset ..
    apply cognizant F X Y V O μ cle xy live pad e (xy he)
    apply (halo_spec ..).mpr
    exact ⟨e.1,he,(Work.E01.sep_step_le e.1 e.2).trans (by omega)⟩
  unfold taste
  simp only [picture,PowerSeries.coeff_map]
  rw [←sum_sub_distrib]
  refine (abs_sum_le_sum_abs ..).trans ?_
  calc _ ≤ ∑ _∈range (p+1), y^(-(1-u)) := by
         apply sum_le_sum;intro i hi
         have hi':i≤p:=Nat.le_of_lt_succ (mem_range.mp hi)
         rw [←mul_sub,abs_mul,abs_pow]
         exact (mul_le_mul_of_nonneg_right (pow_le_one₀ (abs_nonneg _) cap) (abs_nonneg _)).trans
           ((one_mul _).le.trans ((abs_sub_comm _ _).le.trans (pay f b g clock _ (bank i hi').1 (bank i hi').2 W W' same)))
       _ = (p+1:ℕ)*y^(-(1-u)) := by simp
       _ ≤ y*y^(-(1-u)) := mul_le_mul_of_nonneg_right enough' (Real.rpow_nonneg y0.le _)
       _ = y^u := by nth_rw 1 [←Real.rpow_one y];rw [←Real.rpow_add y0];congr 1;ring

end YM.Integration.FVA1Physical.Wilson
