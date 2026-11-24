import YM.Integration.WilsonLocalKernelMoments
import YM.Integration.WilsonLocalHolonomy
import YM.Integration.ActualNumericCouplingSmallness

/-! Local Wilson estimates on the measured temperatures of an original funded run. -/
noncomputable section
namespace YM.Integration.WilsonPhysicalKernelClock
open YM RG Lattice Wilson Filter PhysicalNext.Repeat.Legato Pert.Asymptotics
open FullQLocal.RenderedStep MatchingLedger.Compass.Income PertExtension.Series
open scoped BigOperators Topology
variable {G : Gauge}

theorem transport (R : Run G) (hG : G.Simple) {P : ℝ → Prop}
    (h : ∀ᶠ t in Tested.germ, P t) :
    ∀ᶠ m : ℕ in atTop, ∀ N p : ℕ, m < N → P (regulatorRun R.family N p (m+1)) := by
  obtain ⟨d,hd,hP⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp h
  let e := d/2
  have he : 0 < e := half_pos hd
  let D := R.family.path.levels
  have ht := (WardBin.bell D hG).comp (tendsto_add_atTop_nat 1)
  filter_upwards [ht.eventually_ge_atTop ((2/e)^2)] with m hm N p hN
  have hb := WardBin.hot D (m+1)
  have hs : 2/e ≤ Real.sqrt (D.clock.hatBeta (m+1)) :=
    (Real.le_sqrt (div_nonneg (by norm_num) he.le) hb.le).2 hm
  have hsmall : regulatorRun R.family N p (m+1) ≤ e := by
    calc
      _ ≤ 2*(Real.sqrt (D.clock.hatBeta (m+1)))⁻¹ :=
        (Weather.into_band R.family R.makes (Nat.succ_le_of_lt hN) p).2
      _ = 2 / Real.sqrt (D.clock.hatBeta (m+1)) := (div_eq_mul_inv _ _).symm
      _ ≤ e := (div_le_iff₀ (Real.sqrt_pos.mpr hb)).2
        (by nlinarith only [(div_le_iff₀ he).mp hs])
  exact hP ⟨Weather.runs_pos R.family R.makes (Nat.succ_le_of_lt hN) p,
    hsmall.trans_lt (half_lt_self hd)⟩

theorem temperature (R : Run G) (N p i : ℕ) (hi : i ≤ N) :
    ((regulatorRun R.family N p i)^2)⁻¹ = R.family.path.β N p i := by
  have hb : 0 < R.family.path.β N p i :=
    (div_pos (zero_lt_one.trans (R.family.path.levels.fits.delayed i)) (by norm_num)).trans_le
      (R.makes.wilson.represents N p i hi).band.1
  change (((Real.sqrt (R.family.path.β N p i))⁻¹)^2)⁻¹ = _
  rw [inv_pow,inv_inv,Real.sq_sqrt hb.le]

theorem moments (R : Run G) (hG : G.Simple) (k : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ m : ℕ in atTop, ∀ N p : ℕ, m < N → ∀ n : ℕ,
      ∀ A : Finset (Edge (Site (R.family.side m p))), A.card = k →
      ∀ U : Config G (R.family.side (m+1) p),
      WilsonLocalKernelMoments.joint (R.family.path.levels.clock.op m p) A
        (R.family.path.β N p (m+1)) n U ≤ (n.factorial:ℝ) *
          ((4/3:ℝ)*(regulatorRun R.family N p (m+1))^2)^n*M := by
  obtain ⟨M,hM,H⟩ := WilsonLocalKernelMoments.calendar R.family.path.levels.clock k
  refine ⟨M,hM,?_⟩
  filter_upwards [transport R hG H] with m hm N p hN n A hA U
  have hv := hm N p hN n m p (R.family.path.levels.blocks m p).branches A hA U
  rwa [temperature R N p (m+1) (Nat.succ_le_of_lt hN)] at hv

theorem holonomy (R : Run G) (hG : G.Simple) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ᶠ m : ℕ in atTop, ∀ N p : ℕ, m < N →
      ∀ (x : Site (R.family.side m p)) (q : PlaqAxes) (U : Config G (R.family.side (m+1) p)),
      let g := regulatorRun R.family N p (m+1)
      WilsonLocalHolonomy.measured (R.family.path.levels.clock.op m p) x q
        (R.family.path.β N p (m+1)) (g^2*(Real.log g)^2) U ≤ C*g^n := by
  obtain ⟨C,hC,H⟩ := WilsonLocalHolonomy.logarithmic R.family.path.levels.clock
  refine ⟨C,hC,fun n => ?_⟩
  filter_upwards [transport R hG (H n)] with m hm N p hN x q U
  have hv := hm N p hN m p (R.family.path.levels.blocks m p).branches x q U
  rwa [temperature R N p (m+1) (Nat.succ_le_of_lt hN)] at hv

end YM.Integration.WilsonPhysicalKernelClock
