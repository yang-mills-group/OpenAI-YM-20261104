import YM.Integration.WilsonTrueProjectedPointGrowth
import YM.Integration.WilsonNeutralPointWeakIncome

/-! At every date in the original interval, the independently prescribed
incoming coefficient has its own receiving power of the measured coupling.
The price is uniform before the upper cutoff, period and child choices. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedPointStock
open Function Filter Finset Matrix PowerSeries Lattice Wilson RG Labels Source Trace.Physical
open FormalBulk08 City Pose PhysicalNext Repeat Legato
open WilsonTrueProjectedPointInverse WilsonTrueProjectedPointSalary WilsonPinnedWidthTransport
open WilsonTrueProjectedPointProgram WilsonPointChildWidthPortfolio WilsonPointChildFiledSalary
open scoped Classical BigOperators PowerSeries
variable {G : Gauge} (R : Run G) {d D : ℕ}
local notation "F" => R.family.labels.level d
local notation "ι" => Letter (R.family.labels.level d)
local notation "Λ" => RG16.Lambda R.family.path.levels
variable (wood : Primer.Families R.family) (a : hue G) (depth : d < D)

private theorem entry_fare (T : Roof.Tilework F) {q k : ℕ} (cap : k ≤ q) (u b : ι) :
    |coeff k (T u b)| ≤ invoice F T q := by
  have one : (k,0) ∈ Finset.HasAntidiagonal.antidiagonal k := by simp
  have first := single_le_sum (f:=fun t : ℕ×ℕ => |coeff t.1 (T u b)|)
    (fun t _ => abs_nonneg _) one
  exact (first.trans (single_le_sum (f:=fun c : ι =>
      ∑ t ∈ Finset.HasAntidiagonal.antidiagonal k, |coeff t.1 (T c b)|)
    (fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) (mem_univ u))).trans (invoice_pays F T cap b)

/-- The finite top may be cut below the original UV cutoff. The same
transfers still use its true nonbare vacuum above that cut. -/
theorem interval (digit : ∀ i, Site (R.family.S.block i)) (N stop first q : ℕ)
    (g : ℕ → ℝ) (report : ι → PowerSeries ℂ) (simple : G.Simple) (o : Stationary.Loc G 1)
    (front : d ≤ R.family.path.levels.clock.J (first+1)) (roof : stop ≤ N)
    (j : ℕ) (fromDate : first ≤ j) (live : j ≤ stop) :
    income R wood a depth digit N stop q g (take R q (lift R wood a depth digit N first g report (stop-first))) j =
      take R q (lift R wood a depth digit N first g report (j-first)) := by
  induction live using Nat.decreasingInduction with
  | self => simp [income,walk]
  | of_succ j hj ih =>
    rw [previous R wood a depth digit N stop q g _ hj,ih (fromDate.trans (Nat.le_succ _))]
    rw [show j+1-first=j-first+1 by omega]
    simp only [WilsonTrueProjectedPointInverse.lift,show first+(j-first)=j by omega]
    rw [coefficients,Matrix.mulVec_mulVec,inverse R wood a depth digit N j (g j) simple o (hj.trans_le roof)
      (front.trans (R.family.path.levels.fits.mono (Nat.succ_le_succ fromDate))),Matrix.one_mulVec]

theorem original (simple : G.Simple) (o : Stationary.Loc G 1) {U : ℕ → ℕ}
    (formal : WilsonWindowFormalPurchase.Canonical U R.kit)
    (point : WilsonNeutralPointForecast.Filed R.kit) (weakly : WilsonNeutralPointWeakForecast.Filed R.kit)
    (q : ℕ) {δ : ℝ} (margin : 0 < δ) :
    ∃ C : ℝ, ∃ V : ℕ, 0 < C ∧ ∀ᶠ first : ℕ in atTop,
    ∀ (_ : d ≤ R.family.path.levels.clock.J (first+1)) (digit : ∀ i, Site (R.family.S.block i))
      (N per stop j : ℕ), first ≤ j → j < stop → stop ≤ N →
    ∀ (v : ι → ℂ) (B : ℝ), 0 ≤ B → (∀ b, ‖v b‖ ≤ B) → ∀ k : Fin (q+1),
    let g := fun l => ConnectedActivityE6.Coat.gStep ((R.family.path.rep N per l).beta)
    let top := take R q (lift R wood a depth digit N first g (fun b => PowerSeries.C (v b)) (stop-first))
    let X := income R wood a depth digit N stop q g top
    (∑ b, ‖X (j+1) k b‖) ≤ (C*(Λ first)^V*B)*
      Real.exp (δ*elapsed R.family.S first j)*(g j)^k.val := by
  classical
  obtain ⟨M,p,hM,onset⟩ := WilsonNeutralPointWeakIncome.funded R wood a depth o simple formal point weakly q
  obtain ⟨m,all⟩ := eventually_atTop.1 onset
  let h := Finset.univ.sup (level R (d:=d) q)
  let zcount := (Fintype.card (Panel R (d:=d) q) : ℝ)
  have z0 : 0 ≤ zcount := Nat.cast_nonneg _
  obtain ⟨C,cp,geometric⟩ := WilsonTrueProjectedPointGrowth.original q p h
    (G.slopeConstant_pos simple).le z0 (zero_le_one.trans hM) margin
  let V := (q+p+3)*h
  refine ⟨(1+(Fintype.card ι:ℝ))*C,V,by positivity,?_⟩
  filter_upwards [Filter.eventually_ge_atTop m] with first fm
  intro front digit N per stop j left right roof v B fund vbound k
  dsimp only
  let g := fun l => ConnectedActivityE6.Coat.gStep ((R.family.path.rep N per l).beta)
  let t := elapsed R.family.S first j
  let n := j-first
  have ages : first+n=j := by dsimp [n];omega
  have funds (i : ℕ) (hi : i ≤ n) (k' : ℕ) (hk : k' ≤ q) (u b : ι) :
      |coeff k' ((WilsonNeutralPointCourse.transfer R wood a depth digit N (first+i))⁻¹ u b)| ≤
       M*(Λ (first+i))^p := by
    have young : first+i ≤ j := by omega
    let Mj := (WilsonNeutralPointCourse.transfer R wood a depth digit N (first+i))⁻¹
    have retained := (all (first+i) (fm.trans (Nat.le_add_right first i))).2 N
      (young.trans_lt (right.trans_le roof)) digit
    exact (entry_fare R Mj hk u b).trans retained
  have initial (z : Panel R (d:=d) q) : ‖readout R q (fun b => PowerSeries.C (v b)) z‖ ≤ B := by
    simp only [readout,coeff_C]
    split_ifs
    · exact vbound _
    · simpa using fund
  have htime : (n:ℝ)*Real.log 3 ≤ t := by simpa only [ages,t] using blocks R.family.S first n
  have hp : 0 < g j := (WilsonTrueProjectedPointClock.thermal R simple left le_rfl
    (right.le.trans roof) (per:=per)).1
  have hbase := (WilsonTrueProjectedPointClock.log_rise R simple left).1
  have ht := WilsonTrueProjectedPointClock.elapsed_nonnegative R left
  have cov (b : ι) :
      ‖take R q (lift R wood a depth digit N first g (fun b => PowerSeries.C (v b)) (n+1)) k b‖ ≤
      (g j)^k.val*B*(C*(Λ first)^V*Real.exp (δ*t)) := by
    let z : Panel R (d:=d) q := (k,b)
    have est := WilsonTrueProjectedPointClock.original R wood a depth digit N per first n q p
      (fun b => PowerSeries.C (v b)) simple o front (by omega) fund (zero_le_one.trans hM) initial funds z
    dsimp only at est
    rw [ages,WilsonTrueProjectedPointGradeLift.constant] at est
    have toll := geometric (Finset.le_sup (f:=level R (d:=d) q) (mem_univ z)) hbase ht htime
    have toll' : (1+zcount*((2*(1+G.slopeConstant*t))^q*(M*(Λ first+G.slopeConstant*t)^p))*((n+1:ℕ):ℝ))^level R q z
      ≤ C*(Λ first)^V*Real.exp (δ*t) := by simpa only [Nat.cast_add,Nat.cast_one] using toll
    exact est.trans (mul_le_mul_of_nonneg_left toll' (mul_nonneg (pow_nonneg hp.le _) fund))
  rw [interval R wood a depth digit N stop first q g (fun b => PowerSeries.C (v b)) simple o
    front roof (j+1) (by omega) (by omega),show j+1-first=n+1 by omega]
  calc
    _ ≤ ∑ _b : ι, (g j)^k.val*B*(C*(Λ first)^V*Real.exp (δ*t)) := sum_le_sum fun b _ => cov b
    _ = (Fintype.card ι : ℝ)*((g j)^k.val*B*(C*(Λ first)^V*Real.exp (δ*t))) := by
      simp only [sum_const,card_univ,nsmul_eq_mul]
    _ ≤ (1+(Fintype.card ι : ℝ))*((g j)^k.val*B*(C*(Λ first)^V*Real.exp (δ*t))) :=
      mul_le_mul_of_nonneg_right (by linarith) (by have := zero_le_one.trans hbase; positivity)
    _ = _ := by dsimp only [t];ring

end YM.Integration.WilsonTrueProjectedPointStock
