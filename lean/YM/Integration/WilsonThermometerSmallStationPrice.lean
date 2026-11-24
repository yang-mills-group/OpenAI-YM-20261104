import YM.Integration.WilsonThermometerSmallPanelRead

/-! Subpower signed physical cost of the actual weak-station fields on the smaller purchased apertures. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.East
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{d n D k N p m:ℕ} {ι:Type}[Fintype ι] {W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ} {L:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (P:ℕ→ ι → Tapes.Panel D) (Z:ArcSky P) (B:Binding C)(H:C.Makes)(h:G.Simple)(hp:Scrim C W u ψ φ δ (fly C.path.levels) r L) (O:HaarBudget G)(J:ChartRatio G)
local notation "A" => C.path.levels

variable (z:ℝ) (hZ : ∀ i≤D,Accent.generator G i≤ z)
open Analysis Next.UVStress Climb Ward
open YM.Integration.WilsonThermometerSmallPanelRead
open YM.Integration.WilsonPositionThermometerStationNorm
include H h hZ hp Z
theorem small_station (f : Extraction.Order) (M : (Cells.standard C).Hierarchy)
    (hn : 2 ≤ n) (x : ι) (d : Fin (D+1)) (ε : ℝ) (pos : 0 < ε) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ᶠ k : ℕ in atTop, ∀ Y,
      PoisedSky (P k) B H O J n z k Y → ∀ᶠ N : ℕ in atTop, ∀ p
      {D' : ℕ} (V : Vane C D') (j : Fin (D'+1)), j.val=d.val → V.k=k →
      V.checked f M D' → ∀ (w : (Cells.standard C).Field j),
        centeredBudget C ⟨j,V.wheel.atCut (N,p) j w⟩
          (Q*((A).clock.hatBeta k)^ε*(cost C d*‖w‖)) (widthSky A (P k x).arc k) N p := by
  obtain ⟨q,hq,columns⟩ := columns_before_period P Z B H h hp O J z hZ hn x d
  let Q := q * (2 * scaleCost C d)
  have fees : 0 ≤ scaleCost C d := Finset.sum_nonneg (fun _ _ => by positivity)
  have Qpos : 0 ≤ Q := mul_nonneg hq (mul_nonneg (by norm_num) fees)
  refine ⟨Q,Qpos,?_⟩
  filter_upwards [columns, YM.Integration.WilsonPositionThermometerStationNorm.original
    (f:=f) (H:=M) h H d ε pos] with k cache station Y seated
  filter_upwards [cache Y seated,eventually_ge_atTop (k+1)] with N budget late p D' V j eqAge site proved w
  have upper : k<N := by omega
  let b := mag A (P k x).arc k
  have mon : 1 ≤ (A).clock.monitor k := Real.one_le_exp (sq_nonneg _)
  have exponent : 0 ≤ (P k x).arc := by linarith only [(P k x).huge,(show (0:ℝ) ≤ (D:ℝ) by positivity)]
  have one : 1≤b := Real.one_le_rpow mon exponent
  let T := Y N p d
  have HT : Tested C d k N p T := (seated.charts N p upper d).1
  have any (v : C.label d) :
      centeredBudget C ⟨d,v⟩ (Q*(C.labels.level d).coeffSize (awake C d k N p v))
        (widthSky A (P k x).arc k) N p := by
    let u := column C d k N p b T v
    obtain ⟨width,ref,atSite⟩ := budget p u
    have seatedSame := recovers C H (seated.early d (Nat.le_of_lt_succ d.isLt)) upper.le
      b (zero_lt_one.trans_le one).ne' T HT v
    change ladd C b k N p d T u = v at seatedSame
    refine ⟨width,ref,fun o => ?_⟩
    have panel := atSite o
    change Interior ((center C.S p width o).chamber 0) (C.O N p (ladd C b k N p d T u) o) ∧
      (center C.S p width o).rootTest (C.beta N p) (C.O N p (ladd C b k N p d T u) o) ≤ _ at panel
    rw [seatedSame] at panel
    refine ⟨panel.1,panel.2.trans ?_⟩
    exact (mul_le_mul_of_nonneg_left (price C H upper.le mon b one T HT v) hq).trans_eq (by ring)
  rw [←eqAge] at any
  obtain ⟨width,ref,atSite⟩ := any (V.wheel.atCut (N,p) j w)
  have norm := station V j eqAge site proved w N p upper
  refine ⟨width,ref,fun o=> ⟨(atSite o).1,(atSite o).2.trans ?_⟩⟩
  exact (mul_le_mul_of_nonneg_left norm Qpos).trans_eq (by ring)

end YM.MergeProof.East
