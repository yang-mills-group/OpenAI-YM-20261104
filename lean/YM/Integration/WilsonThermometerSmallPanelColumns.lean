import YM.Integration.WilsonThermometerSmallPanelMoment
import YM.TraceExtension.Prom.Zoom.Boats

/-! Uniform linear-combination prices on a genuine smaller reflected panel. -/
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
include H h hZ hp Z
theorem columns_before_period (hn : 2 ≤ n) (x : ι) (d : Fin (D+1)) :
    ∃ Q : ℝ, 0 ≤ Q ∧
    ∀ᶠ k : ℕ in atTop, ∀ Y, PoisedSky (P k) B H O J n z k Y →
    ∀ᶠ N : ℕ in atTop, ∀ p (v : C.label d),
      centeredBudget C ⟨d,ladd C (mag A (P k x).arc k) k N p d (Y N p d) v⟩
        (Q * (C.labels.level d).coeffSize v) (widthSky A (P k x).arc k) N p := by
  let I := (C.labels.level d).Index
  let e (i : I) : C.label d := Pi.single i 1
  choose q positive charged using fun i : I =>
    single_before_period P Z B H h hp O J z hZ hn x d (e i)
  let Q := ∑ i : I, q i
  have cap (i : I) : q i ≤ Q :=
    Finset.single_le_sum (f:=q) (fun i _ => positive i) (Finset.mem_univ i)
  refine ⟨Q,Finset.sum_nonneg (fun i _ => positive i),?_⟩
  filter_upwards [eventually_all.mpr charged] with k paid Y seated
  filter_upwards [eventually_all.mpr (fun i => paid i Y seated),eventually_ge_atTop (k+1)]
    with N receipts late p v
  let b := (P k x).arc
  let m := widthSky A b k
  have hk : m ≤ N := (widerSky A b k).trans ((beforeSky A b k).trans (by omega))
  refine ⟨hk,(seated.early d (Nat.le_of_lt_succ d.isLt)).trans (by omega),?_⟩
  intro s
  let T := center C.S p hk s
  let β := C.beta N p
  let L := ladd C (mag A b k) k N p d (Y N p d)
  let F (i : I) := C.O N p (L (e i)) s
  have basis (i : I) : Interior (T.chamber 0) (F i) ∧ T.rootTest β (F i) ≤ q i :=
    (receipts i p).choose_spec.2 s
  have total : ∑ i : I, v i • e i = v := by
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp [e]
    · intro i _ other
      simp [e,Ne.symm other]
    · simp
  have repr : C.O N p (L v) s = ∑ i, v i • F i := by
    let M := (C.linearO N p d s).mk' (fun t => C.O N p t s)
    have expansion := congrArg (fun t => M (L t)) total
    change M (L v) = ∑ i, v i • M (L (e i))
    simpa only [map_sum,map_smul] using expansion.symm
  obtain ⟨inside,bound⟩ := Next.UVStress.root_sum T β Finset.univ F v
    (fun i _ => (basis i).1) (seamless H N p)
  change Interior (T.chamber 0) (C.O N p (L v) s) ∧ T.rootTest β (C.O N p (L v) s) ≤ _
  rw [repr]
  refine ⟨inside,bound.trans ?_⟩
  calc
    ∑ i, ‖v i‖ * T.rootTest β (F i) ≤ ∑ i, ‖v i‖ * Q :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left ((basis i).2.trans (cap i)) (norm_nonneg _))
    _ = Q * (C.labels.level d).coeffSize v := by
      rw [Labels.Frame.coeffSize,Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

end YM.MergeProof.East
