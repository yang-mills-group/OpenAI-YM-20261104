import YM.Integration.WilsonPositionThermometerStationNorm
import YM.Integration.ActualTrajectoryTransport
import YM.Next.RANK.TrueWind

/-! Engineering-normalized complete original one-source row on the
reporting torus. The regular and compulsory pieces use the original
history down from the ultraviolet, including the incoming Wilson law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionThermometerDepositedRow
open Function Set Filter MeasureTheory Lattice Wilson RG Source Table Spec Labels
open Climb Trace Trace.Pilot Next.UVStress Next.Rank Next.Rank.Spindle
open MergeProof.Accent MergeProof.East Extra.Histories
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {d k N p : ℕ} (hc : C.Makes)

def row (C : Family G) (d k N p : ℕ) (v : C.label d) :=
  parcel C d k N p (pinHat C d k • v)

include hc

theorem coordinate (ref : C.ref d ≤ k) (upper : k ≤ N) (v : C.label d) :
    (row C d k N p v).x = Price.awake C d k N p v := by
  let T := C.factory d N p
  have linear := ((hc.calibrated d N p (ref.trans upper)).linear k ref upper).1
  change (T.entries k (T.terminal.symm (pinHat C d k • v))).x =
    pinHat C d k • (T.entries k (T.terminal.symm v)).x
  rw [map_smul,linear.map_smul]

private theorem flow (ref : C.ref d ≤ k) (upper : k ≤ N) (v : C.label d) :
    (row C d k N p v).density 0 (C.localSection d) (C.path.rep N p k) =
      gust C.path N p N (singleP C N p v) k upper := by
  let X : Course C N p k := ⟨C.path.β N p,upper,fun _ _ _=>rfl,
    fun _ i=>Overlay.beta_positive hc.wilson i⟩
  let a := pinHat C d k
  have nz : a≠0 := inv_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (C.S.a_pos k).ne'))
  have read := rates_arc hc ref X (a • v) k upper le_rfl
  have tilt : singleP C N p (a • v) = a • singleP C N p v := by
    funext U
    have lin := C.linearO N p d (0 : Site (C.side N p))
    simp only [singleP,lin.map_smul,Pi.smul_apply,smul_eq_mul]
    ring
  rw [tilt,flows_smul C X _ (singleP_int C N p v) a k upper] at read
  have cancel := congrArg (fun f : Config G (C.side k p) → ℂ => a⁻¹ • f) read
  change a⁻¹ • (a • (row C d k N p v).density 0 (C.localSection d) (C.path.rep N p k)) =
      a⁻¹ • (a • gust C.path N p N (singleP C N p v) k upper) at cancel
  simpa only [smul_smul,inv_mul_cancel₀ nz,one_smul] using cancel

theorem deposited (ref : C.ref d ≤ k) (upper : k ≤ N) (v : C.label d)
    (U : Config G (C.side k p)) :
    (row C d k N p v).density 0 (C.localSection d) (C.path.rep N p k) U =
      (C.path.rep N p k).eval U • actualTransport C (N:=N) (C.O N p v 0) upper U := by
  rw [actualTransport_unnormalize C hc (le_rfl : N≤N),flow hc ref upper v]
  apply congrArg (fun f => gust C.path N p N f k upper U)
  funext Y
  rw [(hc.wilson.starts N p).2]
  exact Complex.real_smul.symm

theorem paid {f : Extraction.Order} {H : (Bel C.book).Hierarchy}
    (smooth : G.Simple) (d : ℕ) (ε : ℝ) (positive : 0 < ε) :
    ∀ᶠ k in atTop, ∀ {D : ℕ} (V : Vane C D) (j : Fin (D+1)), j.val=d → V.k=k →
      V.checked f H D → C.ref j ≤ k → ∀ (w : (Bel C.book).Field j) (N p : ℕ) (upper : k<N),
      let v := V.wheel.atCut (N,p) j w
      let q := row C j k N p v
      let P := C.path.rep N p k
      q.Format 0 C.params P ∧ q.x=Price.awake C j k N p v ∧
      q.remBound 0 P (Real.sqrt (C.path.levels.clock.forcedAllowance k))
        ((C.path.levels.params k).columns * ((C.path.levels.clock.hatBeta k)^ε *
          (WilsonPositionThermometerStationNorm.cost C d * ‖w‖))) ∧
      ∀ U,q.density 0 (C.localSection j) P U=P.eval U • actualTransport C (N:=N) (C.O N p v 0) upper.le U := by
  filter_upwards [WilsonPositionThermometerStationNorm.original (f:=f) (H:=H) smooth hc d ε positive]
    with k grant D V j grade date tested ref w N p upper v q P
  have data := hc.calibrated j N p (ref.trans upper.le)
  have hx := coordinate (p:=p) hc ref upper.le v
  have price := grant V j grade date tested w N p upper
  refine ⟨data.format k ref upper.le _,hx,rem_mono (data.cap k ref upper.le _) ?_,deposited hc ref upper.le v⟩
  apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans (C.path.levels.params k).columns_ge)
  exact (Work.G08.size_core _ _).trans (hx ▸ price)

end YM.Integration.WilsonPositionThermometerDepositedRow
end
