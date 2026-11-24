import YM.AllOrder.Leading.Raw

/-!
# Leading correlation kernels at ALL scales / ALL finite horizons

Scale convention compatible with the Trace `Final`; frame choice out of the
same field system. Includes verifying the trace reading with any indicated
leading coupling. Later compare frames before claiming higher order.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Leading
open Spec Function Filter Set Extraction Climb Table Ward Trace Trace.Pilot Trace.Terrace Analysis
open Trace.Over MergeProof.East Next.UVStress Maxwell Spin Next.Rank
open scoped BigOperators Topology Classical ContDiff
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable {F : Spec.Final C f S} {U : ℝ → FamilyFrame S} {g : ℝ → ℝ}
local notation "free" => Bel C.book

/-- Read on this frame. -/
abbrev tableRead {n : ℕ} (V : FamilyFrame S) (r : ℝ) (v : Fin n → (free).Tag) :=
    tested r (fun d => (V d).toLinearMap) v

/-- The centred field conventions are unselected here; the centered stress
is literally the same as in `Spec.Final` except the units. -/
structure Aligned (F : Spec.Final C f S) (g : ℝ → ℝ) (U : ℝ → FamilyFrame S) : Prop where
  respects (d : ℕ) : ∀ᶠ r in trail, Spin.realH F.room.kernel.spin (Free.spin_free C.labels) (U r d)
  unit (d : ℕ) : ∀ᶠ r in trail, U r d ((free).unit d) = S.unit d
  nested (d e : ℕ) (h : d ≤ e) : ∀ᶠ r in trail, ∀ x,
    U r e ((Free.scheme C.labels).rise h x) = F.sector.derivatives.rise h (U r d x)
  jets (n : ℕ) (v : Fin n → (free).Tag) (j : ℕ) (K : Set (Points n))
      (hK : IsCompact K) (hV : K ⊆ conf n) {ε : ℝ} (he : 0 < ε) :
    ∀ᶠ r in trail, ∀ x ∈ K, ‖iteratedFDeriv ℝ j (tableRead (U r) r v) x -
      iteratedFDeriv ℝ j (disc v) x‖ < ε
  generator (i j : Axis) : Tendsto
    (fun r => (r^4 : ℝ) • (U r 4).symm (reCenter S F.sector.energy i j))
      trail (𝓝 (standard4 C i j))
  trace : Tendsto
    (fun r => (U r 4).symm (((g r^2)⁻¹ * r^4) • TraceExtension.theta S F.sector.energy))
    trail (𝓝 ((4*d2 G) • stepField C))

/-- Expand an arbitrary input and take its finite jets. Needed because the
diagonal construction keeps the same family of frames for all finite labels.
Useful for moving-label estimates after converting frames. -/
lemma expand_jet {n : ℕ} (hS : S.Hierarchy) (P : FamilyFrame S)
    {r : ℝ} (hr : 0<r) {t : Fin n → ℕ}
    (v : Ribbon (free) t) (j : ℕ) {x : Points n} (hV : x ∈ conf n) :
    ‖iteratedFDeriv ℝ j (tableRead P r (hang t v)) x - iteratedFDeriv ℝ j (disc (hang t v)) x‖ ≤
    ∑ b : record C t, ‖coords _ b v‖ * ‖iteratedFDeriv ℝ j (tableRead P r (hang t (combination _ b))) x -
       iteratedFDeriv ℝ j (disc (hang t (combination _ b))) x‖ := by
    let R(b : record C t) := tableRead P r (hang t (combination _ b))
    let T (b : record C t) := disc (hang t (combination _ b))
    let w(b : record C t) := coords _ b v
    have hg(y : Points n) : tableRead P r (hang t v) y= ∑ b,w b • R b y :=
      basis_tuple _ v ((S.classMoment S t (r • y)).compLinearMap (fun i => (P (t i)).toLinearMap))
    have hh(y : Points n) : disc (hang t v) y= ∑ b,w b • T b y :=
      basis_tuple _ v ((free).classMoment free t y)
    have hR b : ContDiffAt ℝ j (R b) x := (((smoothZoom hS.smooth _ hr) x hV).contDiffAt
          ((conf_open _).mem_nhds hV)).of_le (WithTop.coe_le_coe.mpr le_top)
    have hT b : ContDiffAt ℝ j (T b) x := (cont_disc (Free.hierarchy C.labels) _ hV).of_le (WithTop.coe_le_coe.mpr le_top)
    rw [funext hg,funext hh, iteratedFDeriv_fun_sum_apply (f:=fun b y=> w b • R b y)
      (fun i _ => (hR i).const_smul _),iteratedFDeriv_fun_sum_apply (f:=fun b y=> w b • T b y) (fun i _ => (hT i).const_smul _), ← Finset.sum_sub_distrib]
    refine le_trans (norm_sum_le ..) (le_of_eq (Finset.sum_congr rfl fun b _ => ?_))
    rw [iteratedFDeriv_const_smul_apply' (hR b),iteratedFDeriv_const_smul_apply' (hT b), ← smul_sub, norm_smul]

set_option maxHeartbeats 200000 in
theorem tasks_aligned
    (h : ∀ m : ℕ, ∀ᶠ r in trail, BundleTests F g r (U r) m) : Aligned F g U := by
  refine ⟨fun d => (h d).mono fun r hr => hr.1 (Fin.last d),
      fun d => (h d).mono fun r hr => hr.2.1 (Fin.last d),
      fun d e hde => (h e).mono fun r hr => hr.2.2.1 (⟨d,Nat.lt_succ_of_le hde⟩ : Fin (e+1))
        (Fin.last e) hde, ?_,?_,?_⟩
  · intro n v j K hK hC ε he
    let t (i : Fin n) := (v i).1
    let V : Ribbon (free) t := fun i => (v i).2
    let c := ∑ b : record C t, ‖coords _ b V‖
    obtain ⟨m,hT,hj,hn,hW,hv⟩ := ((eventually_all.mpr (fun i=>eventually_ge_atTop (t i))).and
        ((eventually_ge_atTop j).and ((eventually_ge_atTop n).and
         ((size_ascends.eventually (Work.A05.compact_fits hK hC)).and
          ((cost_clears.const_mul c).eventually (gt_mem_nhds (by simpa using he))))))).exists
    have hv : c*costHint m < ε := hv
    let n' : Fin (m+1) := ⟨n,Nat.lt_succ_of_le hn⟩
    let d(i:Fin n) : Fin (m+1) := ⟨t i,Nat.lt_succ_of_le (hT i)⟩
    filter_upwards [h m,self_mem_nhdsWithin] with r hr hx p hp
    have hg(b : record C t) := hr.2.2.2.1 n' d b (⟨j,Nat.lt_succ_of_le hj⟩ : Fin (m+1)) p (hW hp)
    change ‖iteratedFDeriv ℝ j (tableRead (U r) r (hang t V)) p-iteratedFDeriv ℝ j (disc (hang t V)) p‖< ε
    refine lt_of_le_of_lt ((expand_jet F.room.kernel (U r) (show 0<r from hx) V j (hC hp)).trans ?_) hv
    unfold c; rw [Finset.sum_mul]; exact Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hg b).le (norm_nonneg _)
  · intro i j; refine Metric.tendsto_nhds.mpr fun ε he => ?_
    obtain ⟨m,hε⟩ := (cost_clears.eventually (gt_mem_nhds he)).exists
    filter_upwards [h m] with r hr
    rw [dist_eq_norm]; exact (hr.2.2.2.2.1 i j).trans hε
  · refine Metric.tendsto_nhds.mpr fun ε he => ?_
    obtain ⟨m,hε⟩ := (cost_clears.eventually (gt_mem_nhds he)).exists
    filter_upwards [h m] with r hr
    rw [dist_eq_norm]; exact hr.2.2.2.2.2.trans hε

theorem aligned_exists {Z : Arch C} {h : (free).Hierarchy} {l : Ultrafilter (ℕ × ℕ)}
    (hG : G.Simple) (hs : Bliss F l Z h) {g : ℝ → ℝ} (hg : Coupling G g) :
    ∃ U : ℝ → FamilyFrame S, Aligned F g U := by
  obtain ⟨X,hX⟩ := bundle_exists hG hs hg
  exact ⟨X,tasks_aligned hX⟩

end YM.AllOrder.Leading
