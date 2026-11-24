import YM.AllOrder.Leading.Correct
import YM.TraceExtension.Atlas.Sink

/-!
# All-length compatible choice, including trace leading normalization

Scales on the physical trajectory. Here we use a `Pilot.Coupling`, which
has the **leading** normalization only. We never transfer an O(g⁴) to a
different coupling without further estimates. This stage needs the estimates
from the Step/Lantern supplies of the trace extension, not just the
perturbative coefficient `d₂`.

The value of a frame on smaller length tails for each finite horizon is the
one relevant for using it. Compatibility of rises is exact there. Above the
running horizon, maps are totalized but not yet required compatible at
those lengths. This is an eventually-compatible germ formulation.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Leading
open Spec Function Filter Set Extraction Climb Table Ward Trace Trace.Pilot Trace.Terrace Analysis
open Trace.Over MergeProof.East Next.UVStress Maxwell Spin Next.Rank
open scoped BigOperators Topology Classical ContDiff
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable {F : Spec.Final C f S}
local notation "free" => Bel C.book

/-- Use inverse `BQ` normalization from the actual Scribe, compare to the
leading Wilson normalization in this coordinate only. -/
lemma scribe_clock {h : (free).Hierarchy} {l : Ultrafilter (ℕ × ℕ)}
    {V : ∀ i, Vane C i} {Z : Arch C} {J : Scaling S} (hG : G.Simple)
    (hj : Scribe f J V Z F.sector l F.room.kernel h) {g : ℝ → ℝ} (hg : Coupling G g) :
    Tendsto (fun i => BQ Z V i * g (J.r i)^2) atTop (𝓝 1) := by
  have hr : Tendsto J.r atTop trail := tendsto_nhdsWithin_iff.mpr
    ⟨J.drips, Eventually.of_forall J.positive⟩
  have hz : G.slopeConstant⁻¹≠0 := inv_ne_zero (Gauge.slopeConstant_pos hG).ne'
  have H := (hg.running.comp hr).div hj.clock hz; rw [div_self hz] at H
  apply H.congr'; filter_upwards [hj.clock.eventually_ne hz,hj.grows.eventually_gt_atTop 0] with i hi hp
  let b := BQ Z V i; let z := LogZoom J i
  change z*g (J.r i)^2/(z/b)= _; have hf : b≠0 := hp.ne'; have hb : z≠0 := (div_ne_zero_iff.mp hi).1
  field_simp; rfl

/-- One frame map family. -/
abbrev FamilyFrame (S : Table C.book) := (d : ℕ) → Spin.change S d

/-- Block of starting conditions, centred *unselected* stress. -/
def BundleTests (F : Spec.Final C f S) (g : ℝ → ℝ) (r : ℝ) (X : FamilyFrame S) (m : ℕ) : Prop :=
    (∀ d : Fin (m+1), Spin.realH F.room.kernel.spin (Free.spin_free C.labels) (X d)) ∧
    (∀ d : Fin (m+1), X d ((free).unit d)=S.unit d) ∧
    (∀ (d e : Fin (m+1)) (h : d.val ≤ e.val), ∀ x,
        X e ((Free.scheme C.labels).rise h x) = F.sector.derivatives.rise h (X d x)) ∧
    (∀ (n : Fin (m+1)) (t : Fin n → Fin (m+1))
       (x : Code fun i : Fin n => (free).Field (t i))
       (j : Fin (m+1)), ∀ y ∈ Scaling.window (sizeHint m) n,
          let p := hang (Fin.val ∘ t) (combination (fun i : Fin n => (free).Field (t i)) x)
          ‖iteratedFDeriv ℝ j (tested r (fun d => (X d).toLinearMap) p) y -
            iteratedFDeriv ℝ j (disc p) y‖ < costHint m) ∧
    (∀ i j : Axis, ‖ r^4 • ((X 4).symm (reCenter S F.sector.energy i j)) -
        standard4 C i j‖ < costHint m) ∧
    ‖(X 4).symm (((g r^2)⁻¹ * r^4) • TraceExtension.theta S F.sector.energy) -
       (4*d2 G) • stepField C‖ < costHint m -- notation parentheses?

lemma bundle_seq {Z : Arch C} {h : (free).Hierarchy} {l : Ultrafilter (ℕ × ℕ)}
    (hG : G.Simple) (hs : Bliss F l Z h) {g : ℝ → ℝ} (hg : Coupling G g)
    (m : ℕ) : ∀ᶠ r in trail, ∃ X : FamilyFrame S, ∀ j : Fin (m+1), BundleTests F g r X j := by
  by_contra hx
  obtain ⟨s,hS,hQ⟩ := contradictionTrail _ hx
  obtain ⟨u,hu,J,hJ,V,H⟩ := hs.picks s (hS.mono_right nhdsWithin_le_nhds) (fun i => (hQ i).1)
  obtain ⟨Y,hY,hA,hB,hX⟩ := align_seq (F:=F) hG H.monorail
  have hT : Tendsto (fun i => (J.U i 4).symm (((g (J.r i)^2)⁻¹ * (J.r i)^4) • TraceExtension.theta S F.sector.energy))
      atTop (𝓝 ((4*d2 G) • stepField C)) := by
    have hm := ((scribe_clock hG H hg).inv₀ one_ne_zero).smul (H.goal S); rw [inv_one,one_smul] at hm
    apply hm.congr'; filter_upwards [H.grows.eventually_gt_atTop 0] with i hi
    let b := BQ Z V i; let A := TraceExtension.theta S F.sector.energy; let t := J.r i; let T := (J.U i 4).symm.toLinearMap.restrictScalars ℝ
    have hb : b ≠ 0 := hi.ne'
    change (b*g t^2)⁻¹ • T ((b*t^4) • A)= T _
    rw [← map_smul,smul_smul]; apply congrArg T; congr 1; rw [mul_inv_rev]; field_simp; rfl
  have hy (m : Fin (m+1)) : ∀ᶠ k in atTop, BundleTests F g (Y.r k) (Y.U k) m := by
    have hΘ (i j : Axis) := Metric.tendsto_nhds.mp (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp H.main i) j) (costHint m) (cost_pos _)
    unfold BundleTests
    refine (eventually_all.mpr (fun (d : Fin (m.val+1)) => hB.hsym d)).and
      ((eventually_all.mpr (fun (d : Fin (m.val+1)) => hB.units d)).and (?and_3))
    refine Eventually.and ?inc (Eventually.and ?jets ?stress)
    case inc =>
      apply eventually_all.mpr; intro d; apply eventually_all.mpr; intro e; by_cases ht : d.val≤e.val
      · exact (hB.rises d e ht).mono fun i hi _ => hi
      exact Eventually.of_forall fun _ h => (ht h).elim
    case jets =>
      apply eventually_all.mpr; intro n; apply eventually_all.mpr; intro t; apply eventually_all.mpr; intro x; apply eventually_all.mpr; intro j
      let y := combination (fun i : Fin n => (free).Field (t i)) x; let P := hang (Fin.val ∘ t) y
      refine (travels_jet F.room.kernel F.phase.transport.derivatives h (Free.scheme_derives C.labels)
        Y hA (t:=Fin.val ∘ t) (fun _ => y) y (fun _ => tendsto_const_nhds)
        j (Scaling.window (sizeHint m) n) (window_closed ..) ?_ _ (half_pos (cost_pos m))).mono
          (fun _ hi x hx => (hi x hx).trans_lt (half_lt_self (cost_pos _)))
      exact fun _ hx => spaced_conf (cost_pos _) hx.1
    case stress =>
      filter_upwards [hX,eventually_all.mpr (fun i=>eventually_all.mpr (hΘ i)),
        Metric.tendsto_nhds.mp hT _ (cost_pos m)] with i hi hj ht
      simp_rw [dist_eq_norm] at hj ht; rw [hi,hY]; exact ⟨hj, ht⟩
  obtain ⟨k,hk⟩ := (eventually_all.mpr hy).exists
  apply (hQ (u k)).2
  change ¬_ at hx
  exact ⟨Y.U k, show _ from (show Y.r k=s (u k) from congr_fun (hY.trans hJ) k) ▸ hk⟩

/-- Implement one diagonal choice, using glen from trace. -/
lemma bundle_exists {Z : Arch C} {h : (free).Hierarchy} {l : Ultrafilter (ℕ × ℕ)}
    (hG : G.Simple) (hs : Bliss F l Z h) {g : ℝ → ℝ} (hg : Coupling G g) :
    ∃ X : ℝ → FamilyFrame S, ∀ m : ℕ, ∀ᶠ r in trail, BundleTests F g r (X r) m := by
  let U(r:ℝ)(X : FamilyFrame S)(m:ℕ):= ∀ j:Fin (m+1), BundleTests F g r X j
  let W(r:ℝ):= (Finset.range (glen C.S r+1)).filter (fun i=> ∃ p,U r p i)
  obtain ⟨x,X,hX⟩ := (bundle_seq hG hs hg 0).exists
  let R(r:ℝ):= if h:(W r).Nonempty then
        (show ∃ f,U r f ((W r).max' h) from (Finset.mem_filter.mp (Finset.max'_mem (W r) h)).2).choose
      else X
  have ht(m:ℕ):∀ᶠ r in trail,U r (R r) m := by
    filter_upwards[bundle_seq hG hs hg m,(glen_leads C.S).eventually_ge_atTop m] with x hx hm
    have hv:m ∈ W x:=Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hm),hx⟩
    have hQ:(W x).Nonempty:=⟨m,hv⟩
    let t:= (W x).max' hQ
    have he: U x (R x) t:=by
      unfold R; rw[dif_pos hQ]; exact (show ∃ X,U x X t from (Finset.mem_filter.mp (Finset.max'_mem (W x) hQ)).2).choose_spec
    exact fun j => he (Fin.castLE (Nat.succ_le_succ (Finset.le_max' _ m hv)) j)
  exact ⟨R,fun m=> (ht m).mono fun i hi=> hi (Fin.last m)⟩
end YM.AllOrder.Leading
