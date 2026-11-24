import YM.Integration.WilsonThermometerWeakCoefficientTail
import YM.Integration.WilsonThermometerWeakMeasuredBounds

/-! Ordinary finite coefficient restoration on the measured continuum frame.
A signed physical comparison to the independently posted polynomial on this
same frame is required at one finite order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakMeasuredSeries
open Set Filter Function Spec Trace.Pilot OPE OPE.Orbits Next.UVStress Climb PhysMS PhysMS.Frame
open WilsonThermometerWeakValueRecovery WilsonThermometerWeakCoefficientTail
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    (F:Final C f S)(R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (U:ℝ→tower S)(H:Leading F U)(simple:G.Simple)(X:Scaling S)(built:Foundation F R)
    {n:ℕ}{d:Caps n}

def approximate (v:ℕ→Points n→ℂ)(p:ℕ)(t:ℝ):Points n→ℂ:=part v (Finset.range (p+1)) t

private theorem sub_bounds {A:Type*}{l:Filter A}{K:Set (Points n)}(openK:IsOpen K)
    (T P:A→Points n→ℂ)(j:ℕ)(left:∀ᶠr in l,ContDiffOn ℝ ∞ (T r) K)
    (right:∀ᶠr in l,ContDiffOn ℝ ∞ (P r) K)(u:Bounded l K T j)(v:Bounded l K P j):
    Bounded l K (fun r=>T r-P r) j:=by
  intro L compact clear
  obtain ⟨B,bp,fee⟩:=u L compact clear
  obtain ⟨D,dp,tail⟩:=v L compact clear
  refine ⟨B+D,add_nonneg bp dp,?_⟩
  filter_upwards [left,right,fee,tail] with r sm₁ sm₂ one two x hx
  have p₁:=((sm₁ x (clear hx)).contDiffAt (openK.mem_nhds (clear hx))).of_le
    (show (j:WithTop ℕ∞)≤∞ from WithTop.coe_le_coe.mpr le_top)
  have p₂:=((sm₂ x (clear hx)).contDiffAt (openK.mem_nhds (clear hx))).of_le
    (show (j:WithTop ℕ∞)≤∞ from WithTop.coe_le_coe.mpr le_top)
  rw [iteratedFDeriv_sub_apply p₁ p₂]
  exact (norm_sub_le ..).trans (add_le_add (one x hx) (two x hx))

include R H simple X built in
/-- The same chosen external derivative height D finances every point of the
compact collar. The independent coefficients are in the numerical g variable
of the common reported frame. -/
theorem original (v:MaxwellSlots C d)(c:ℕ→Points n→ℂ)(g:ℝ→ℝ)(j p D q:ℕ)(retains:WilsonThermometerWeakSignedJets.high j p≤q)
    (limit:Tendsto g trail (𝓝 0))(positive:∀ᶠr in trail,0<g r)
    (legal:∀a≤q,ContDiffOn ℝ ∞ (c a) (conf n))
    (posted:WilsonThermometerWeakValueRecovery.Signed trail (conf n)
      (fun r=>measured F none (U r) v r-approximate c q (g r))
      g (WilsonThermometerWeakSignedJets.high j p+1) D):
    ∀L,IsCompact L→L⊆conf n→∀ε:ℝ,0<ε→∀ᶠr in trail,∀x∈L,
      ‖iteratedFDeriv ℝ j (measured F none (U r) v r) x-
        iteratedFDeriv ℝ j (approximate c p (g r)) x‖≤ε*g r^p:=by
  let T:=fun r=>measured F none (U r) v r
  let A:=fun r=>approximate c q (g r)
  let B:=fun r=>approximate c p (g r)
  have pq:p≤q:=(Nat.le_succ p).trans ((Nat.le_mul_of_pos_left (p+1) (pow_pos (by decide) j)).trans retains)
  have continuous (k:ℕ)(hk:k≤q)(r:ℝ):ContDiffOn ℝ ∞ (approximate c k (g r)) (conf n):=
    smooth c _ _ fun a ha=>legal a ((Nat.le_of_lt_succ (Finset.mem_range.mp ha)).trans hk)
  have st:∀ᶠr in trail,ContDiffOn ℝ ∞ (T r) (conf n):=(show ∀ᶠr:ℝ in trail,0<r from self_mem_nhdsWithin).mono
    fun r hr=>WilsonThermometerWeakMeasuredBounds.unselected F U v r hr
  have sa:∀ᶠr in trail,ContDiffOn ℝ ∞ (A r) (conf n):=Eventually.of_forall (continuous q le_rfl)
  have sb:∀ᶠr in trail,ContDiffOn ℝ ∞ (B r) (conf n):=Eventually.of_forall (continuous p pq)
  have flat:∀k,Bounded trail (conf n) (fun r=>T r-A r) k:=by
    intro k
    apply sub_bounds (conf_open n) T A k st sa (WilsonThermometerWeakMeasuredBounds.original F R U H simple X built v (fun _=>none) k)
    have finite:=WilsonThermometerWeakCoefficientTail.original (conf_open n) c (Finset.range (q+1)) g k 0
      (fun a ha=>legal a (Nat.le_of_lt_succ (Finset.mem_range.mp ha))) (fun a _=>Nat.zero_le _) limit (positive.mono fun _ h=>h.le)
    simpa only [Price,pow_zero,mul_one,WilsonThermometerWeakValueRecovery.Bounded,A,approximate] using finite
  have estimated:=WilsonThermometerWeakSignedJets.measured (conf_open n) (Subset.rfl) g j p D limit positive
    (fun r=>T r-A r) ((st.and sa).mono fun _ h=>h.1.sub h.2) posted (flat _) (fun k _ _=>flat k)
  apply WilsonThermometerWeakSignedJets.restore (conf_open n) g j p limit positive T B A st sa sb estimated
  have cutoff: (fun r=>A r-B r)=(fun r=>part c (Finset.Ico (p+1) (q+1)) (g r)):=by
    funext r x
    change (∑a∈Finset.range (q+1),g r^a • c a x)-(∑a∈Finset.range (p+1),g r^a • c a x)=_
    rw [←Finset.sum_range_add_sum_Ico (fun a=>g r^a • c a x) (Nat.succ_le_succ pq)]
    dsimp [part]
    abel
  rw [cutoff]
  exact WilsonThermometerWeakCoefficientTail.original (conf_open n) c _ g j (p+1)
    (fun a ha=>legal a (Nat.le_of_lt_succ (Finset.mem_Ico.mp ha).2))
    (fun _ ha=>(Finset.mem_Ico.mp ha).1) limit (positive.mono fun _ h=>h.le)

end YM.Integration.WilsonThermometerWeakMeasuredSeries
end
