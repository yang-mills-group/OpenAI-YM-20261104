import YM.SignedWilsonExpansion.Homes.MeterQ

/-! Relative cost understood in the physical-ordered sense: for all sufficiently late
UV at fixed regulator data. Use Ultrafilter association only to compare on those tails.
We will not require lifting the hierarchy projectors individually on this filter. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.SignedWilsonExpansion.Homes
open Function Filter Set MeasureTheory Extraction Climb Spec Table Next.UVStress OPE.Levy Trace.Pilot PhysMS PhysMS.Frame
open MergeProof.East Next.Rank Ward Next.Rank.East Pert.Scale Maxwell Extra.FD PhysicalNext.Repeat.Legato Run Lattice FullVolume Cells
open scoped Topology BigOperators Classical ContDiff
variable {ι α:Type*}

variable {Y:Type*} {L:Filter ι} {f : Filter α} [f.NeBot]
theorem surveyM (P:ι→α→Prop) : ∃ U:ι→Ultrafilter α,(∀ i, (U i:Filter _) ≤ f) ∧
   ∀ i, (∃ᶠ v in f, P i v) → ∀ᶠ v in (U i:Filter α), P i v := by
   have hx(i):∃ U:Ultrafilter α,(U:Filter α) ≤ f ∧ ((∃ᶠ v in f, P i v) → ∀ᶠ v in (U:Filter α), P i v) := by
      by_cases h:∃ᶠ v in f, P i v
      · obtain ⟨U,u⟩:= exists_ultrafilter_iff.mpr (frequently_iff_neBot.mp h)
        exact ⟨U,u.trans inf_le_left, fun _=> Filter.le_principal_iff.mp (u.trans inf_le_right) ⟩
      obtain ⟨U,u⟩:=exists_ultrafilter_iff.mpr (show NeBot f by infer_instance)
      exact ⟨U,u,fun s=> (h s).elim⟩
   choose k h t using hx; exact ⟨k,h,t⟩

lemma pairsC {X : ι→α→ ℂ} {z:ℂ}
   (H: ∀ U:ι→Ultrafilter α,(∀ i,(U i:Filter _) ≤ f) → ∃ v:ι→ℂ,
   (∀ᶠ i in L,Tendsto (X i) (U i:Filter α) (𝓝 (v i))) ∧ Tendsto v L (𝓝 z)) :
   Tendsto (fun p:ι× α => X p.1 p.2) (L.curry f) (𝓝 z) := by
   apply Metric.tendsto_nhds.mpr
   intro ε ep
   change ∀ᶠ i in L, ∀ᶠ p in f, dist (X i p) z < ε
   obtain ⟨U,hu,H'⟩:= surveyM (f:=f) (fun i p=>¬ dist (X i p) z < ε)
   obtain ⟨v,px,P⟩:= H U hu
   filter_upwards [P.eventually (Metric.ball_mem_nhds _ ep),px] with i hi hz
   by_contra h
   have he: ∀ᶠ p in (U i:Filter α), dist (X i p) z < ε := hz.eventually (Metric.isOpen_ball.mem_nhds hi)
   obtain ⟨p,H,H'⟩:=(he.and (H' i (show ∃ᶠ p in f,¬ dist (X i p) z < ε from not_eventually.mp h))).exists
   exact H' H

lemma pairCostC {X:ι→α→ ℂ} {B:ι→ℕ} (hB:Tendsto B L atTop)
   (H: ∀ U:ι→Ultrafilter α,(∀ i,(U i:Filter _) ≤ f) → ∃ v:ι→ℂ,
   (∀ᶠ i in L,Tendsto (X i) (U i:Filter α) (𝓝 (v i))) ∧ ∃ε:ℝ,∀ᶠ i in L, ‖v i‖ ≤ ε) :
   ∃ ε:ℝ, ∀ᶠ (p:ι× α) in L.curry f, ‖X p.1 p.2‖ ≤ ε := by
   let Q(i): Finset ℕ := Finset.filter (fun b:ℕ=> ∃ᶠ p in f,(b:ℝ) ≤ ‖X i p‖) (Finset.range (B i+1))
   have q(i):0∈Q i:= Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.zero_lt_succ _),Eventually.frequently (Eventually.of_forall fun p=>Nat.cast_zero (R:=ℝ) |>.trans_le (norm_nonneg (X i p)))⟩
   let m(i):=(Q i).max' ⟨0,q i⟩
   obtain ⟨U,hu,H'⟩:= surveyM (f:=f) (fun i p=>(m i:ℝ) ≤ ‖X i p‖)
   obtain ⟨v,px,ε,hε⟩:= H U hu
   obtain ⟨k,hk⟩:=exists_nat_gt ε
   refine ⟨k,?_⟩
   change ∀ᶠ i in L, ∀ᶠ p in f, ‖X i p‖ ≤ k
   filter_upwards [px,hε,hB.eventually_ge_atTop k] with i hv hi hp
   by_contra! h
   have hy: k∈Q i:= Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hp), h.mono (fun _ h=> h.le)⟩
   have hm: k≤ m i:= Finset.le_max' _ _ hy
   have he: ∀ᶠ p in (U i:Filter α), (m i:ℝ) ≤ ‖X i p‖ := H' i ((Finset.mem_filter.mp (show m i ∈ Q i from Finset.max'_mem ..)).2)
   exact (hi.trans_lt hk).not_ge ((show (k:ℝ) ≤ m i by exact_mod_cast hm).trans (ge_of_tendsto hv.norm he))

lemma chooseV {X:ι→Type*} [∀ i, Nonempty (X i)] {Y : ∀ i, X i→Prop} (h:∀ᶠ i in L, ∃ x,Y i x):∃ p:∀i,X i,∀ᶠ i in L,Y i (p i) := by
   let p(i):X i:= if h:∃ x,Y i x then h.choose else Classical.arbitrary (X i)
   exact ⟨p,h.mono fun i hi=> show Y i (p i) by rw [show p i=hi.choose from dif_pos hi]; exact hi.choose_spec⟩

end YM.SignedWilsonExpansion.Homes
