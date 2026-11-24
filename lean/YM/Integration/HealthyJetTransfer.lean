import YM.Integration.LocalizedDirectionalJets
import YM.Push.LOCAL_SPLITTING.Calculus

/-! A physical equality on a wider healthy region transports all requested local directional jets. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.HealthyJetTransfer

open Function Set Filter MeasureTheory Lattice Wilson RG
open scoped Classical Topology

variable {G : Gauge} {n : Side}

theorem margin {a b : ℝ} (hab : a < b) (P : Support n) {U : Config G n} (hU : Healthy a P U) :
    ∀ᶠ V in 𝓝 U, Healthy b P V := by
  have each (p : Face (Per n)) :
      ∀ᶠ V in 𝓝 U, Disjoint P (touched p) ∨ G.chord (faceValue V p) < b := by
    by_cases hp : Disjoint P (touched p)
    · exact Eventually.of_forall fun _ => Or.inl hp
    obtain ⟨x,hx,hp'⟩ := Finset.not_disjoint_iff.mp hp
    have hs : G.chord (faceValue U p) ≤ a := le_of_not_gt fun ha =>
      (Finset.disjoint_left.mp hU) hx ((flags_spec a U x).2 ⟨p,hp',ha⟩)
    have hc : Continuous (fun V : Config G n => G.chord (faceValue V p)) := by
      unfold faceValue
      fun_prop
    exact (hc.continuousAt.eventually (gt_mem_nhds (lt_of_le_of_lt hs hab))).mono fun _ h => Or.inr h
  filter_upwards [eventually_all.2 each] with V h
  apply Finset.disjoint_left.mpr
  intro x hx hflag
  obtain ⟨p,hp,ht⟩ := (flags_spec b V x).1 hflag
  rcases h p with h0 | h0
  · exact (Finset.disjoint_left.mp h0) hx hp
  · exact lt_asymm h0 ht

theorem frozen (P : Support n) (W : Config G n) : Continuous (LocalizedDirectionalJets.field P W) := by
  apply continuous_pi
  intro e
  by_cases he : LocalizedDirectionalJets.inside P e
  · simpa only [LocalizedDirectionalJets.field,if_pos he] using (continuous_apply e : Continuous (fun U : Config G n => U e))
  · simpa only [LocalizedDirectionalJets.field,if_neg he] using (continuous_const : Continuous (fun _ : Config G n => W e))

theorem diagonal (P : Support n) (U : Config G n) : LocalizedDirectionalJets.field P U U = U := by
  funext e
  simp [LocalizedDirectionalJets.field]

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem cylinders (q : BudgetPoint) (o : Site n) (P : Support n) (F H : Config G n → X) {b c : ℝ}
    (hb : q.threshold < b) (hl : LocalOn P F) (h : ∀ U, Healthy b P U → F U = H U)
    (paid : ∀ W : Config G n, q.supBounds o P (fun V => H (LocalizedDirectionalJets.field P W V)) c) :
    q.supBounds o P F c := by
  refine ⟨(paid 1).1,?_⟩
  intro U hU l hm hdir
  let φ := LocalizedDirectionalJets.field P U
  have ht : Tendsto φ (𝓝 U) (𝓝 U) := by
    have hφ := (frozen P U).continuousAt (x:=U)
    change Tendsto φ (𝓝 U) (𝓝 (φ U)) at hφ
    simpa only [φ,diagonal] using hφ
  have he : F =ᶠ[𝓝 U] (fun V => H (φ V)) := by
    filter_upwards [ht.eventually (margin hb P hU)] with V hV
    exact (congrFun (LocalizedDirectionalJets.restore U hl) V).symm.trans (h _ hV)
  have hi : Tendsto (increment U) (𝓝 0) (𝓝 U) := by
    have hc : Continuous (increment U) := continuous_pi fun e => by unfold increment; fun_prop
    have hu := hc.continuousAt (x:=0)
    change Tendsto (increment U) (𝓝 0) (𝓝 (increment U 0)) at hu
    simpa only [Work.G07.at_zero_increment] using hu
  rw [Push.Local.left_congr l U (he.comp_tendsto hi)]
  exact (paid U).2 U hU l hm hdir

end YM.Integration.HealthyJetTransfer
end
