import YM.MSbar.Sage.Cross
import YM.UVNext.PRICED_KERNELS.Trees
import YM.Next.FREE_KERNELS.Traffic
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.MinBranches
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Reach
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath
open Lattice Wilson RG Function Filter MeasureTheory Push.Local Push Push.AbsoluteSums
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{c f:Side}(S:StepData c f){U V U' V':Config G f}{R:PathData G}{σ C T a v δ w β:ℝ}
open Finset RG.PathData Patch Pressure
variable {Y X: Support f}{k M:ℕ}{p:BudgetPoint}{d:Clip}
open Next.Scheduling Precision ConnectedActivityE6 Next.Fluctuations
set_option quotPrecheck false
local notation "v!"=> S.ratio
local notation "p!" => predReach S.patch+1
def necklace (P: Patch) := P.L.val*(predReach P+3)
omit S in
lemma closeB (S:StepData c f) {i:Site c} {b:Edge (Site f)} (hp : separation i (S.ratio.parent b.1) ≤ predReach S.patch+1) :
    b.1∈ halo (necklace S.patch) {S.ratio.embed i} ∧ b.1+step b.2∈ halo (necklace S.patch) {S.ratio.embed i}:=by
    let L:=S.patch.L; have hh: separation (S.ratio.embed i) b.1≤ necklace S.patch-1:=by
       have hv:= (Next.Free.scaled_root S.ratio i (S.ratio.parent b.1)).trans (Nat.mul_le_mul_left S.ratio.count.val hp)
       have hk:separation (S.ratio.embed (S.ratio.parent b.1)) b.1≤ L.val:=by rw [separation_comm]; exact_mod_cast UVNext.PricedKernels.embed_parent S.ratio b.1
       refine (separation_triangle _ (S.ratio.embed (S.ratio.parent b.1)) _).trans ((Nat.add_le_add hv hk).trans ?_); unfold necklace; have hl : 1 ≤ S.patch.L.val:=S.patch.L.property; change L.val*(predReach S.patch+1)+ L.val ≤ L.val*(predReach S.patch+3)-1; unfold L; simp only [Nat.mul_add,mul_one]; omega
    have hx:1 ≤ necklace S.patch:= by unfold necklace; exact Nat.mul_pos S.patch.L.property (by omega)
    exact ⟨halo_spec.mpr ⟨_,mem_singleton_self _,hh.trans (Nat.sub_le ..)⟩,halo_spec.mpr ⟨_,mem_singleton_self _,(separation_triangle _ b.1 _).trans ((Nat.add_le_add hh (Work.E01.sep_step_le ..)).trans (by omega))⟩⟩
private lemma agreesN (j:Site c)(U V:Config G f) (he:Agrees (halo (necklace S.patch) {S.ratio.embed j}) U V) : AgreeNear S.ratio.parent j (predReach S.patch+1) U V := fun i hp=>he i (closeB S hp).1 (closeB S hp).2
-- For rating-only analytic.Stimulus noise ratio.Jetra
variable (hd : S.patch.Branches S.kernel G)

structure Trail (S:StepData c f) (Y : Support f) (M : ℕ)(U U' V V':Config G f): Prop where
    from_old: Spine Y U V
    renewed: Spine Y U' V'
    approves : Agrees (halo (2*M) Y) U U'
    afterR : Agrees (halo (2*M) Y) V V'
-- free right angle
lemma toward (Q:Config G c)(x:Config G f)(t:S.Choices) : S.noise β (S.prediction x t) Q=(S.penaltyZ β G)⁻¹ ^ Fintype.card (Edge (Site c))*Real.exp (-β*noiseTaylor S Q x t):=by unfold StepData.noise StepData.penaltyWeight noiseTaylor; rw [← mul_assoc, Finset.mul_sum, prod_mul_distrib,prod_const,card_univ, Real.exp_sum]
variable (ht: necklace S.patch ≤ M)(hp: Trail S Y M U U' V V')
include hp ht hd
lemma pillarP (j:Site c) : (AgreeNear S.ratio.parent j (p!) U U' ∧ AgreeNear S.ratio.parent j (p!) V V') ∨ (AgreeNear S.ratio.parent j (p!) U V ∧ AgreeNear S.ratio.parent j (p!) U' V'):=by
    let i:= S.ratio.embed j; let X:= halo (necklace S.patch) {i}; by_cases hz : Disjoint X Y
    · exact Or.inr ⟨agreesN S _ _ _ (hp.from_old _ hz),agreesN S _ _ _ (hp.renewed _ hz)⟩
    obtain ⟨x,hx,hY⟩:= Finset.not_disjoint_iff.mp hz; have he(t:Site f)(htx:t∈X):separation i t≤M:=by obtain ⟨b,hb,H⟩:= halo_spec.mp htx; exact (mem_singleton.mp hb ▸ H).trans ht
    have hi :X⊆ halo (2*M) Y:= seep (halo_spec.mpr ⟨x,hY,(separation_comm x i).trans_le (he x hx)⟩) he
    exact Or.inl ⟨agreesN S _ _ _ (agrees_mono hp.approves (coe_subset.mpr hi)),agreesN S _ _ _ (agrees_mono hp.afterR (coe_subset.mpr hi))⟩
def uniformed (S:StepData c f)(U:Config G f) := ∀ i:S.Choices,(∀ j,Tags.siteMass U i j=1) ∧ ∀ j,Tags.pinMass U i j=1
lemma liked (hf:uniformed S U')(hg:uniformed S V') (i:S.Choices) : S.likelihood U i = S.likelihood V i:=by
    unfold StepData.likelihood; apply congr_arg₂ (·*·) <;> apply prod_congr rfl <;> intro j _
    · have hv: Tags.siteMass U i j=Tags.siteMass V i j:= by
          rcases pillarP S hd ht hp j with ⟨h₀,h₁⟩ |⟨h₀,h₁⟩; exact ((Emblems.frames_agree U U' j i i hd rfl (h₀.shrink (by simp))).2.trans ((hf i).1 j)).trans ((Emblems.frames_agree V V' j i i hd rfl (h₁.shrink (by simp))).2.trans ((hg i).1 j)).symm; exact (Emblems.frames_agree _ _ _ _ _ hd rfl (h₀.shrink (by simp))).2
      refine mul_left_cancel₀ (show (Fintype.card S.patch.FrameTag:ℝ)≠0 by positivity) hv
    have hv : Tags.pinMass U i j=Tags.pinMass V i j:=by
       rcases pillarP S hd ht hp j.1 with ⟨h₀,h₁⟩|⟨h₀,h₁⟩; exact ((Emblems.choices U U' j i i hd rfl rfl rfl h₀).2.1.trans ((hf i).2 j)).trans ((Emblems.choices V V' j i i hd rfl rfl rfl h₁).2.1.trans ((hg i).2 j)).symm; exact (Emblems.choices _ _ _ _ _ hd rfl rfl rfl h₀).2.1
    exact mul_left_cancel₀ (show (Fintype.card S.patch.Points:ℝ)≠0 by positivity) hv
lemma payday (Q:Config G c)(hf:uniformed S U')(hg:uniformed S V')(i:S.Choices)(he:∀ j:S.Choices, noiseTaylor S Q U' i-noiseTaylor S Q V' i=noiseTaylor S Q U' j-noiseTaylor S Q V' j) :
    S.density β U Q=S.density β V Q * Real.exp (-β*(noiseTaylor S Q U' i-noiseTaylor S Q V' i)):=by
    unfold StepData.density; rw [sum_mul]; apply sum_congr rfl; intro j _; rw [liked S hd ht hp hf hg,he j]
    have hr: noiseTaylor S Q U j-noiseTaylor S Q V j=noiseTaylor S Q U' j-noiseTaylor S Q V' j:=by
       unfold noiseTaylor; rw [← mul_sub,← mul_sub,← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]; apply congr_arg; apply sum_congr rfl; intro b hb; rcases pillarP S hd ht hp b.1 with ⟨h₀,h₁⟩ |⟨h₀,h₁⟩
       · rw [(Emblems.choices U U' b j j hd rfl rfl rfl h₀).2.2,(Emblems.choices V V' b j j hd rfl rfl rfl h₁).2.2]
       rw [(Emblems.choices U V b j j hd rfl rfl rfl h₀).2.2,(Emblems.choices U' V' b j j hd rfl rfl rfl h₁).2.2,sub_self,sub_self]
    rw [←hr,toward,toward,mul_assoc (S.likelihood ..),mul_assoc (_⁻¹^_), ← Real.exp_add,show _+_=-β*noiseTaylor S Q U j by ring]
end YM.MSbar.Heath
