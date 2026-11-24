import YM.Comparison.RG02.Affinity.Reach
import YM.Comparison.RG02.Laplace.Prism
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Affinity
open Function Filter Finset MeasureTheory
open YM.Marker YM.Multi Order Assembly Actual YM.Lattice YM.Tree
open YM.Precision YM.Next.SectorChange
open Matrix
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff ENNReal
variable {G : Gauge} {V : Type} [DecidableEq V] {R : Census V}
variable {I : Type} [Fintype I] [DecidableEq I]
local notation "Λ" => I→ℝ
open Gaussian PertExtension.Series PertExtension.Series.Tested Laplace.Prism Laplace
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
local notation "E"=>House X I
namespace Door
variable (x : X) (S : Vibe X I) (g ε : ℝ)

def circle : Set (I→ℝ) := Metric.closedBall (0:E) ε |> fun A=> (fun v:I→ℝ=> g • (season x v)) ⁻¹' A
omit [DecidableEq I] in
lemma circle_spec (v : Λ): v∈circle (I:=I) x g ε ↔ ‖g • (season x v)‖≤ ε := by unfold circle; rw [Set.mem_preimage]; simp
omit [DecidableEq I] in
lemma closed_circle : IsClosed (circle (I:=I) x g ε) := IsClosed.preimage ((season_cont x).const_smul g) Metric.isClosed_closedBall
omit [DecidableEq I] in
lemma compact_circle (hg : 0<g) : IsCompact (circle (I:=I) x g ε) := by
   apply IsCompact.of_isClosed_subset (ProperSpace.isCompact_closedBall (α:=Λ) 0 (ε/g)) (closed_circle ..)
   intro v hv; have he:‖g • v‖≤ε := by
     have hh : ‖(g • (season x v)).2.2‖ ≤ ‖g • (season x v)‖ := (norm_snd_le ..).trans (norm_snd_le ..)
     have hx := hh.trans ((circle_spec ..).mp hv)
     rw [facing] at hx; exact hx
   rw [Metric.mem_closedBall, dist_zero_right, le_div_iff₀ hg]; rwa [norm_smul,Real.norm_of_nonneg hg.le,mul_comm g] at he
local notation "♩" => ((1,x,0):House X I)
local notation "L"=> reach (I:=I) X
omit [DecidableEq I] in
lemma finances (v : Λ) (hg : 0<g) : g*Prism.size ♩ L v=g+‖g • season x v‖ := by
  change g*(1+_)=_
  rw [mul_add,mul_one,norm_smul,Real.norm_of_nonneg hg.le]; rfl
variable {g}
omit [DecidableEq I] in
lemma root_circle (hp : 0<ε) : Major ♩ L (fun g=> circle x g ε) := by
   refine ⟨ε,hp,eventually_pos.mono fun g hg v hv=>?_⟩
   rw [finances x g v hg]; exact le_add_of_nonneg_of_le hg.le (not_le.mp (mt (circle_spec ..).2 hv)).le
omit [DecidableEq I] in
lemma cap_circle (δ : ℝ) (he : ε < δ) : Prism.Fits ♩ L δ (fun g=> circle x g ε) := by
   filter_upwards [Tested.eventually_small (sub_pos.mpr he)] with g hg v hv
   rw [finances x g v hg.1]; linarith [(circle_spec ..).mp hv,hg.2]

-- lifted window. Note no claim about C.Makes budgets in any of this.
def pull (g : ℝ) := Vibe.outreach x S g ⁻¹' circle x g ε
lemma qualifies : ∀ᶠ g in along, 0 < (Vibe.basis x S g).det := by
    let f := fun u:ℝ×X=> (S.B u).det
    have he : ContinuousAt f 0 := (YM.Push.Loops.det_contDiff.contDiffAt.comp 0 S.smooth).continuousAt
    have hv : Tendsto (fun g:ℝ=> (g,g • x)) along (𝓝 0) := by
       rw [show (0:ℝ×X)=((0:ℝ), (0:ℝ) • x) from Prod.ext rfl (zero_smul ℝ x).symm]; exact (((show Continuous (fun g:ℝ=> (g,g • x)) by fun_prop).tendsto 0).mono_left nhdsWithin_le_nhds)
    have hT := (he.tendsto.comp hv)
    exact hT.eventually (lt_mem_nhds (by unfold f; rw [S.identity,Matrix.det_one]; simp))
private lemma cash (g:ℝ) (hg:0<g) (v:I→ℝ): v∈pull x S ε g ↔ ‖S.effect (g • season x v)‖ ≤ ε := by rw [pull,Set.mem_preimage,circle_spec,Vibe.emblem x S v hg.ne']
lemma pays (hp : 0<ε): Major ♩ L (pull x S ε) := by
    have hV : ∀ᶠ v:E in 𝓝 0, ‖S.effect v‖ < ε := (S.no_jets.2.continuousAt.norm).eventually (gt_mem_nhds (by dsimp only; rw [S.base,norm_zero]; exact hp))
    obtain ⟨e,he,h⟩:= Metric.eventually_nhds_iff.mp hV
    refine ⟨e,he,eventually_pos.mono fun g hg v hv=>?_⟩
    rw [finances x g v hg]; by_contra! hx
    exact hv ((cash x S ε g hg v).2 (h (y:=g • season x v) (by rw [dist_zero_right]; linarith)).le)

lemma pull_cap {δ:ℝ} (he:0<δ): ∃ h:ℝ, 0<h ∧ ∀ ε,ε≤h → Prism.Fits ♩ L δ (pull x S ε) := by
    have hv : ∀ᶠ v:E in 𝓝 0, ‖S.reverse v‖ < δ/2 := S.continuous_back.continuousAt.norm.eventually (gt_mem_nhds (by dsimp only; rw [S.back,norm_zero]; exact half_pos he))
    obtain ⟨h,h0,H⟩:= Metric.eventually_nhds_iff.mp hv
    refine ⟨h/2,half_pos h0,fun ε he'=>?_⟩
    filter_upwards [qualifies x S,Tested.eventually_small (half_pos he)] with a ht ha v hb
    have hi := ha.1
    let u:= a • season x v
    have hp := H (y:=S.effect u) (by rw [dist_zero_right]; exact ( ((cash x S ε a hi v).1 hb).trans he').trans_lt (half_lt_self h0))
    have hw : (S.B (u.1,u.2.1)).det = (Vibe.basis x S a).det := by
       have hr:u=(a,a • x,a • v):=by unfold u; rw [facing]; exact Prod.ext (mul_one a) rfl
       rw [hr]; rfl
    rw [Vibe.resets _ _ (isUnit_iff_ne_zero.mpr (hw ▸ ht.ne'))] at hp
    rw [finances x a v hi]; exact le_of_lt ((add_lt_add ha.2 hp).trans_eq (add_halves δ))
end Door
end YM.Comparison.RG02.Affinity
