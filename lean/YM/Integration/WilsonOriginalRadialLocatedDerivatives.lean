import YM.Integration.WilsonOriginalRadialBoard

/-! The original normalized conditional on a cropped exponential chart. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalRadialLocatedDerivatives
open Function Finset Filter Set Lattice RG Wilson Next.Foundations Push.Local
open Planned.AtomRegular WardBin.Lies RG01.Kernel Labels WilsonCapturedPrimaryAngles
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge} {n:Side}
private def seat (f:Config G n→ℂ) (B:BudgetPoint) (o:Site n) (J:Finset (Link n)) (V:Config G n) :=
  (f ∘ increment V) ∘ limitAmp B o J

private theorem seated (f:Config G n→ℂ) (B:BudgetPoint) (o:Site n) (J:Finset (Link n)) (V:Config G n)
    {k:ℕ} (sf:Germ k f V) : ContDiffAt ℝ k (seat f B o J V) 0 := by
  unfold seat
  have h:ContDiffAt ℝ k (f ∘ increment V) ((limitAmp B o J) 0):=by
    rw [map_zero]
    exact sf
  exact h.comp 0 (limitAmp (G:=G) B o J).contDiff.contDiffAt

private theorem slot (f:Config G n→ℂ) (B:BudgetPoint) (o:Site n) (J:Finset (Link n)) (V:Config G n)
    {k:ℕ} {C:ℝ} (sf:Germ k f V) (cp:0≤C)
    (cap:∀ l:List (Directions G n),l.length=k →
      (∀v∈l,B.dirBound o v ∧ ∀e∉J,v e=0) → ‖leftDerivs f l V‖ ≤ C):
    ‖iteratedFDeriv ℝ k (seat f B o J V) 0‖ ≤ polarCost k*C := by
  have smooth:=seated f B o J V sf
  refine op_polar (Analysis.sym_Jet smooth) cp (fun x hx=>?_)
  let v:=limitAmp B o J x
  have hv : (fun s:ℝ=>seat f B o J V (s • x))=fun s:ℝ=>f (increment V (s • v)) := by
    ext1 s
    exact congr_arg (f ∘ increment V) (map_smul ..)
  rw [←iteratedDeriv_on_line smooth x,hv,←leftDerivs_diag,zero_smul,Work.G07.at_zero_increment]
  apply cap _ (List.length_replicate ..)
  intro a ha
  rw [(List.mem_replicate.mp ha).2]
  refine ⟨fun e=>?_,fun e he=>limit_miss he x⟩
  by_cases h:e∈J
  · simpa only [v,limit_hit h,amp_apply] using (amp_fits B o).mpr hx e
  · rw [show v e=0 from limit_miss h x,norm_zero]
    exact (weight_pos B o e).le

private theorem agreement (B:BudgetPoint) (o:Site n) (J:Finset (Link n)) (v u:Directions G n):
    amp B o (chain B o J v u)=limitAmp B o J (chain B o J v u):=by
  funext e
  by_cases he:e∈J
  · simp [amp_apply,he]
  · simp [amp_apply,he,chain,suppress_apply]

theorem chart (f:Config G n→ℂ) (B:BudgetPoint) (o:Site n) (J:Finset (Link n)) (w:Directions G n)
    {k:ℕ} {C:ℝ} (cp:0≤C) (sf:Germ k f (bone B o J w))
    (cap:∀l:List (Directions G n),l.length≤k →
      (∀v∈l,B.dirBound o v ∧ ∀e∉J,v e=0) → ‖leftDerivs f l (bone B o J w)‖≤C)
    (hx:∀i∈J,‖limitAmp B o J w i‖≤1) (hw:∀i∈J,weight B o i≤1):
    ContDiffAt ℝ k (f ∘ bone B o J) w ∧
    ∀i≤k,‖iteratedFDeriv ℝ i (f ∘ bone B o J) w‖≤baseCost G k*C := by
  let L:=chain B o J w
  let H:=seat f B o J (bone B o J w)
  have ht:=chain_cost k hx hw
  have hd:ContDiffAt ℝ k L w:=ht.analytic.of_le le_top
  have he:ContDiffAt ℝ k H (L w):=by
    unfold L H
    rw [chain_zero]
    exact seated f B o J _ sf
  have hu:f ∘ bone B o J =ᶠ[𝓝 w] H ∘ L:=by
    filter_upwards [linked (B:=B) (o:=o) (J:=J) (w:=w)] with u gu
    simpa only [L,H,seat,Function.comp_apply,agreement] using congrArg f gu
  refine ⟨(he.comp w hd).congr_of_eventuallyEq hu,fun i hi=>?_⟩
  have bound j (hj:j≤k):‖iteratedFDeriv ℝ j H (L w)‖≤diagonals k*C:=by
    unfold H L
    rw [chain_zero]
    apply (slot f B o J _ (sf.of_le (Nat.cast_le.mpr hj)) cp (fun l eq fits=>cap l (eq.trans_le hj) fits)).trans
    exact mul_le_mul_of_nonneg_right (diagonals_le hj) cp
  rw [(hu.iteratedFDeriv (𝕜:=ℝ) i).eq_of_nhds]
  exact (nest_bound hd he hi (mul_nonneg (diagonals_nonneg _) cp) (relay_one ..)
    (fun j _ hj=>ht.norm_le j hj) bound).trans_eq (by unfold baseCost;ring)

end YM.Integration.WilsonOriginalRadialLocatedDerivatives
