import YM.Planned.RECIPE_STARTUP_PORT.Layout
import YM.Planned.RECIPE_STARTUP_PORT.Horizon
import Mathlib.Analysis.Complex.Liouville
/-!
# Actual startup analyticity (no tuning established by this lemma)

Address set `drawer` independent of β and of the horizon length at fixed
level/period. Analytic bounds in the absolute per-anchor prices on the entry
values, also each priced regular field derivative. Forced hard lookup operates
only on fixed real fields. This is not analyticity of masks in those fields.
-!
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.TopOrbit
open Function Set RG Wilson Precision Lattice Filter
open Ovens Ovens.Pipes WilsonStartup WilsonStartup.Start RG.Shoot Progress.DirectedRecipe Progress.DirectedRecipe.Rack
open scoped Matrix.Norms.Frobenius Topology BigOperators Classical ContDiff
variable {G:Gauge} {a:Levels G} {Horizon':Horizon a} {O:ChartRatio G} (K:Kin Horizon' O) (N p:ℕ) (q s:BudgetPoint)
-- remove q s; implicit
local notation "n" => a.S.side N p
local notation "P" => a.budget N

abbrev startup (β:ℝ) := fromTop K N p β (Planned.Port.pot a N p) (Planned.Port.kettle a N p β)

lemma permits (h : ∀ N,K.path N N=Design.top G (a.params N).clip) (hr : Start.Allows a N) (β : ℝ) (hb : β∈Shoot.band a N) : ((startup K N p β).activities.Valid P (a.clock.allowance N) (a.clock.forcedAllowance N)) := by
  let X:= Planned.Port.stamped a (permissions a)
  have hh := (Planned.Port.card (p:=p) hr (permissions a) h).law β hb
  exact hh.ingredients.gates ..

-- Global addresses on OUTPUT even. Widening tucks. `written` is linear; exponent terms may vanish exactly everywhere.
lemma startup_reg_spin (i : ℕ) (β : ℝ) : (startup K N p β).activities.E i = β • ((startup K N p 1).activities.E i) := by
  change stuff (upE (dictionary G n)) (payload (a.params N).clip P G n β).regular i = β • stuff (upE (dictionary G n)) (payload (a.params N).clip P G n 1).regular i
  set X:=dictionary G n
  by_cases hh : i ∈ range (upE X)
  · obtain ⟨j,rfl⟩:=hh
    rw [stuffed,stuffed]; change (payload _ _ G n β).regular j = _
    dsimp only [payload]; split_ifs
    · unfold written
      cases hv : Padded.name (Sheet n) j
      · change (β*share*_) • _ = β • ((1*share*_) • _); rw [one_mul,mul_assoc,smul_smul]
      apply Eq.symm; exact smul_zero _
    change _ = β • (0:Config G n→ℝ); rw [smul_zero]
  rw [blank _ _ hh,blank _ _ hh,smul_zero]

def ep (f : ℝ→ℝ) := (f=fun _=>0) ∨ ∃ t:ℝ,f=fun w=> Real.exp (t*w) -- remove alpha

private lemma ep_mul {f g:ℝ→ℝ} (hf : ep f) (hg : ep g) : ep (f*g) := by
  rcases hf with rfl|⟨w,rfl⟩ <;> rcases hg with rfl|⟨z,rfl⟩
  · left; ext1 x; change (0:ℝ)*0=0; simp
  · left; ext1 x; change (0:ℝ)*_=0; simp
  · left; ext1 x; change _*(0:ℝ)=0; simp
  exact Or.inr ⟨w+z,funext fun x=> by dsimp; rw [←Real.exp_add,add_mul]⟩

set_option maxHeartbeats 800000 in
lemma startup_kernel_spin (i : ℕ) (U : Config G n):
    ep (fun β =>(startup K N p β).activities.K i U) := by
  change ep fun β=> solid (folio G n) P (widen (dictionary G n) (payload (a.params N).clip P G n β)) i U
  by_cases ht : (addr (folio G n) P i).eligible (a.budget N).threshold U
  · dsimp only [solid]; simp only [if_pos ht]
    suffices ∀ v : Finset Ovens.Label, ep (fun β=> ∏ j ∈ v,Pipes.reach (widen (dictionary G n) (payload (a.params N).clip P G n β)) j U) by apply this
    intro v
    have hh(j) : ep (fun β=>Pipes.reach (widen (dictionary G n) (payload (a.params N).clip P G n β)) j U) := by
         set X := dictionary G n
         rcases j with j|j
         · by_cases he : j ∈ range (upK X)
           · obtain ⟨k,rfl⟩:=he
             simp only [widen,Pipes.reach,payload,Sum.elim_inl,stuffed]; split_ifs
             · unfold paid; split_ifs
               · right; exact ⟨-charge (a.params N).clip (a.budget N) _ U,funext fun _=>by congr 1; ring⟩
               all_goals exact Or.inl rfl
             all_goals exact Or.inl rfl
           exact Or.inl (funext fun β=> by simp only [Pipes.reach,widen,Sum.elim_inl,blank _ _ he,Pi.zero_apply])
         · left;ext1 β
           simp only [Pipes.reach,payload,widen,Sum.elim_inr]; change Real.exp ((stuff (upS X) (fun _=> (0:Config G n→ℝ)) j) U)-1=0
           by_cases he : j ∈ range (upS X)
           · obtain ⟨k,rfl⟩:=he; rw [stuffed]; simp
           rw [blank _ _ he]; simp
    induction v using Finset.induction_on with
    | empty => simp only [Finset.prod_empty]; exact Or.inr ⟨0,funext fun _=>by simp⟩
    | insert i s hi ih =>
      simp only [Finset.prod_insert hi]; exact ep_mul (hh i) ih
  left; funext β; exact if_neg ht

end YM.UVExt.TopOrbit
