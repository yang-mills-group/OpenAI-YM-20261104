import YM.MS.Landau
import YM.MS.CostVertex
import Mathlib.Analysis.Real.Pi.Bounds
/-! Engineering test value for the chosen lattice and continuum Landau symbols. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Landau
open Real Function Set Finset Plane Wire Momentum Koszul
open Complex (I)
open scoped Topology ContDiff
variable {A C ι P : Type} [Fintype A] [DecidableEq A] [DecidableEq C]

def choir (K : Flux (Atom A) (Momentum A) ℂ) (z : P→Momentum A) : Flux (Leg A C) P ℂ := fun l k p=> if l.2=k.2 then K l.1 k.1 (z p) else 0
abbrev wfield (a:Leg A C) := (dim a.1:ℤ)
variable {S : Scale ι} {a: ι → ℝ}
def cut (_:ι) := firstZone A -- lint
omit [DecidableEq A] in
lemma zone' (p : Momentum A) (hp : p ∉ firstZone A) : 1≤ ‖p‖ := by
  simp only [firstZone, Metric.mem_closedBall, dist_zero_right, not_le] at hp
  linarith [Real.pi_gt_three]

variable (h : ∀ i, 1≤ S.length i)
include h
omit [DecidableEq A] in
private lemma coatSharp {k : Momentum A→ℝ} (H : propagated S k) (b : ℕ) : Sharp S (phaseDiff S) (cut (A:=A)) (fun i p=> (coat b (S.length i) k (wave p):ℂ)) (fun i p=> (coat b (S.length i) k p:ℂ)) (fun i=> S.length i^b) := by
   obtain ⟨hs,hc,hl,hp⟩:= propagated.coatCost H b h
   exact Sharp.linear (D:=fun _=> firstZone A) (l:=fun i x=> coat b (S.length i) k (wave x)) (r:=fun i x=>coat b (S.length i) k x) ⟨hs,hl,hc,hp⟩ Complex.ofRealCLM
lemma precision_propagated (i j:A) : propagated S (precision i j) := by
   have hu : propagated S (fun p : Momentum A=> delta i j p.sq) := by
      unfold delta; split; exact propagated.summed h; exact propagated.const 0
   exact hu.sub ((propagated.comp h i).mul (propagated.comp h j))
lemma line_meter (ha : ∀ i, phaseDiff S i ≤ a i) : Meter (ι:=ι) (A:= Leg A C) wfield a S
    (fun i=> choir (line (S.length i)) wave) (fun i=> choir (line (S.length i)) id) cut 4 := by
   intro x y
   let w := (fun i=>S.length i ^ ((4:ℤ)-wfield x-wfield y))
   let h0 (s t : Leg A C) := Sharp.zero (G:=ℂ) (E:=Momentum A) (a:=phaseDiff S) (S:=S) (D:=cut) (fun i=> zpow_nonneg (S.pos i).le (4-wfield s-wfield t)) fun i=> (pd_pos i).le
   let K := (ContinuousLinearMap.mul ℝ ℂ) I
   have hz (e:A) := Sharp.linear (coatSharp (S:=S) h ((propagated.summed h).mul (propagated.comp h e)) 1) K
   refine Sharp.up (a:=phaseDiff S) ?_ ha
   unfold choir; dsimp only; split
   · rcases x with ⟨⟨_|k,_|_⟩,s⟩ <;> rcases y with ⟨⟨_|j,_|_⟩,u⟩ <;>
        first | exact h0 _ _ | skip
     · convert hz j using 1 <;> rfl
     · convert coatSharp h (precision_propagated h k j) 2 using 1 <;> rfl
     · convert hz k using 1 <;> rfl
   exact h0 _ _
lemma lap_meter (ha : ∀ i, phaseDiff S i ≤ a i) : Meter (ι:=ι) (A:= Leg A C) wfield a S
    (fun i=> choir (laplace (low (S.length i))) wave) (fun i=> choir (laplace (low (S.length i))) id) cut 3 := by
   intro x y
   let v : ℂ→L[ℝ] ℂ:= (ContinuousLinearMap.mul ℝ ℂ).flip (2:ℂ)⁻¹
   have ht := coatSharp (A:=A) h ((propagated.const 1).add (propagated.summed h)) 0
   have hi (s t : Leg A C) := Sharp.zero (G:=ℂ) (E:=Momentum A) (a:=phaseDiff S) (S:=S) (D:=cut) (fun i=> zpow_nonneg (S.pos i).le (3-wfield s-wfield t)) fun i=>(pd_pos i).le
   refine Sharp.up (a:=phaseDiff S) ?_ ha
   unfold choir; dsimp only; split
   · rcases x with ⟨⟨_|k,_|_⟩,s⟩ <;> rcases y with ⟨⟨_|j,_|_⟩,u⟩ <;> first | exact hi _ _ | dsimp only [laplace,delta]
     · convert ht.linear (-v) using 1 <;> norm_num [wfield,dim,v,low,div_eq_mul_inv] <;> (ext; ring)
     · convert ht.linear (-v) using 1 <;> norm_num [wfield,dim,v,low,div_eq_mul_inv] <;> (ext; ring)
     all_goals split
     all_goals first | (simp only [Complex.ofReal_zero, zero_div]; exact hi _ _) | (simp_rw [div_eq_mul_inv]; convert! ht.linear v using 1)
   exact hi _ _
end YM.MS.Landau
