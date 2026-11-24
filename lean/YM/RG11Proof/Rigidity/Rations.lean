import YM.RG11Proof.Rigidity.Pig

/-!
# Clear a common position denominator on harmonics (all still Euclidean)
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity
open Tensor Analysis Maxwell Maxwell.Free Extra.FD.SphereTest Filter Set
open scoped BigOperators Topology ContDiff Classical

/-- A (real-)analytic harmonic on the domain, with a cross-multiply extension
by global analytic functions. There is no claim to solve a general Dirichlet
problem; each one-slot Wick reading here has this stronger property. -/
structure Ghost (U : Set E4) (f : E4 → ℝ) : Prop where
  thin (x : E4) (hx : x∈ U) : ContDiffAt ℝ ω f x
  light (x : E4) (hx : x∈ U) : lap f x = 0
  silk : ∃ p q : E4 → ℝ, ContDiff ℝ ω p ∧ ContDiff ℝ ω q ∧ ∀ x∈ U, q x ≠ 0 ∧ q x * f x = p x

namespace Ghost
variable {U V : Set E4} {f g : E4 → ℝ}

lemma mono (A : Ghost U f) (h : V ⊆ U) : Ghost V f where
  thin x H := A.thin x (h H)
  light x H := A.light x (h H)
  silk := by obtain ⟨p,q,ha,hb,hh⟩:=A.silk; exact ⟨p,q,ha,hb,fun x hx=> hh x (h hx)⟩

lemma swap (A : Ghost U f) (hU : IsOpen U) (h : EqOn g f U) : Ghost U g where
  thin x H := (A.thin x H).congr_of_eventuallyEq (h.eventuallyEq_of_mem (hU.mem_nhds H))
  light x H := (lap_local (h.eventuallyEq_of_mem (hU.mem_nhds H))).trans (A.light x H)
  silk := by obtain ⟨p,q,ha,hb,hh⟩:=A.silk; exact ⟨p,q,ha,hb,fun x hx=> h hx ▸ hh x hx⟩

lemma addG (A : Ghost U f) (B : Ghost U g) : Ghost U (fun x=> f x+g x) where
  thin x H := (A.thin x H).add (B.thin x H)
  light x H := (lap_add (A.thin x H) (B.thin x H)).trans (by rw [A.light x H,B.light x H,add_zero])
  silk := by
    obtain ⟨p,q,ha,hb,hh⟩:=A.silk
    obtain ⟨r,s,ht,hS,hk⟩:=B.silk
    exact ⟨fun x=>p x*s x+q x*r x,fun x=>q x*s x,(ha.mul hS).add (hb.mul ht),hb.mul hS,fun x hx=>
      ⟨mul_ne_zero (hh x hx).1 (hk x hx).1,by dsimp only; rw [← (hh x hx).2,← (hk x hx).2];ring⟩⟩

lemma mulG (A : Ghost U f) (c : ℝ) : Ghost U (fun x=>f x*c) where
  thin x H := (A.thin x H).mul contDiffAt_const
  light x H := by
    let L := ContinuousLinearMap.lsmul ℝ (E:=ℝ) ℝ c
    rw [show (fun x=>f x*c)=L ∘ f from funext fun x=>mul_comm _ _,Maxwell.Free.lap_linear L (A.thin x H),A.light x H,map_zero]
  silk := by
    obtain ⟨p,q,ha,hb,hh⟩:=A.silk; exact ⟨fun x=>p x*c,q, ha.mul contDiff_const,hb,fun x hx=>
      ⟨(hh x hx).1,(mul_assoc _ _ _).symm.trans (congr_arg (· * c) (hh x hx).2)⟩⟩

lemma zeroG : Ghost U (fun _=>0) :=
  ⟨fun _ _=>contDiffAt_const,fun _ _=>congr_fun Maxwell.Free.lap_zero _,⟨fun _=>0,fun _=>1,contDiff_const,contDiff_const,by simp⟩⟩

lemma sumG {I : Type*} (s : Finset I) (t : I → E4 → ℝ) (h : ∀ i∈s, Ghost U (t i)) :
    Ghost U (fun x=>∑ i∈s,t i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zeroG (U:=U))
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (h _ (Finset.mem_insert_self ..)).addG (ih (fun i hi=>h i (Finset.mem_insert_of_mem hi)))

lemma gone (A : Ghost U f) (hU : U∈𝓝 (0:E4)) (T : E4 → ℝ) (hT : ContDiffAt ℝ ∞ T 0)
    (he : f =ᶠ[𝓝 0] qRad • T) : EqOn f 0 U := by
  have hL : Extra.FD.lap f =ᶠ[𝓝 0] 0 := eventually_of_mem hU fun x hx=> A.light x hx
  have hh := dividesToZero (A.thin 0 (mem_of_mem_nhds hU)) hT he hL
  obtain ⟨p,q,ha,hb,h⟩ := A.silk
  have hp : p =ᶠ[𝓝 (0:E4)] 0 := by
    filter_upwards [hU,hh] with x hx hL; rw [← (h x hx).2, hL]; exact mul_zero _
  have hm := AnalyticOnNhd.eq_of_eventuallyEq (𝕜:=ℝ) ha.analyticOnNhd (fun _ _ => analyticAt_const) hp
  intro x hx
  exact (mul_eq_zero.mp ((h x hx).2.trans (congr_fun hm x))).resolve_left (h x hx).1
end Ghost

variable {G : Gauge}

-- Move just the external endpoint (probe degree zero, any other degree at the
-- primary, no derivatives requested at a collision). Includes `lap` in the
-- ACTUAL offset variable.
lemma drifting {j k : ℕ} (a : Maxwell.Probe G j) (b : Maxwell.Probe G k) (w : E4) :
    Ghost {x : E4| x ≠ w} (fun x=> legKernel a b (x-w)) := by
  let h:= kernel_pole a b
  let f := legKernel a b
  refine ⟨fun x hx=> ?_,fun x hx=> ?_,?_⟩
  · exact (h.diff (x-w) (show x-w∈ away from sub_ne_zero.mpr hx)).comp x (contDiffAt_id.sub contDiffAt_const)
  · have he (i : Axis) (f : E4 → ℝ) : grad i (fun x=> f (x-w)) = fun x=> grad i f (x-w) := by
      funext x
      simp only [grad,D]; rw [show (fun x=> f (x-w)) =  (fun x=> f (x+(-w))) from funext fun y=> by simp [sub_eq_add_neg], fderiv_comp_add_right]
      simp [sub_eq_add_neg]
    simp_rw [lap,he]; exact h.Laplace (show x-w∈ away from sub_ne_zero.mpr hx)
  obtain ⟨p,ht,hp⟩:= h.precise
  let g := fun x : E4=> x-w
  have hg : ContDiff ℝ ω g := contDiff_id.sub contDiff_const
  exact ⟨p ∘ g, rad (4+j+k-1) ∘ g, ht.comp hg,(rad_diff _).comp hg,fun x hx=>
    ⟨by have ht := norm_pos_iff.mpr (show x-w≠0 from sub_ne_zero.mpr hx); dsimp only [rad,g,Function.comp_apply]; positivity,hp _ (sub_ne_zero.mpr hx)⟩⟩

lemma ghost_line (z : E4) (i : Foil) (c : G.ColorIndex) (t : Pig G) :
    Ghost {x : E4| z+x≠ t.origin} (fun x=> line (toss i (z+x) c) t) := by
  have hu : IsOpen {x : E4|z+x≠ t.origin} := by exact isOpen_ne_fun (continuous_const.add continuous_id) continuous_const
  let a := flavor 0 c (cell i.1 i.2)
  let b := t.dart.flip.2
  have hm := (drifting a b (t.origin-z)).mono (V:={x:E4|z+x≠ t.origin}) (by
    intro x hx he
    exact hx (show z+x=t.origin from by rw [show x=t.origin-z from he]; abel))
  apply hm.swap hu
  intro x hx; dsimp only; rw [show line (toss i (z+x) c) t=legKernel a b (z+x-t.origin) from if_neg hx,show z+x-t.origin=x-(t.origin-z) by abel]

end YM.RG11.Rigidity
