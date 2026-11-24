import YM.SchemeConversionRG11.FirstMS.DR.Meridian

/-! Strip identity exactly gets Taylor-local annular coefficients. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.FirstMS.DR
open Function Set Filter MSbar MSbar.Dim MSbar.Symbol MeasureTheory Metric Complex
open scoped Topology ContDiff Classical

variable {u : Set ℂ} {R : ℝ} {F : ℂ × ℝ × Patch → ℂ} (h : Window u R F) (hu : IsOpen u)
include hu h

def peel (F : ℂ × ℝ × Patch → ℂ) : ℂ × ℝ × Patch → ℂ := fun p=> Symbol.strip (fun t:ℝ=> F (p.1,t,p.2.2)) p.2.1

lemma peeled : Window u R (peel F) := by
   let L := (ContinuousLinearEquiv.prodComm ℝ Patch ℝ)
   have hw := h.AH'.arguments L.hasTemperateGrowth
   have hp := hw.rad_strip hu |>.arguments L.symm.hasTemperateGrowth
   refine ⟨hp,h.size,fun z hz a x t=>?_,fun z hz x a ha=>?_⟩
   · exact congr_fun (congr_arg Symbol.strip (funext fun k:ℝ=> show F (z,k,x,-t)= F (z,k,x,t) from h.even z hz k x t)) a
   unfold peel; rw [show (fun t:ℝ=> F (_,t,_))=0 from funext fun t=> h.ends z hz t a ha]; exact congr_fun Symbol.strip_zero _

private lemma raises (n:ℕ) : AH u (fun p:ℂ × ℝ=> layer n (fun t=> billAt p.1 (fun y => F (p.1,t,y))) p.2) := by
   have he:= h.integral hu
   have hb := (he.arguments (tame_projR (X:=ℝ))).rad_tail n hu
   exact hb.arguments (w:=fun t:ℝ=> ((0:ℝ),t)) (tame_pair (HasTemperateGrowth.const (0:ℝ)) (by fun_prop))

lemma integral_peel {z:ℂ}(hz:z∈u)(t:ℝ) : billAt z (fun y=> peel F (z,t,y)) = Symbol.strip (fun s=> billAt z (fun y=> F (z,s,y))) t := by
   let f(s:ℝ) := billAt z (fun y=> peel F (z,s,y)); let g := Symbol.strip (fun s=> billAt z (fun y=> F (z,s,y)))
   have he (s : ℝ) (hs : s≠0) : f s=g s := by
      let F' : ℂ × ℝ × Patch→ℂ := fun p=> - F (p.1,0,p.2.2)
      have ha : Window u R (fun p:ℂ × ℝ × Patch=> - F (p.1,0,p.2.2)) := by
         have hg := (h.AH'.arguments (w:=fun p : ℝ × Patch=> ((0:ℝ),p.2)) (tame_pair (HasTemperateGrowth.const _) tame_projR)).neg
         exact ⟨hg,h.size,(fun w hw q x r=> congr_arg Neg.neg (h.even _ hw 0 x r)),fun w hw _ t ht=> by rw [h.ends w hw _ t ht,neg_zero]⟩
      have hu' := peeled h hu
      apply smul_right_injective ℂ hs -- expands
      dsimp only [f,g]; rw [Symbol.roll, Complex.real_smul, ← hu'.consts s hz s]
      have hh : (fun a : Patch=> (s:ℂ)* peel F (z,s,a))=fun a=> F (z,s,a)+F' (z,s,a):= by
         funext a; rw [←Complex.real_smul]; exact (Symbol.roll (fun v=>F (z,v,a))).trans (sub_eq_add_neg ..) -- fix
      rw [hh,h.sum_bill hu ha s hz]
      dsimp only
      rw [show (fun y=> F' (z,s,y)) = fun y=> (-1:ℂ)*F (z,0,y) from funext fun y=> by simp [F'], h.consts 0 hz]; ring
   change f t=g t
   have hc : Continuous f := (((peeled h hu).integral hu).slice hz).1.continuous
   have hb : Continuous g := ((raises h hu 1).slice hz).1.continuous
   rcases eq_or_ne t 0 with rfl|hr
   · exact tendsto_nhds_unique_of_eventuallyEq (hc.continuousWithinAt (s:= Ioi 0)) hb.continuousWithinAt (mem_of_superset self_mem_nhdsWithin fun t ht=> he t (ne_of_gt ht))
   exact he t hr

lemma later (j:ℕ) : Window u R (peel^[j] F) := by
   induction j with | zero=> exact h | succ i ih=> rw [iterate_succ_apply']; exact peeled ih hu

lemma integral_layer {z:ℂ}(hz:z∈u)(t:ℝ)(j:ℕ): billAt z (fun y=> peel^[j] F (z,t,y)) = layer j (fun s=> billAt z (fun y=> F (z,s,y))) t := by
   induction j generalizing t with
   | zero=> rfl
   | succ i ih=> simp_rw [iterate_succ_apply']; rw [integral_peel (later h hu i) hu hz,Symbol.layer_next]; exact congr_fun (congr_arg Symbol.strip (funext ih)) _

omit hu h in
lemma strip_pow (g : ℝ→ℂ)(j:ℕ)(t:ℝ) : g t = (∑ k ∈ Finset.range j, (t:ℂ)^k*layer k g 0)+(t:ℂ)^j*layer j g t := by
   induction j with
   | zero=> simp
   | succ i ih=>
     rw [ih,Finset.sum_range_succ,pow_succ,layer_next,mul_assoc,← Complex.real_smul,Symbol.roll, mul_sub]; ring

end YM.SchemeConversionRG11.FirstMS.DR
