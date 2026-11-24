import YM.OPE.Compatible.Spa.CO
/-!
# Radical complement engineering. τ-all phases. Finite exposed algebra.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Set Function
open scoped Topology BigOperators Classical
-- Turns.K generic prism ν
variable {E F Z M:Type}[AddCommGroup E][Module ℝ E][AddCommGroup F][Module ℝ F][AddCommGroup Z][Module ℝ Z]
variable {π:E→ₗ[ℝ] F}{σ:E→ₗ[ℝ] E}{f:E≃ₗ[ℝ] Jewel F}{U W:Submodule ℝ F}{Y:Submodule ℝ E}
variable (H:Flank f σ U W Y)(he:Horb π σ f)
lemma splicing (H:Flank f σ U W Y)(he:Horb π σ f)(x:E) :∃ c:Jewel W,x-marchL f W c∈Y:=by
      have hu (j:ℕ)(hj:j≤3)(x:E)(hp:∀ i:Fin 3,i.val <j→ f x i=0) :∃ c:Jewel W,x-marchL f W c∈Y:=by
        induction hj using Nat.decreasingInduction generalizing x with
        | self=> have ht:f x=0:=funext fun i=> hp i i.isLt; rw [show x=0 from f.map_eq_zero_iff.mp ht]; use 0; rw[map_zero,sub_zero]; exact Y.zero_mem
        | of_succ i hi IH=>
           let s:Fin 3:=⟨i,hi⟩; obtain ⟨u,hu,v,hv,F₀⟩:= Submodule.mem_sup.mp (show f x s∈ U⊔W from H.decmp.sup_eq_top.symm ▸ Submodule.mem_top); obtain ⟨w,hw,hf⟩:=H.toll u hu; let c:Jewel W:= Pi.single s ⟨v,hv⟩; let q:= (σ^i) w
           have hx'(j): f ((σ^j) w)=(τΓ F ^ j) (f w):=by
              induction j with| zero=>rfl| succ k ih=> rw[pow_succ',pow_succ' (τΓ ..), Module.End.mul_apply,Module.End.mul_apply, he.inverse',ih]
           have hQ:q∈Y:=by
              unfold q; exact (show ∀ j:ℕ,(σ^j) w ∈ Y from fun j=>by induction j with | zero=>exact hw| succ j ih=> rw[pow_succ', Module.End.mul_apply]; exact H.τZ _ ih) _
           have hk (y:Jewel F)(j:Fin 3): (τΓ F ^ j.val) y j=y 0∧∀ t:Fin 3,t < j→ (τΓ F ^ j.val) y t=0:=by
              fin_cases j<;> refine ⟨rfl,fun t h=>?_⟩ <;> fin_cases t <;> first | rfl| (exfalso; revert h; decide)
           have hg(j:Fin 3): f (x-(marchL f W c+q)) j= f x j-((c j).val+(τΓ F^i) (f w) j):=by simp only [map_sub,map_add,Pi.sub_apply,Pi.add_apply,Mway f c,q,hx']
           obtain ⟨z,hz⟩:= IH (x-(marchL f W c+q)) (fun j hj=>by
               rw [hg]; by_cases hl:j=s; · subst j; rw [(hk _ s).1, ← hf, ← F₀]; unfold c; rw [Pi.single_eq_same,add_comm v u]; exact sub_self _
               have ht : j<s:= lt_of_le_of_ne (by exact show j.val≤ i from by omega) hl; rw [hp _ ht,(hk _ s).2 _ ht,show c j=_ from (show c j=0 from Pi.single_eq_of_ne hl _),ZeroMemClass.coe_zero,add_zero,sub_zero])
           use c+z; rw [map_add, show x-(marchL f W c+marchL f W z)=x-(marchL f W c+q)-marchL f W z+q by abel]; exact Y.add_mem hz hQ
      exact hu 0 (by omega) x (fun i h=>by omega)
-- packaging extraction
structure Sleek (ι:F→ₗ[ℝ] E)(π:E→ₗ[ℝ] F)(Y:Submodule ℝ E) :Prop where
    len (f:F):π (ι f)=f
    hero (x:E) : x∈Y↔ π x=0
    slice (x:E):x-ι (π x)∈Y
lemma frond (ι:F→ₗ[ℝ] E)(Y:Submodule ℝ E)(h:∀ f,ι f∈Y→ f=0)(hp:∀ x: E,∃ v:F,x-ι v∈Y):∃ f:E→ₗ[ℝ] F, Sleek ι f Y:=by
      choose g hg using hp; have hv(a:E)(b:F)(hB:a-ι b ∈Y): g a=b:= by
        apply sub_eq_zero.mp; apply h; rw [map_sub, show ι (g a)-ι b=(a-ι b)-(a-ι (g a)) by abel]; exact Y.sub_mem hB (hg a)
      let f:E→ₗ[ℝ] F:={toFun:=g,map_add':=fun x y=>hv _ _ (by rw [map_add,add_sub_add_comm]; exact Y.add_mem (hg x) (hg y)),map_smul':=fun c x=> hv _ _ (by change c•_-ι (c • g x)∈_; rw [map_smul,← smul_sub]; exact Y.smul_mem c (hg x))}
      refine ⟨f, fun x=>hv _ _ (by rw[sub_self]; exact Y.zero_mem),fun x=>⟨fun h=>hv x _ (by rw [map_zero,sub_zero]; exact h),fun hh=>?_⟩,hg⟩
      have he:=hg x; change g x=0 at hh; rwa [hh,map_zero,sub_zero] at he
lemma Sleek.comm {B':F→ₗ[ℝ] E}(h:Sleek B' π Y) (d:F→ₗ[ℝ] F) (hp:∀ x,x∈Y→σ x∈Y) (hq:∀ x,σ (B' x)=B' (d x))(x:E): π (σ x)=d (π x):=by
     have hv:= (h.hero _).1 (hp _ (h.slice x)); rw [map_sub,map_sub,hq,h.len] at hv; exact sub_eq_zero.mp hv
end YM.OPE.Hark
