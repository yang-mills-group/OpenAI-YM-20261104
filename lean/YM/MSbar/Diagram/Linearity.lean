import YM.MSbar.Diagram.IntegerWard
import YM.MSbar.Domain.Linear
/-! Universal-context Lap linearity. By transfer, no demand on analytically continuing
absolute values in complex s. Tree bilinear direct. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Diagram.Clear
open Super Domain Domain.DR Loops Dim Symbol Function Set Filter MeasureTheory Arrow
open scoped Topology BigOperators Classical ContDiff ENNReal
variable {C:Type} {W:Edition C} {R T : ℝ} {m n j:ℕ} {F G H:Functionals C}{K P:Links C}{d k:Bit}
section lp
variable (hk:Pilot univ j W k K)(hB:Band univ K R)(hr:0≤R)(hf:Full univ n W d F)
include hk hB hr hf
private lemma fired (v:Words C m) : Integrable (fun x=>dotted (W.members m) (K m m) (F m m) x v) (actual m):= integrable hf hk hB hr (mem_univ _) v
lemma add_lap (hg:Full univ n W d G): Lap W K (F+G)=Lap W K F+Lap W K G:=by
   refine Total.identify (budget (hf.add hg) hk hB hr isOpen_univ) ((budget hf hk hB hr isOpen_univ).add (budget hg hk hB hr isOpen_univ)) (fun m=>?_)
   rw [nominal (hf.add hg) hk hB hr (mem_univ _)]; simp only [Pi.add_apply]; rw [nominal hf hk hB hr (mem_univ _),nominal hg hk hB hr (mem_univ _)]
   funext v; unfold Loops.loop; simp only [Pi.add_apply,dotted,mul_add,Finset.sum_add_distrib]; exact integral_add (fired hk hB hr hf v) (fired hk hB hr hg v)
lemma scale_lap (c:ℂ): Lap W K (c • F)=c • Lap W K F:=by
   refine Total.identify (budget (hf.scale c) hk hB hr isOpen_univ) ((budget hf hk hB hr isOpen_univ).scale c) (fun m=>?_)
   rw [nominal (hf.scale c) hk hB hr (mem_univ _)]; simp only [Pi.smul_apply]; rw [nominal hf hk hB hr (mem_univ _)]
   funext v; unfold Loops.loop; simp only [Pi.smul_apply,dotted, smul_eq_mul,mul_left_comm _ c, ← Finset.mul_sum]; exact integral_const_mul ..
lemma line_lap (hp:Pilot univ j W k P)(he:Band univ P R): Lap W (K+P) F=Lap W K F+Lap W P F:=by
   refine Total.identify (budget hf (hk.add hp) (hB.add he) hr isOpen_univ) ((budget hf hk hB hr isOpen_univ).add (budget hf hp he hr isOpen_univ)) (fun m=> ?_)
   rw [nominal hf (hk.add hp) (hB.add he) hr (mem_univ _)]; simp only [Pi.add_apply]; rw [nominal hf hk hB hr (mem_univ _),nominal hf hp he hr (mem_univ _)]
   funext v; unfold Loops.loop; simp only [Pi.add_apply,dotted,add_div,add_mul,Finset.sum_add_distrib]; exact integral_add (fired hk hB hr hf v) (fired hp he hr hf v)
lemma kernel_lap (c:ℂ): Lap W (c • K) F=c • Lap W K F := by
   refine Total.identify (budget hf (hk.scale c) (hB.scale c) hr isOpen_univ) ((budget hf hk hB hr isOpen_univ).scale c) (fun m=>?_)
   rw [nominal hf (hk.scale c) (hB.scale c) hr (mem_univ _)]; simp only [Pi.smul_apply]; rw [ nominal hf hk hB hr (mem_univ _)]
   funext v; unfold Loops.loop; simp only [Pi.smul_apply,smul_eq_mul,dotted,div_eq_mul_inv,mul_assoc,← Finset.mul_sum]; exact integral_const_mul ..
end lp
-- tree direct distributed once; orientation. Prove unconditional. duplicate via sed
lemma add_tree_1 : splice W d K (F+G) H = splice W d K F H + splice W d K G H:= by
   have hp a b (z:ℂ): Tree.charge W d a b K (F+G) H z= Tree.charge W d a b K F H z + Tree.charge W d a b K G H z:= by
      unfold Tree.charge; rw [← dux_add]; congr! 1; unfold Tree.root; funext m x; simp [add_mul,mul_add]
   funext z n i; unfold splice walk; simp only [hp,Pi.add_apply];
   let p(a b:C)(F:Functionals C)(u v:Words C n):=Tree.charge W d a b K F H z n (u,v)
   let q:= W.parity ∘ (label (m:=n)); have h(a b:C): Super.split q (fun x y=>p a b F x y+p a b G x y) i= Super.split q (p a b F) i+Super.split q (p a b G) i:= congr_fun (split_add (F:=p a b F) (G:=p a b G) q) i
   unfold p q at h; simp_rw [h,Finset.sum_add_distrib]
lemma scale_tree_1 (c:ℂ): splice W d K (c • F) H = c • splice W d K F H := by
   have hp a b (z:ℂ): Tree.charge W d a b K (c • F) H z=c • Tree.charge W d a b K F H z:= by
      unfold Tree.charge; rw [← dux_scale]; congr! 1; unfold Tree.root; funext m x; simp [mul_left_comm _ c]; ring
   funext z n i; unfold splice walk; simp only [hp,Pi.smul_apply,smul_eq_mul]
   let p(a b:C)(F:Functionals C)(u v:Words C n):= Tree.charge W d a b K F H z n (u,v)
   let q:= W.parity ∘ (label (m:=n)); have h(a b:C): Super.split q (fun x y=>c*p a b F x y) i=c* Super.split q (p a b F) i:= congr_fun (split_scale (F:=p a b F) q c) i
   unfold p q at h; simp_rw [h,Finset.mul_sum]
lemma add_tree_2 : splice W d K H (F+G) = splice W d K H F + splice W d K H G:= by
   have hp a b (z:ℂ): Tree.charge W d a b K H (F+G) z= Tree.charge W d a b K H F z + Tree.charge W d a b K H G z:= by
      unfold Tree.charge; rw [← dux_add]; congr! 1; unfold Tree.root; funext m x; simp [add_mul,mul_add]
   funext z n i; unfold splice walk; simp only [hp,Pi.add_apply];
   let p(a b:C)(F:Functionals C)(u v:Words C n):=Tree.charge W d a b K H F z n (u,v)
   let q:= W.parity ∘ (label (m:=n)); have h(a b:C): Super.split q (fun x y=>p a b F x y+p a b G x y) i= Super.split q (p a b F) i+Super.split q (p a b G) i:= congr_fun (split_add (F:=p a b F) (G:=p a b G) q) i
   unfold p q at h; simp_rw [h,Finset.sum_add_distrib]
lemma scale_tree_2 (c:ℂ): splice W d K H (c • F) = c • splice W d K H F := by
   have hp a b (z:ℂ): Tree.charge W d a b K H (c • F) z=c • Tree.charge W d a b K H F z:= by
      unfold Tree.charge; rw [← dux_scale]; congr! 1; unfold Tree.root; funext m x; simp [mul_left_comm _ c]
   funext z n i; unfold splice walk; simp only [hp,Pi.smul_apply,smul_eq_mul]
   let p(a b:C)(F:Functionals C)(u v:Words C n):= Tree.charge W d a b K H F z n (u,v)
   let q:= W.parity ∘ (label (m:=n)); have h(a b:C): Super.split q (fun x y=>c*p a b F x y) i=c* Super.split q (p a b F) i:= congr_fun (split_scale (F:=p a b F) q c) i
   unfold p q at h; simp_rw [h,Finset.mul_sum]

lemma add_tree_3 : splice W d (K+P) F H = splice W d (K) F H + splice W d (P) F H:= by
   have hp a b (z:ℂ): Tree.charge W d a b (K+P) F H z= Tree.charge W d a b (K) F H z + Tree.charge W d a b (P) F H z:= by
      unfold Tree.charge; rw [← dux_add]; congr! 1; unfold Tree.root Tree.letter; funext m x; simp [add_mul,mul_add]; ring
   funext z n i; unfold splice walk; simp only [hp,Pi.add_apply];
   let p(a b:C)(K:Links C)(u v:Words C n):=Tree.charge W d a b (K) F H z n (u,v)
   let q:= W.parity ∘ (label (m:=n)); have h(a b:C): Super.split q (fun x y=>p a b K x y+p a b P x y) i= Super.split q (p a b K) i+Super.split q (p a b P) i:= congr_fun (split_add (F:=p a b K) (G:=p a b P) q) i
   unfold p q at h; simp_rw [h,Finset.sum_add_distrib]
lemma scale_tree_3 (c:ℂ): splice W d (c • K) F H = c • splice W d (K) F H := by
   have hp a b (z:ℂ): Tree.charge W d a b (c • K) F H z=c • Tree.charge W d a b (K) F H z:= by
      unfold Tree.charge; rw [← dux_scale]; congr! 1; unfold Tree.root Tree.letter; funext m x; simp [mul_left_comm _ c]; ring
   funext z n i; unfold splice walk; simp only [hp,Pi.smul_apply,smul_eq_mul]
   let p(a b:C)(K:Links C)(u v:Words C n):= Tree.charge W d a b (K) F H z n (u,v)
   let q:= W.parity ∘ (label (m:=n)); have h(a b:C): Super.split q (fun x y=>c*p a b K x y) i=c* Super.split q (p a b K) i:= congr_fun (split_scale (F:=p a b K) q c) i
   unfold p q at h; simp_rw [h,Finset.mul_sum]


lemma add_tick : tick W K (F+G)=tick W K F+tick W K G:= by
   have h(z:ℂ)(a:C):Arrow.read a K (F+G) z=Arrow.read a K F z+Arrow.read a K G z:= by
       funext m h; obtain ⟨⟨_|⟨b,_|⟨b,w⟩⟩,y⟩,t⟩:=h <;> simp [Arrow.read,mul_add]
   funext z n s; unfold tick walk; simp_rw [look,h,metric_add,Pi.add_apply,Finset.sum_add_distrib]; exact congr_fun (split_add (F:=fun x y=> look W K F z n (x,y)) (G:=fun x y=>look W K G z n (x,y)) _) s
lemma scale_tick (c:ℂ) : tick W K (c•F)=c • tick W K F:= by
   have h(z:ℂ)(a:C):Arrow.read a K (c•F) z=c • Arrow.read a K F z:= by
       funext m h; obtain ⟨⟨_|⟨b,_|⟨b,w⟩⟩,y⟩,t⟩:=h <;> simp [Arrow.read,mul_left_comm]
   funext z n s; unfold tick walk; simp_rw [look,h,metric_scale,Pi.smul_apply,smul_eq_mul,← Finset.mul_sum]; exact congr_fun (split_scale (F:=fun x y=>look W K F z n (x,y)) (W.parity ∘ label) c) s

end YM.MSbar.Diagram.Clear
