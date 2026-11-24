import YM.RG11Scheme.Stencil.Mine

/-! Exact potential propagation of chip. All powers account per leg weights. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace YM.RG11Scheme.Stencil.Shot
open Filter Function Set Lattice Pert Align Maxwell Mesh
open Pert.Full Point
open scoped BigOperators Classical Topology
variable {G:Gauge} {j : ℕ} {E: Type} [AddCommGroup E]
local notation "Δ" => Bond G
lemma go_concat (f:Cover→E)(x:Cover)(S D : List Axis) : go (S++D) f x = go S (go D f) x := by induction S generalizing x with|nil=>rfl|cons i S h=> rw [List.cons_append,onwards,onwards,h,h]
lemma dark (S)(x) : go S (0:Cover→E) x=0 := by induction S generalizing x with|nil=>rfl|cons i S h=> simp [h]

def variance (D:List Axis) : Cover := (D.map (fun i => step i)).sum
@[simp] lemma var_nil : variance []=0:=rfl
lemma reversal (D) (B:Cover→ℝ) (x y:Cover) : go D (fun p=>B (x-p)) y=(-1:ℝ)^D.length * go D B (x-y-variance D) := by
   induction D generalizing x y with
   | nil=> simp
   | cons i D IH =>
      rw [List.length_cons,onwards,IH, IH,onwards,pow_succ,show variance (i::D)=step i+variance D from rfl,show x-y-(step i+variance D)+step i=x-y-variance D by abel,show x-(y+step i)-variance D=x-y-(step i+variance D) by abel]; ring

def source (v : Chip G j) := v.aim.1 + variance v.d
def stain (v:Chip G j) := (-1:ℝ)^v.d.length • v.u
lemma ray_chip (v:Chip G j)(z:Cover)(i:Axis) : ray (stub v) (z,i) = if v.aim.2=i then (go v.d Pert.Cellular.coverLine (z-source v)) • stain v else 0 := by
    let y:=v.aim.2
    by_cases h:v.aim.2=i
    · rw [if_pos h]; apply ext_inner_left ℝ; intro u
      rw [ray_eval]; change go v.d (tip v.u (node u (z,i)) v.aim.2) v.aim.1 = _
      simp_rw [h]; unfold tip node
      simp_rw [if_true,real_inner_smul_right]
      rw [show (fun x:Cover=> Pert.Cellular.coverLine (x-z) * inner ℝ v.u u) = (fun x=> (AddMonoidHom.mulRight (inner ℝ v.u u)) (Pert.Cellular.coverLine (z-x))) from funext fun x=>congrArg (fun a=> a * inner ℝ v.u u) (by rw [← opposite (x-z), neg_sub]), go_map, reversal]
      unfold stain source; rw [real_inner_smul_right,real_inner_comm]; rw [sub_add_eq_sub_sub]; simp only [AddMonoidHom.mulRight_apply]; ring
    rw [if_neg h]; apply ext_inner_left ℝ; intro u; rw [ray_eval];change go v.d (tip v.u _ v.aim.2) v.aim.1=inner ℝ u (0:G.Color);unfold tip node; simp only [if_neg h,inner_zero_right];exact dark (E:=ℝ) ..
lemma ray_tally (v:Chip G j)(z:Cover)(i:Axis)(D:List Axis) : go D (fun y=>ray (stub v) (y,i)) z=go (D++v.d) Pert.Cellular.coverLine (z-source v) • (if v.aim.2=i then stain v else 0) := by
    by_cases h:v.aim.2=i
    · simp_rw [ray_chip,if_pos h]; let C:=LinearMap.toSpanSingleton ℝ _ (stain v); rw [show (fun y:Cover=> _)=(fun y=> C (go v.d Pert.Cellular.coverLine (y-source v))) from ?_] -- fix
      · apply Eq.trans (go_map C.toAddMonoidHom (fun y:Cover=>go v.d Pert.Cellular.coverLine (y-source v)) D z); rw [go_concat]; refine congrArg (fun u:ℝ=>C u) ?_; change go D (fun y : Cover=> go v.d Pert.Cellular.coverLine (y-source v)) z=go D (go v.d Pert.Cellular.coverLine) (z-source v); simpa only [sub_eq_add_neg] using (shifted D (go v.d Pert.Cellular.coverLine) (-source v) z)
      exact rfl
    simp_rw [ray_chip,if_neg h,smul_zero];exact dark ..

private theorem budget_chip (v:Chip G j) (i:Axis) (D:List Axis) : ∃ C>0, ∀ z, ‖go D (fun y=>ray (stub v) (y,i)) z‖ ≤ C/wide z^(2+j+D.length) := by
   let U := if v.aim.2=i then stain v else 0
   let s:= source v; let k:=2+j+D.length
   obtain ⟨C,hc,H⟩:=cover_bound (D++v.d); have hw : (D++v.d).length+2=k:= by rw [List.length_append,v.len]; dsimp [k];omega
   refine ⟨C * (1+wide s)^k * (1+‖U‖),by have := wide_pos s; positivity,fun z=>?_⟩
   rw [ray_tally, norm_smul]; let x:=z-s;have hx:=wide_pos x; have hs:=wide_pos s;have hp:=wide_pos z
   apply (le_trans (mul_le_mul (H (z-s)) (show ‖U‖ ≤ 1+‖U‖ by linarith) (norm_nonneg U) (by positivity)))
   rw [hw]; change C/wide x^k*(1+‖U‖)≤_ / wide z^k; rw [mul_div_right_comm (C*(1+wide s)^k) _]; apply mul_le_mul_of_nonneg_right _ (by positivity)
   apply (div_le_div_iff₀ (by positivity) (by positivity)).2; rw [mul_assoc, mul_comm ((1+wide s)^k),←mul_pow]; gcongr; exact wide_budget z s
private lemma breaking (D : List Axis) (r : ℝ)(A:Δ)(i:Axis)(p:Cover): go D (fun x=> (r•A) (x,i)) p=r • go D (fun x=> A (x,i)) p := go_map ((r • LinearMap.id : G.Color→ₗ[ℝ]G.Color).toAddMonoidHom) _ _ _
variable {A:Dual G}
theorem budget_arm (h:A∈ quarry G j) (i:Axis)(D:List Axis) : ∃ C>0, ∀ z, ‖go D (fun y=>ray A (y,i)) z‖ ≤ C/wide z^(2+j+D.length) := by
    induction h using Submodule.span_induction with
    | mem y hy=> obtain ⟨c,rfl⟩:=hy; exact budget_chip c i D
    | zero => refine ⟨1,zero_lt_one,fun x=>?_⟩; simp_rw [map_zero,Pi.zero_apply,show (fun _:Cover => (0:G.Color))=(0:Cover→ G.Color) from rfl,dark,norm_zero]; have:=wide_pos x; positivity
    | add u v hu hv H K=>
       obtain ⟨C,hc,H⟩:=H; obtain ⟨B,hb,Q⟩:=K; refine ⟨C+B,by positivity,fun z=>?_⟩
       rw [map_add,show (fun x=> _)=(fun (x:Cover)=>ray u (x,i))+(fun (x:Cover)=>ray v (x,i)) from ?_]; rotate_left
       · rfl
       rw [plus_go]; exact (norm_add_le ..).trans ((add_le_add (H z) (Q z)).trans_eq (add_div ..).symm)
    | smul r v he IH=>
       obtain ⟨C,hc,H⟩:=IH; refine ⟨(1+‖r‖)*C, by positivity,fun z=>?_⟩
       rw [map_smul,breaking, norm_smul];apply (mul_le_mul (by linarith only [norm_nonneg r]: ‖r‖ ≤ 1+‖r‖) (H z) (norm_nonneg _) (by positivity)).trans; exact (mul_div_assoc ..).symm.le
end YM.RG11Scheme.Stencil.Shot
