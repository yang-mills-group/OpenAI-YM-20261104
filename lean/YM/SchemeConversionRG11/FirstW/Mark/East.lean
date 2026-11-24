import YM.SchemeConversionRG11.FirstW.Mark.Pole
/-! Equation & orbital projection for direct torus branch. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW
open Function Filter Set Lattice Pert Align Maxwell Topology
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {p : Ear G (Per n)}
abbrev impulse := @needle G n
-- `grad` sign here is negative.
lemma east_free (he : ∀ ε:Site n→G.Color, p (Orb.grad ε)=0) : Orb.divB (tbranch G n p)=fun _=>0 := by
  funext x; apply ink_zero; intro t
  let u:=unitColor G t
  let f y := (linGreen n (y-x)) • u
  have eh (e : Edge (Site n)) : Orb.grad f e = (Orb.ghostLink (x,e.2) u e - Orb.ghostLink (x-step e.2,e.2) u e) := by unfold Orb.grad Orb.ghostLink f linGreen; simp only [if_true]; rw [show e.1 + step e.2 - x=e.1-(x-step e.2) by abel]
  change inner ℝ u _ = 0; unfold Orb.divB
  simp_rw [inner_sum, inner_sub_right, branch_elem,←map_sub, ←map_sum]
  rw [show ∑ i:Axis,(Orb.ghostLink (x,i) u - Orb.ghostLink (x-step i,i) u)= Orb.grad f from funext fun s=>by simp only [Finset.sum_apply,Pi.sub_apply]; rw [Finset.sum_eq_single s.2,eh]; intro j _ hj; unfold Orb.ghostLink; simp only [Ne.symm hj,if_false,sub_self]; simp, he]
lemma ghost_swap (l s : Edge (Site n)) (u : G.Color) : Orb.ghostLink l u s = Orb.ghostLink s u l := by
  unfold Orb.ghostLink; rw [show l.1-s.1=-(s.1-l.1) by abel,Full.toroid_even]; split_ifs <;> grind
lemma landing (i : Axis) (v : Site n) (u : G.Color) :
    Orb.lap (fun w : Site n=> Orb.ghostLink (w,i) u) v = -needle (v,i) u + fun s:Edge (Site n)=>if s.2=i then ((n.val : ℝ)^(-4:ℤ)) • u else 0 := by
  let F (v : Site n) := Orb.ghostLink (v,i) u
  funext s; change Orb.lap F v s = -(needle (v,i) u s) + _
  have eq : Orb.lap F v s = Orb.lap (fun w : Site n=>Orb.ghostLink s u (w,i)) v := by
    unfold F Orb.lap; simp only [Finset.sum_apply, Pi.add_apply,Pi.sub_apply,Pi.smul_apply]; apply Finset.sum_congr rfl; intro j _; rw [ghost_swap (v+step j,i),ghost_swap (v-step j,i),ghost_swap (v,i)]
  rw [eq,Orb.lap_ghost,pinched]; cases s; congr 2 <;> grind
lemma water (p : Ear G (Per n)) (hc : ∀ f:Axis → G.Color, p (f ∘ Prod.snd)=0) (k : Axis) (x : Site n) :
    Orb.lap (Orb.row (tbranch G n p) k) x = -(ladder p (x,k)) := by
  apply ink_eq; intro t; let u := unitColor G t
  simp only [inner_neg_right,ladder_val,Orb.lap,Orb.row,two_smul]
  simp_rw [inner_sum,inner_sub_right,inner_add_right,branch_elem,←map_add,← map_sub,← map_sum]
  have hh := landing (n:=n) k x u; simp_rw [Orb.lap,two_smul] at hh
  let f i := if i=k then ((n.val:ℝ)^(-4:ℤ)) • u else 0
  rw [hh]; change p (_+f ∘ Prod.snd)=-_
  rw [map_add,map_neg,hc,add_zero]
lemma active_equation (p : Ear G (Per n)) (he : ∀ ε:Site n→G.Color, p (Orb.grad ε)=0) (hc : ∀ f:Axis → G.Color, p (f ∘ Prod.snd)=0) (v : FullT G n) :
    (∑ x,∑ i,∑ j, if i<j then inner ℝ (Orb.cur v x i j) (Orb.cur (tbranch G n p) x i j) else 0) = p v := by
  have H := Orb.total v (tbranch G n p)
  simp_rw [east_free he, inner_zero_right,Finset.sum_const_zero,add_zero,water p hc,inner_neg_right,Finset.sum_neg_distrib,neg_neg] at H
  rw [H, ← ladder_sol]
  exact (Fintype.sum_prod_type (fun l:Site n × Axis=>inner ℝ (v l) (ladder p l))).symm

def reflectT (G : Gauge) (n : Side) : FullT G n →ₗ[ℝ] FullT G n := LinearMap.pi fun l=> -LinearMap.proj (Orb.image l)
def reduced (p : Ear G (Per n)) : Module.Dual ℝ (Orb.Potential G n) := p ∘ₗ (Orb.LinkP G n).subtype
lemma reduced_pinch (e : Edge (Site n)) (u : G.Color) : reduced (pinch e u) = Orb.formElem e u := by
  apply LinearMap.ext; intro l; exact (real_inner_comm u (l.val e)).symm
lemma branch_odd (p : Ear G (Per n)) : (((Orb.kernelEquiv G n).symm (reduced p)).val : FullT G n) = tbranch G n p + reflectT G n (tbranch G n p) := by
  have he (l : Edge (Site n)) (u : G.Color) : (((Orb.kernelEquiv G n).symm (reduced (pinch l u))).val : FullT G n) = tbranch G n (pinch l u)+reflectT G n (tbranch G n (pinch l u)) := by
    rw [branch_at,reduced_pinch,←Orb.inverse_eq,LinearEquiv.symm_apply_apply]; funext s; dsimp [Orb.response, reflectT]; rw [Orb.ghost_image]; abel
  rw [pips_all p]
  have hf : reduced (∑ e:Edge (Site n), pinch e (ladder p e))=∑ e:Edge (Site n), reduced (pinch e (ladder p e)) := by ext1 y; simp only [reduced,LinearMap.comp_apply, LinearMap.sum_apply]
  rw [hf]; simp_rw [map_sum,AddSubmonoidClass.coe_finsetSum, he,Finset.sum_add_distrib] -- name
lemma pinch_potential (p q : Ear G (Per n)) : Align.jointB G n (reduced p) (reduced q) = q (tbranch G n p + reflectT G n (tbranch G n p)) := by
  change q (((Orb.kernelEquiv G n).symm (reduced p)).val) = _
  rw [branch_odd]
end YM.RG11.FirstW
