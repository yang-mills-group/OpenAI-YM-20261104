import YM.SchemeConversionRG11.FirstW.Mark.East
/-! Native linear mark arrays in exact probe representation. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter Set Lattice Pert Align Maxwell Topology
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {X : Type*} [AddCommGroup X] [One X]
variable (k : Labels.Key G)
def tape (h : ℝ) (x : Four X) : Ear G X := (Labels.axes G k.1).coord k.2 ∘ₗ (Bare.wideLinear G k.1 h x)
def mass (k : Labels.Key G) := k.1+2
abbrev native (k : Labels.Key G) (x : Four X) := tape k 1 x
lemma tape_scales (h : ℝ) (x : Four X) : tape k h x = (h^(mass k))⁻¹ • native k x := by
  apply LinearMap.ext; intro A
  have he : h ^ (-(↑k.fst + 2 : ℤ)) = (h^mass k)⁻¹ := by rw [zpow_neg,mass]; norm_cast
  simp only [native,tape,Bare.wideLinear,LinearMap.comp_apply,LinearMap.smul_apply,LinearMap.sum_apply,map_smul,map_sum,one_zpow,one_smul,he,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _; ring
lemma tape_again (h : ℝ) (x : Site n) : reduced (tape k h x) = (Labels.axes G k.1).coord k.2 ∘ₗ Bare.slope h x k.1 := by
  apply LinearMap.ext; intro v; unfold tape reduced; simp only [LinearMap.comp_apply, Submodule.subtype_apply]
  rw [Bare.slope_eq] -- ambiguity
variable {j : ℕ}
-- signed transform of native gradients, proves row kills all. constant axes separately.
def momentE (f : Four X → G.Color) : Wind G X := fun e => f e.1 - f (e.1 + step e.2)
lemma tilted (s : Signed) (f : Four X→G.Color) : Bare.wideLink G s (momentE f) = momentE (f ∘ s.act) := by
  funext e; rw [Bare.wideLink_apply]
  have hv := Lattice.Step.vec_rotate (d:= posDir e.2) (R:=X) s
  rw [Step.vec_pos] at hv
  unfold Step.used momentE; dsimp only [comp_apply,Prod.fst, Prod.snd]; simp_rw [Signed.act_add, ←hv]
  split_ifs with h <;> simp [h,Step.vec]
  rw [sub_eq_add_neg]
lemma tilt_const (s : Signed) (f : Axis→G.Color) : ∃ r:Axis→G.Color, Bare.wideLink G s (R:=X) (f ∘ Prod.snd)=r ∘ Prod.snd := by
  refine ⟨fun i:Axis=> (if ((posDir i).rotate s).neg then -1 else (1:ℝ)) • f ((posDir i).rotate s).dir, funext fun e=>?_⟩
  rw [Bare.wideLink_apply]; unfold Step.used; split_ifs with h <;> simp [h]
lemma washed (f : Four X→G.Color) (x : Four X) : Bare.wideCore G j x (momentE f)=0 := by
  funext i l γ
  have he (z : Four X) : Bare.wideCurl (momentE f) z i l=0 := by unfold Bare.wideCurl; dsimp only [momentE]; rw [add_right_comm z]; abel
  simp only [Bare.wideCore_apply,he,smul_zero,Finset.sum_const_zero]; rfl
lemma rubbed (f : Axis→G.Color) (x : Four X) : Bare.wideCore G j x (f ∘ Prod.snd)=0 := by
  funext i l γ; simp [Bare.wideCore_apply,Bare.wideCurl]
lemma letter_C (h : ℝ) (x : Four X) (u : Axis → G.Color) : tape k h x (u ∘ Prod.snd)=0 := by
  unfold tape; suffices hh : Bare.wideLinear G k.fst h x (u∘Prod.snd)=0 by rw [LinearMap.comp_apply,hh,map_zero]
  rw [Bare.wideLinear,LinearMap.smul_apply, LinearMap.sum_apply,Finset.sum_eq_zero]
  · exact smul_zero _
  intro y _; choose r hr using tilt_const (X:=X) y u; simp only [LinearMap.comp_apply,hr,rubbed,map_zero]
lemma letter_T (h : ℝ) (x : Four X) (f : Four X→G.Color) : tape k h x (momentE f) = 0 := by simp only [tape,Bare.wideLinear,LinearMap.comp_apply, LinearMap.sum_apply,LinearMap.smul_apply,tilted,washed,smul_zero, Finset.sum_const_zero,map_zero]
lemma lifted_curl (x : Site n) (A : FullT G n) (i j : Axis) : Bare.wideCurl A x i j=Orb.cur A x i j := rfl
-- decompose by orthonormal responses using same axes, both turn orientations. finite differences remain visible.
def billed {j} (s : Signed) (l : Fin (Labels.dim G j)) (v : Spot G j) := (Fintype.card Signed : ℝ)⁻¹ * (j.factorial:ℝ)⁻¹ * (Labels.axes G j).coord l (Labels.Taylor.turn s.ortho (Bare.radialMap v.impulse))
def eman (x : Site n) (a : Atom j) (u : G.Color) : Ear G (Per n) := ∑ k:Atom.Kind j, a.degree k • pinch (a.edgePull x k) u
set_option maxRecDepth 5000 in
lemma exact_sector (u : G.ColorIndex) (x : Site n) (a : Atom j) (A : FullT G n) :
    inner ℝ (unitColor G u) (Bare.wideCore G j (affine a.rot⁻¹ 0 x) (Bare.wideLink G a.rot A) a.slash a.channel a.γ) = (j.factorial:ℝ)⁻¹ *
       ((eman x a (unitColor G u)) A - (eman x (Align.swap a) (unitColor G u)) A) := by
  rw [Atom.core_combine]; unfold Align.swap
  simp_rw [real_inner_smul_right,inner_sub_right,Atom.read_wrap]; unfold eman; simp only [inner_sum,LinearMap.sum_apply,real_inner_smul_right,LinearMap.smul_apply,pinch_eq]; rfl
lemma letter_exact (x : Site n) : native k x = ∑ s:Signed,∑ v:Spot G k.1,billed s k.2 v • (eman x (v.atom s) (unitColor G v.color)-eman x (Align.swap (v.atom s)) (unitColor G v.color)) := by
  apply LinearMap.ext; intro A; simp only [native,tape,Bare.wideLinear,LinearMap.comp_apply, LinearMap.sum_apply,LinearMap.smul_apply, LinearMap.sub_apply, map_sum,map_smul, smul_eq_mul,one_zpow, one_smul,Finset.mul_sum]; apply Finset.sum_congr rfl; intro r _
  let P : Bare.Response G k.1:= Bare.wideCore G k.1 (affine r⁻¹ 0 x) (Bare.wideLink G r A)
  have hf (v : Spot G k.1) := exact_sector v.color x (v.atom r) A
  nth_rw 1 [show (Bare.wideCore G _ _ (Bare.wideLink G r A))= _ from meter_full P]; simp only [map_sum,map_smul,smul_eq_mul,Finset.mul_sum]; apply Finset.sum_congr rfl; intro v _; rw [show v.meter P=(k.fst.factorial:ℝ)⁻¹* _ from hf v]; unfold billed; ring
end YM.RG11.FirstW
