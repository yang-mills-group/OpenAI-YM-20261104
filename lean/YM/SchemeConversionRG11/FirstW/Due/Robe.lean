import YM.SchemeConversionRG11.FirstW.Due.Nod
/-! Colors/transforms of individual leg currents. No manuscript contact equality here. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW
open Function Filter MeasureTheory Lattice Pert Align Topology Deck Maxwell Extra.FD MvPolynomial LinearMap
open scoped BigOperators Classical
variable {G : Gauge} {X : Type*} [AddCommGroup X] [One X] {d : ℕ} {n : Side} (F : Labels.Frames G)
lemma ac_sum (P : Module.End ℝ (Dot G d)) (x : Dot G d) (a : Who G d) : P x a= ∑ b:Who G d,accord P a b *x b := by
  have h:x=∑ b:Who G d,x b • Pi.single (M:=fun _=>ℝ) b 1:=funext fun i=>by simp [Finset.sum_apply,Pi.single_apply]
  nth_rw 1 [h]; simp only [map_sum,Finset.sum_apply,map_smul,Pi.smul_apply,smul_eq_mul,accord]; exact Finset.sum_congr rfl fun i _ =>by rw [mul_comm]; congr! 
variable {o : Four X}
def taxes (d : ℕ) (o : Four X) (h : ℝ): Wind G X →ₗ[ℝ] Dot G d := LinearMap.pi fun a => tape a.val h o
def guardH (d : ℕ) (o : Four X) (h : ℝ) (A B:Wind G X) : Dot G d := fun i=>echoLeg h o i.val A B
lemma tax_sig (o : Four X) (h : ℝ) (A:Wind G X)(d : ℕ) : taxes d o h A=salute d (fun i=> Bare.wideLinear G i h o A) := rfl
lemma glow_sig (o : Four X)(h : ℝ) (A B:Wind G X) (d : ℕ) : guardH d o h A B=salute d (fun i=>(h^(i+2))⁻¹ • glint o i A B) := by
 funext i; simp only [guardH,echoLeg,echoAt,salute,LinearMap.smul_apply,LinearMap.compr₂_apply,LinearMap.pi_apply, LinearMap.comp_apply,LinearMap.proj_apply,map_smul];rfl
abbrev paintL (d : ℕ) (u : G.El) := lit d (G:=G) (fun j=> Labels.Taylor.paint (j:=j) u)
abbrev swayL (G : Gauge) (d : ℕ) (u : Signed) := lit d (G:=G) (fun j=> Labels.Taylor.turn (j:=j) u⁻¹.ortho)
lemma tint (u : G.El) (x : Dot G d) (p : Position.E F d) : look (paintL d u x) (cloak F p) = look x (cloak F p) := by
  -- instantiate at truncated jet
  let B:= barks d x
  have H : salute d B=x := bark_in x
  rw [←H,seen,paintL, lit_any,seen]
  exact (RawLabels.physicalLabel F d p).property.2 B u
lemma cirrus (u : Signed) (x : Dot G d) (p : Position.E F d) : look x (cloak F (rideO F u.ortho d p))=look (swayL G d u x) (cloak F p) := by
  let B:=barks d x
  have H:salute d B=x:=bark_in x
  rw [←H,seen,swayL,lit_any,seen, Full.sections,LinearMap.comp_apply,RawLabels.physical_ortho]; change Labels.read _ (Labels.rotated _ _)=_
  rw [Labels.rotated,Labels.eval_changed];rw [show (u.ortho)⁻¹ = u⁻¹.ortho from (map_inv (Signed.inclusionO) u).symm];rfl
structure TiltM (T : Dot G d→ₗ[ℝ]Dot G d) (L : Module.End ℝ (Wind G X)) (o : Four X) (h : ℝ): Prop where
 flow (A : Wind G X) : T (taxes d o h A)=taxes d o h (L A)
 upright (A B : Wind G X): T (guardH d o h A B)=guardH d o h (L A) (L B)
lemma tint_pl (d : ℕ) (u : G.El) (o : Four X) (h : ℝ) : TiltM (paintL d u) (putting u) o h := by
 constructor
 · intro A; simp only [tax_sig,paintL,lit_any,letter_key]
 intro A B; rw [paintL,glow_sig, glow_sig,lit_any]; apply congrArg _; funext j; rw [map_smul]; simp only [glint_once,map_smul,map_add,putting_mark]
lemma spin_pl (G : Gauge) (d : ℕ) (t : Signed) (h : ℝ): TiltM (swayL G d t) (Bare.wideLink G t) (0:Four X) h := by
 constructor
 · intro A; simp only [tax_sig,swayL,lit_any,linear_symm,Signed.act_zero,affine,zero_add]
 intro A B; rw [swayL,glow_sig,glow_sig,lit_any]; simp only [map_smul,glints_symm,Signed.act_zero,affine,zero_add]
lemma TintK (L : Module.End ℝ (FullT G n)) (D : Module.End ℝ (Dot G d)) (o : Site n) (h : ℝ) (hp:TiltM D L o h) (hq : ∀ p : Ear G (Per n), L (tbranch G n (p ∘ₗ L))= tbranch G n p) (i : Who G d) :
    ∑ a:Who G d, accord D i a • L (river h a.val o)= river h i.val o := by
  have he : tape i.val h o ∘ₗ L = ∑ a:Who G d, accord D i a • tape a.val h o := by
    apply LinearMap.ext; intro A; rw [LinearMap.comp_apply,LinearMap.sum_apply]; have H:= ac_sum D (taxes d o h A) i; rw [hp.flow] at H; simp only [taxes,LinearMap.pi_apply] at H; rw [H]; apply Finset.sum_congr rfl; intro e _; rw [LinearMap.smul_apply]; rfl
  simp_rw [gauged]; exact ((by rw [he,map_sum,map_sum]; simp only [map_smul]:L (tbranch G n (tape i.val h o ∘ₗ L))=∑ a:Who G d,_).symm).trans (hq _)
lemma turn_branch (t : Signed)(p : Ear G (Per n)): Bare.wideLink G t (tbranch G n (p ∘ₗ Bare.wideLink G t))=tbranch G n p:= by
 rw [shape_pull,spin_once,inv_mul_cancel]; funext i; simp [Bare.wideLink_apply, Step.rotate_one,Signed.act_one,posDir,Step.used]
lemma color_branch (t : G.El)(p : Ear G (Per n)): putting t (tbranch G n (p ∘ₗ putting t))=tbranch G n p:= by
 rw [branch_put]; funext i; simp only [putting_node,←G.adjoint_mul,mul_inv_cancel,G.adjoint_one]
lemma barcloak (p : Position.E F d) : cloak F ((freeTable F).conj (table_spin F) d p) = MvPolynomial.map (starRingEnd ℂ) (cloak F p) := by
 apply rename_injective (fun x: Who G d=> x.val) Subtype.val_injective
 change uncap _=rename _ (MvPolynomial.map _ _); rw [stretch,Full.sections,LinearMap.comp_apply,Submodule.subtype_apply, RawLabels.physical_real]; change Labels.conjPol (Full.sections _ _ p)=_
 rw [←stretch]; unfold Labels.conjPol uncap; rw [map_rename]
end YM.RG11.FirstW
