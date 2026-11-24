import YM.FVAAlt2.Embedding
import YM.FVAAlt2.FreqReflect

/-! No harmonic link modes survive the inversion constraint. Harmonic scalar
ghosts have to be removed explicitly. Prove that the range of the position
projection is the literal complexification of the real three constrained
integration subspaces. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2
open Lattice Finset Function MS.Koszul MS.Native MS.Plane MS.Landau
open Pert.Orb SchemeRG11.Sway
variable {G:Gauge}{n:Side}
local notation "X" => Land G n
local notation "A" => Mode G n
local notation "C" => G.ColorIndex
local notation "U" => ScalarGhost G n
local notation "Z" => Site n
open Matrix

lemma even_v (a:ScalarGhost G n)(z:Z): a.val (-z)=a.val z:= (show _∧_ from a.property).1 z

lemma fields_mirror (a:X)(u v:U): mirrored (fields a u v):= by
  rintro ⟨⟨_|i,t⟩,k⟩ x
  · cases t; exact congrArg (fun w:G.Color=> w k) (even_v u x); rfl
  cases t; swap; · change -(((gM v).val (Pert.Orb.image (x,i))) k)=_; rw [(gM v).property]; simp; rfl
  change -(a.val.val (Pert.Orb.image (x,i)) k)=_; rw [a.val.property]; simp; rfl
lemma invert_sum (a:Potential G n) (k:C)(i:Axis) : ∑ x:Z,a.val (x,i) k=0:= by
  have h x : a.val (-x+ (-step i),i) k= -(a.val (x,i) k):= by rw [← sub_eq_add_neg,show ((_,_): Pert.Orb.Links n)=Pert.Orb.image (x,i) from rfl,a.property]; simp
  have he:= Equiv.sum_comp ((Equiv.neg (Site n)).trans (Equiv.addRight (-step i))) (fun x=> a.val (x,i) k)
  simp only [Equiv.trans_apply, Equiv.neg_apply, show ∀ x, Equiv.addRight (-step i) x=(x:Z)+ (-step i) from fun _=>rfl,h,sum_neg_distrib] at he; linarith
lemma fields_valid (a:X)(u v:U): OKPosition n (fields a u v):= by
  constructor
  · rintro ⟨⟨_|i,_|_⟩,k⟩
    · have he:= sumM u; change ∑ x, u.val x k=0; rw [show ∑ x:Z, u.val x k= (∑ x:Z,u.val x) k from Eq.symm ?_,he]; rfl
      simp [WithLp.ofLp_sum,Finset.sum_apply]
    · simp [fields]
    exacts [invert_sum a.val k i,invert_sum (gM v) k i]
  · intro k x; have ht := div_trans a; change ∑ i,(a.val.val _ k-a.val.val _ k)=0; have h:=congrArg (fun v: ScalarGhost G n=>v.val x k) ht; change divB a.val.val x k=0 at h; simpa only [divB,WithLp.ofLp_sum,Finset.sum_apply,PiLp.sub_apply] using h
  · exact ⟨fun k x=>v.val x k,fun _ _ _=>rfl⟩
  exact fun _ _=>rfl

/-- Normalize a scalar gradient to an even mean-zero representative (no
connectedness or smoothness assumptions). -/
lemma even_shift {f:A→ℝ}(h:OKPosition n f)(he:mirrored f)(k:G.ColorIndex):
    ∃ a: Z→ℝ, (∀ x:Z, a (-x)=a x) ∧ ∑ x, a x=0 ∧ ∀ (x:Z)(i:Axis),
      f (kBranch k i,x)=a x-a (x+step i):= by
  obtain ⟨p,hp⟩:= h.gradient
  let u(x:Z):= (p k x+p k (-x))/2
  have hm(x:Z)(i:Axis): f (kBranch k i,x)=u x-u (x+step i):= by
    have hh : -f (kBranch k i,-x-step i)=f (kBranch k i,x):=he (kBranch k i) x
    rw [hp,hp,sub_add_cancel] at hh; rw [hp]; unfold u; rw [show -(x+step i)= -x-step i from by abel]; linarith
  let c:=∑ x,u x / (Fintype.card Z:ℝ)
  refine ⟨fun x=> u x-c,fun x=>by dsimp only [u]; rw [neg_neg]; ring,?_,fun x i=>by rw [hm]; ring⟩
  have hK: (Fintype.card Z:ℝ)≠0:= by exact_mod_cast Fintype.card_ne_zero
  rw [sum_sub_distrib,sum_const]; unfold c; rw [show ∑ x,u x / (Fintype.card Z:ℝ)=(∑ x,u x) / (Fintype.card Z:ℝ) from (Finset.sum_div ..).symm,card_univ,nsmul_eq_mul, _root_.mul_div_cancel₀ (∑ x,u x) hK, sub_self]

lemma actual_three {f:A→ℝ}(h:OKPosition n f)(he:mirrored f): ∃ a:X,∃ u v:U, fields a u v=f := by
  let R: Chart.City G Z:= fun l=> WithLp.toLp 2 (fun i=> f (vecBranch i l.2,l.1))
  have hv:R∈LinkP G n:= by
    intro l; ext k; exact Eq.symm (neg_eq_iff_eq_neg.mpr (he (vecBranch k l.2) l.1 |>.symm)) -- sign
  let a: Potential G n:=⟨R,hv⟩
  have ha: a∈TransV G n:= by change dLin a=0; refine Subtype.ext (funext fun x=>PiLp.ext fun k=>?_); change divB R x k=0; simpa [divB, WithLp.ofLp_sum,Finset.sum_apply,R] using h.vector k x -- simp at goal?
  let T(x:Z):= (WithLp.toLp 2 (fun k:C=> f (cBranch k,x)):G.Color)
  have ht:T∈Mean G n:= ⟨fun x=>PiLp.ext fun k=>he (cBranch k) x,by
      change (∑ x : Site n, LinearMap.proj (R:=ℝ) x) T = 0; rw [LinearMap.sum_apply]; apply PiLp.ext; intro k; change (∑ x,T x) k=0; simp only [WithLp.ofLp_sum,Finset.sum_apply,T]; exact h.noHarm _⟩
  choose b hb hx hh using even_shift h he
  let V(x:Z):=(WithLp.toLp 2 (fun k:C=> b k x):G.Color)
  have hV: V∈Mean G n:= ⟨fun x=>PiLp.ext fun k=>hb k x,by
      change (∑ x : Site n, LinearMap.proj (R:=ℝ) x) V = 0; rw [LinearMap.sum_apply]; apply PiLp.ext; intro k; change (∑ x,V x) k=0; simp only [WithLp.ofLp_sum,Finset.sum_apply,V]; exact hx _ ⟩
  refine ⟨⟨a,ha⟩,⟨T,ht⟩,⟨V,hV⟩,funext ?_⟩
  rintro ⟨⟨⟨_|i,_|_⟩,k⟩,x⟩
  · rfl
  · exact (h.noB k x).symm
  · rfl
  exact (hh ..).symm

section complexify
variable {R T:Type}[AddCommGroup R][AddCommGroup T]{f: Mode G n→R}
lemma glue_pull (L:R→+T)(h:OKPosition n f): OKPosition n (L ∘ f) := by
  obtain ⟨hor,vert,⟨v,hv⟩,h⟩:=h
  constructor
  · intro t; simp_rw [Function.comp_apply,← map_sum,hor,map_zero]
  · intro k x; simp_rw [Function.comp_apply,← map_sub,← map_sum,vert,map_zero]
  · exact ⟨fun a=> L ∘ v a,fun a x i=> by rw [Function.comp_apply,hv,map_sub];rfl⟩
  intro k x; rw [Function.comp_apply,h,map_zero]
lemma mir_pull (L:R→+T)(h:mirrored f): mirrored (L ∘ f) := by
  intro b x; rw [Function.comp_apply,← h b x]; unfold tensorMir; split; rfl; rw [map_neg]; rfl
lemma add_shape {g:A→R}(h:OKPosition n f)(H:OKPosition n g):OKPosition n (f+g) := by
  obtain ⟨u,hu⟩:=h.gradient; obtain ⟨w,hw⟩:=H.gradient; constructor
  · intro t; simp_rw [Pi.add_apply,sum_add_distrib,h.noHarm,H.noHarm,add_zero]
  · intro k x; simp only [Pi.add_apply,add_sub_add_comm,sum_add_distrib,h.vector,H.vector,add_zero]
  · exact ⟨u+w,fun i x k=> by rw [Pi.add_apply,hu,hw]; simp only [Pi.add_apply]; abel⟩
  intro k x; rw [Pi.add_apply,h.noB,H.noB,add_zero]
lemma add_mir {g:A→R}(h:mirrored f)(H:mirrored g):mirrored (f+g) := by
  intro b x; rw [Pi.add_apply,← h b x,← H b x]; unfold tensorMir; split; rfl; exact neg_add ..
end complexify

variable {ι κ:Type} [Fintype ι][DecidableEq ι][Fintype κ][DecidableEq κ] (A':Module.Basis ι ℝ (Land G n))(b:Module.Basis κ ℝ (ScalarGhost G n))

def SpaceField (n: Side){G:Gauge} (f: Mode G n→ℂ):Prop:= OKPosition n f ∧ mirrored f
lemma realizes_fields (f:A→ℂ) : SpaceField n f ↔ (∃ x, (embeddingM A' b).transpose *ᵥ x=f):= by
 let X₁:=(embeddingM A' b).transpose; let Y:=(embeddingℝ A' b).transpose
 have ht(z:A→ℝ): OKPosition n z ∧ mirrored z ↔ z ∈ LinearMap.range Y.mulVecLin := by
    refine ⟨ fun ⟨h,hp⟩ => ?_,?_⟩
    · obtain ⟨a,v,w,rfl⟩:= actual_three h hp; refine ⟨(coordBasis A' b).equivFun (a,(v,w)),?_⟩; rw [mulVecLin_apply,embLap]; rw [LinearEquiv.symm_apply_apply]; rfl
    rintro ⟨p,rfl⟩; change OKPosition n (Y *ᵥ p)∧ mirrored (Y *ᵥ p); unfold Y; rw [embLap]; exact ⟨fields_valid ..,fields_mirror _ _ _⟩
 constructor
 · rintro ⟨h,H⟩; obtain ⟨a,ha⟩:= (ht (Complex.re ∘ f)).mp ⟨glue_pull Complex.reCLM.toLinearMap.toAddMonoidHom h,mir_pull Complex.reCLM.toLinearMap.toAddMonoidHom H⟩; obtain ⟨v,hv⟩:= (ht (Complex.im ∘ f)).mp ⟨glue_pull Complex.imCLM.toLinearMap.toAddMonoidHom h,mir_pull Complex.imCLM.toLinearMap.toAddMonoidHom H⟩
   let x(i:Alpha ι κ):ℂ:= ⟨a i,v i⟩; have he: Complex.re ∘ (X₁ *ᵥ x)=Complex.re ∘ f:= (emb_real A' b x).trans ha; have hg: Complex.im ∘ (X₁ *ᵥ x)=Complex.im ∘ f:= (emb_imag A' b x).trans hv; exact ⟨x,funext fun i=> Complex.ext (congrFun he i) (congrFun hg i)⟩
 rintro ⟨x,h⟩
 have u: (Complex.re ∘ f)=Y *ᵥ (Complex.re ∘ x):= by rw [← h]; exact emb_real ..
 have v: (Complex.im ∘ f)=Y *ᵥ (Complex.im ∘ x):= by rw [← h]; exact emb_imag ..
 let L:=Complex.ofRealHom.toAddMonoidHom; let R:ℝ→+ℂ:= (Complex.I) • L
 obtain ⟨ht₁,hp⟩:= (ht (Complex.re ∘ f)).mpr ⟨_,u.symm⟩; obtain ⟨ht₂,hq⟩:= (ht (Complex.im ∘ f)).mpr ⟨_,v.symm⟩
 have hh : L ∘ Complex.re ∘ f + R ∘ Complex.im ∘ f=f:= by funext i; change _+Complex.I * (↑((f i).im):ℂ)=_; rw [mul_comm]; exact Complex.re_add_im ..
 exact ⟨hh ▸ add_shape (glue_pull L ht₁) (glue_pull R ht₂), hh ▸ add_mir (mir_pull L hp) (mir_pull R hq)⟩ -- motive?
end YM.FVAAlt2
