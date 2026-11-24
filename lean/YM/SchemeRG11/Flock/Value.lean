import YM.SchemeRG11.Flock.Taut
/-! Bone: tagged horizontal polynomial is always a selectable leading field.
 From reprojected Wilson basis, color-correct. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Outlook
open Function Lattice Pert Maxwell Flock Bare Tree Bark Haze Pile Atoll Crest Labels MvPolynomial RawLabels
open scoped Classical
variable {G:Gauge} {n d w:ℕ}
variable (n)
def codeP (p: Sky G n): pLabel G:=match p with
 | (⟨⟨0,_⟩,_⟩,_)=>0
 | (⟨⟨m+1,_⟩,Sum.inl j⟩,c)=> ∑ i:Fin (Labels.dim G m), groveL m j c (axes G m i) • X (⟨m,i⟩:Key G)
 | (⟨⟨_+1,_⟩,Sum.inr _⟩,_)=>0
lemma pennant (p: Sky G n): IsWeightedHomogeneous generation (codeP n p) (inkAge p):=by
 obtain ⟨⟨⟨_ | k,h⟩,a⟩,c⟩:=p; unfold codeP; exact isWeightedHomogeneous_zero ..
 rcases a with j|j
 · unfold codeP; apply IsWeightedHomogeneous.sum; intro i hi; exact Submodule.smul_mem (weightedHomogeneousSubmodule ℝ generation _) _ (isWeightedHomogeneous_X ..)
 unfold codeP; exact isWeightedHomogeneous_zero ..
lemma penn_eval(p: Sky G n)(A: Labels.Jet G): aeval (rune A) (codeP n p)=Level n p A:=by
 obtain ⟨⟨⟨_ | k,h⟩,a⟩,c⟩:=p
 · exact map_zero (aeval (rune A))
 rcases a with j|j
 · unfold codeP Level; simp only [map_sum,map_smul,aeval_X]; rw [show grove k j _ _=groveL k j c (A k) from rfl]; conv_rhs=>rw [←(axes G k).sum_repr (A k)]
   rw [map_sum]; apply Finset.sum_congr rfl; intro i _; rw [_root_.map_smul]; exact mul_comm ..
 exact map_zero (aeval (rune A))
lemma card_eval(A:Labels.Jet G)(q:Sketch G n): aeval (rune A) (aeval (codeP n) q)= aeval (fun i=>Level n i A) q:=by
 have he : (aeval (R:=ℝ) (rune A)).comp (aeval (codeP n))=aeval (fun i=>Level n i A):=by ext i; rw [AlgHom.comp_apply,aeval_X,aeval_X,penn_eval]
 exact DFunLike.congr_fun he q
lemma card_grade {q:Sketch G n} (h:IsWeightedHomogeneous inkAge q w): IsWeightedHomogeneous generation (aeval (codeP n) q) w:=graded _ (fun i=>by rw [aeval_X]; exact pennant n i) _ h

variable {n}
abbrev nib (A:Labels.Jet G)(p:pLabel G):=aeval (rune A) p
lemma cabin(p:pLabel G)(A:Labels.Jet G):Complex.ofReal (nib A p)=read A (realCast p):=by
 induction p using MvPolynomial.induction_on with
 | C c=> simp [nib,Labels.read] -- check
 | add a b ha hb=> rw [nib,map_add,Complex.ofReal_add]; change Complex.ofReal (nib A a)+Complex.ofReal (nib A b)=_; unfold realCast; rw [ha,hb,map_add,map_add]
 | mul_X a i h=> unfold nib;rw [_root_.map_mul,Complex.ofReal_mul]; unfold nib at h; rw [h]; unfold realCast; rw [_root_.map_mul (MvPolynomial.map _),_root_.map_mul (Labels.read A)]; simp only [aeval_X,map_X]; rw [Labels.read,aeval_X]; rfl
lemma solder (p q:pLabel G)(h: realCast p=realCast q): p=q:=by ext k; apply Complex.ofReal_injective; exact (MvPolynomial.coeff_map _ _ _).symm.trans ((congrArg (MvPolynomial.coeff k) h).trans (MvPolynomial.coeff_map _ _ _))
lemma real_material (q:Pol G)(h:conjPol q=q) : ∃ p:pLabel G,realCast p=q:=by
 rw [← q.support_sum_monomial_coeff]; let d(s:Key G→₀ℕ):=MvPolynomial.coeff s q
 refine ⟨∑ i∈q.support,monomial i (d i).re,?_⟩; unfold realCast; rw [map_sum]; apply Finset.sum_congr rfl; intro i hi; rw [map_monomial]; congr 1
 have e : star (d i)=d i:= (MvPolynomial.coeff_map _ _ _).symm.trans (congrArg (MvPolynomial.coeff i) h)
 exact Complex.conj_eq_iff_re.mp e -- check
abbrev Neutral(p:pLabel G):Prop:=∀A:Labels.Jet G,∀u:G.El,nib (colored u A) p=nib A p
abbrev Still(q:Sketch G n):Prop:=∀ x u,aeval (aloft n x u) q=aeval x q
abbrev Solid(q:Sketch G n):Prop:=∀ x, aeval (wingline n x) q = aeval x q
lemma bone {q:Sketch G n} (hs:Still q):Neutral (aeval (codeP n) q):=by
 intro A u; unfold nib; rw [card_eval,card_eval]; simp_rw [level_star]; exact hs _ _
lemma embodied {q:pLabel G}(h:Neutral q)(g:IsWeightedHomogeneous generation q w)(he:w≤d): realCast q∈localFields G d:=by
 constructor
 · refine (MvPolynomial.mem_restrictSupport_iff ℂ).mpr (fun a ha=>?_) ; have hh: Finsupp.weight generation a=w:= Crest.mapped _ g (mem_support_iff.mp ha); change (Finsupp.weight generation) a≤_; rw [hh]; exact he
 intro A u; rw [← cabin,← cabin,h]
lemma dissolves {q:Sketch G n}(hs:Solid q): aeval (liftP n) (aeval (codeP n) q)=q:=by apply MvPolynomial.funext; intro x; simp_rw [←aeval_eq_eval, lift_read,card_eval,level_line]; exact hs x
lemma rebase_high (l:Pol G)(g:IsWeightedHomogeneous generation l w):IsWeightedHomogeneous generation (changed (rebase G) l) w:=by
 conv => arg 2; arg 2; rw [←l.support_sum_monomial_coeff]
 rw [_root_.map_sum]; apply IsWeightedHomogeneous.sum; intro i hi
 rw [←g (mem_support_iff.mp hi)]; exact pure_moved (fun a:ℕ=>a+2) (rebase G) i (l.coeff i)
lemma flesh {p:pLabel G}(h:Neutral p)(g:IsWeightedHomogeneous generation p w)(he:w≤d):∃ r:pLabel G,realCast r=(fixedPolynomial G d ⟨realCast p,embodied h g he⟩).val ∧ Neutral r ∧ IsWeightedHomogeneous generation r w ∧∀ X: Maxwell.TaylorTower G, nib (fun i=>gaugeJet (X i)) p = nib (fun i=>gaugeJet (X i)) r:=by
 let L:Label G d:=⟨realCast p,embodied h g he⟩; let M:=fixedPolynomial G d L
 have hp: realBar L=L:=by apply Subtype.ext; apply eval_ext; intro A; rw [show (realBar L).val =conjPol L.val from rfl,conj_value,show L.val=realCast p from rfl, ← cabin]; simp
 obtain ⟨r,hr⟩:=real_material M.val (congrArg Subtype.val (show realBar M=M from (fixed_real _).trans (congrArg _ hp)))
 refine ⟨r,hr, fun A u=> Complex.ofReal_injective ?_,?_,fun X=>Complex.ofReal_injective ?_⟩
 · rw [cabin,cabin, hr]; exact M.property.2 A u
 · intro s hs; refine rebase_high (realCast p) (mapped _ g) ?_ -- key binder?
   rw [show changed (rebase G) (realCast p)= M.val from rfl,← hr, MvPolynomial.coeff_map]; change ↑(coeff s r)≠(0:ℂ); exact_mod_cast hs
 rw [cabin,cabin,←jet_value, ← jet_value, hr]; congr 1; exact (unchanged (realCast p)).symm
lemma cardinality {q:Sketch G n} (hs:Solid q)(hn:Still q)(hg:IsWeightedHomogeneous inkAge q w)(h:w≤d)(F:Labels.Frames G): ∃ p: pLabel G,∃ v: (Maxwell.freeTable F).Field d,realCast p=(RawLabels.physicalLabel F d v).val ∧ Neutral p ∧ IsWeightedHomogeneous generation p w ∧ Starts inkAge w (showP G n p) q:=by
 obtain ⟨p,hp,he,hk,hr⟩:= flesh (bone hn) (card_grade n hg) h
 refine ⟨p,enroll F d ⟨_,embodied (bone hn) (card_grade n hg) h⟩,?_,he,hk,?_⟩
 · rw [embed_round]; exact hp
 have hf: q= aeval (liftP n) p:=by
    apply MvPolynomial.funext; intro x; simp_rw [←aeval_eq_eval]
    have hw:=dissolves hs
    calc _ = aeval x (aeval (liftP n) (aeval (codeP n) q)) := congrArg _ hw.symm
         _ = _ := by
            rw [lift_read,lift_read]; choose Y hy using isle_shell n x; change nib _ _= nib _ _; rw [← _root_.funext hy]; exact hr Y
 rw [hf]; exact liftTop n p hk
end YM.SchemeRG11.Outlook
