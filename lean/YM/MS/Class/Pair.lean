import YM.MS.Class.Geometry
/-!
# Class at rank two

Antifield coefficient also independent of the kinetic; scale ghost variables.
`anti` sign rule relates it to a real coefficient. Quadratic symbols on unclamped
plane waves: a negative convention in det can still be scaled.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Landau.Detect
open Function Filter Set Finset Plane Koszul Real Momentum Wire
open scoped Topology ContDiff
open Complex (I)
variable {G: Gauge} {F : Law G} {h : ℤ}
-- polarization length two
lemma pair_shape (X: Class F h) (i j : Branch G Axis) : Shape (fun p: FourP=> F [(i,p),(j,-p)]) (h-(wfield i+wfield j)):= by
    let I := ContinuousLinearMap.id ℝ FourP
    let Q : Wire (Branch G Axis) FourP FourP:= [(i,I),(j,-I)]; have hQ : Course true Q := by intro _; simp [Q,net]
    convert X.graded FourP Q hQ using 1; rfl; simp [fieldDim,Q]
lemma pair_color (X: Class F h) (K:G.Simple) (k l : Atom Axis) (p:FourP) (e:G.ColorIndex) (i j) : F [qnote k i p,qnote l j (-p)] = if i=j then F [qnote k e p,qnote l e (-p)] else 0:= by
   let V i j:= F [qnote k i p, qnote l j (-p)]
   have hv : ∀ (g:G.El) i j, (∑ a:G.ColorIndex,(weight g i a:ℂ)*(∑ b:G.ColorIndex,(weight g j b:ℂ)*V a b))=V i j:= fun g i j=> X.solid.color _ (fun _=> by simp [net,qnote]: Course true [qnote k i p,qnote l j (-p)]) g
   obtain ⟨c,hc⟩:= pair_value K V hv; change V i j = if i=j then V e e else 0; rw [hc i j,hc e e]; simp
lemma oddStar (x:ℂ) (h:-x=star x) : ∃ a:ℝ,x=I*(a:ℂ):= by
   have ht := congr_arg Complex.re h; simp at ht
   exact ⟨x.im, by apply Complex.ext <;> simp; linarith⟩
lemma evenStar (x:ℂ) (h:x=star x) : ∃ a:ℝ,x=(a:ℂ):= by
   have ht := congr_arg Complex.im h; simp at ht; exact ⟨x.re, by apply Complex.ext <;> simp; linarith⟩
namespace Mark -- temporarily
variable (i j : CI G)
-- anti-ghost
abbrev ghostPair (F: Law G) (i j : CI G) (a:Axis) := fun (p: FourP)=>F [C i p,U a j (-p)]
-- vector pair
abbrev kinPair (F : Law G) (i j : CI G) (a b:Axis) := fun (p: FourP)=>F [W a i p, W b j (-p)]
lemma gshape (X: Class F h) (i j:CI G) (a:Axis): Shape (ghostPair F i j a) (h-3) := pair_shape X _ _
lemma kshape (X: Class F h) i j a b: Shape (kinPair F i j a b) (h-2) := pair_shape X _ _
lemma gsign (X:Class F h) (k:Signed) a p: cross (k.flip a) true * ghostPair F i j (k.perm a) (k.act p)=ghostPair F i j a p := by
   have hv:= X.signed k [C i p,U a j (-p)] (fun _=>by simp [C,U,qnote,net])
   simpa [negateField,permute,ghostPair,C,U,qnote] using hv
lemma ksign (X:Class F h) (k:Signed) a b p: cross (k.flip a) true * cross (k.flip b) true * kinPair F i j (k.perm a) (k.perm b) (k.act p) = kinPair F i j a b p:= by
   have hv:= X.signed k [W a i p,W b j (-p)] (fun _=>by simp [W,qnote,net]); simpa [negateField,permute,kinPair,W,qnote] using hv
lemma gmirror (X:Class F h) a p: ghostPair F i j a ((Signed.mirror a).act p)= - ghostPair F i j a p := by
   have hv:= gsign i j X (Signed.mirror a) a p; rw [← hv]; simp [Signed.mirror]
lemma gdown (X:Class F h) a p: ghostPair F i j a (-p)= - ghostPair F i j a p := by
   have hv:= gsign i j X down a p; rw [← hv]; simp [show down.flip a=true from rfl]
lemma swap_same (X:Class F h) a b: ghostPair F i j a (spike a)=ghostPair F i j b (spike b) := by
   rw [← gsign i j X (turn a b)]; simp [turn]
lemma ghost_scalar (X:Class F h) (ht:h≤4): ∃ a:ℝ, (h=4 ∨ a=0) ∧ ∀ k p, ghostPair F i j k p= (a:ℂ)*I*(p k:ℂ):= by
   let V:=ghostPair F i j
   rcases lt_trichotomy h 3 with he|he|he
   · refine ⟨0, Or.inr rfl,fun k p=>?_⟩; rw [(gshape X i j _).charge (by omega)]; simp
   · subst h; refine ⟨0, Or.inr rfl,fun k p=>?_⟩
     have hq x : V k x=V k 0:= shape_constant (gshape X i j k) x
     have H : V k p=V k ((Signed.mirror k).act p) := (hq p).trans (hq _).symm
     simpa only [Complex.ofReal_zero,zero_mul] using skew_null _ (H.trans (gmirror i j X k p))
   have he : h=4:= by omega
   obtain ⟨b,hb⟩:= oddStar (V 0 (spike 0)) (by
       apply Eq.trans (gdown i j X 0 (spike 0)).symm
       convert! X.solid.real' [C i (spike 0), U 0 j (-spike 0)] (fun _=>by simp [C,U,net,qnote]) using 1)
   subst h; refine ⟨b,Or.inl rfl,fun k p=>?_⟩; rw [shape_skew_one (gshape X i j k) (gmirror i j X k) p, swap_same i j X k 0]; change (p k:ℂ)*V 0 (spike 0)=_; rw [hb]; ring
lemma even (X:Class F h) a b p : kinPair F i j a b (-p)=kinPair F i j a b p:= by
   have hv:= ksign i j X down a b p; simpa only [down_act,down_perm,Equiv.refl_apply,show down.flip a=true from rfl,show down.flip b=true from rfl,cross_true,neg_mul_neg,one_mul] using hv
lemma oddtwo (X:Class F h) {a b:Axis} (hp:a≠b) : ∀ p, kinPair F i j a b ((Signed.mirror a).act p)= - kinPair F i j a b p:= by
   intro p; rw [← ksign i j X (Signed.mirror a) a b p]; simp [Signed.mirror,hp]
lemma oddtwo' (X:Class F h) {a b:Axis} (hp:a≠b) : ∀ p, kinPair F i j a b ((Signed.mirror b).act p)= - kinPair F i j a b p:= by
   intro p; rw [← ksign i j X (Signed.mirror b) a b p]; simp [Signed.mirror, Ne.symm hp]
end Mark
end YM.MS.Landau.Detect
