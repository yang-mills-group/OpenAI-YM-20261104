import YM.WilsonCoeffUV.Step.Ward.Covariance
/-!
# Triangular stationary-phase lookup of the first loop

X-adic. Distinguish orders before multiplying with X^-2.
Exclusive cut filtration, consecutive gradients commute. No bounds or
assumption of a C-integrated density at these orders.
-/
set_option autoImplicit false

noncomputable section
namespace YM.WilsonCoeffUV.Blue.Cameo
open Matrix Function PowerSeries
open scoped BigOperators ContDiff Topology
variable {U V : Type*}{n m k:ℕ}{R:Type*} [CommRing R]

section trunc
variable {f g: PowerSeries R}
abbrev Dark (n:ℕ)(f: PowerSeries R): Prop:= Equal n f 0
lemma Dark.faint (h:Dark n f)(p:m≤n):Dark m f:=fun i t=>h i (lt_of_lt_of_le t p)
lemma Dark.off (h:Dark n f){i}(p:i<n): coeff i f=0:= (h i p).trans (map_zero _)
lemma Dark.lamp (h:Dark n f)(p:Dark n g):Dark n (f+g):=by simpa only [zero_add] using h.add p
lemma Dark.sham (h:Dark n f): Dark n (-f):= fun i p=>by rw [map_neg,h.off p,neg_zero,map_zero]
lemma Dark.eclipse (h: Dark n f)(p:Dark m g): Dark (n+m) (f*g):=by apply equal_iff.mpr; rw [sub_zero,pow_add]; exact mul_dvd_mul (sub_zero f ▸ equal_iff.mp h) (sub_zero g ▸ equal_iff.mp p)
lemma Dark.rune (h:Dark n f)(g:PowerSeries R): Dark n (g*f):=by rw [mul_comm]; simpa only [Nat.add_zero] using (h.eclipse (show Dark 0 g from fun _ p=>by omega))
lemma Dark.zero (n:ℕ) : Dark n (0:PowerSeries R):= fun _ _=>rfl
lemma Dark.turf (h:Dark n f)(i:ℕ): Dark (n+i) (X^i*f):=by rw [mul_comm]; exact Dark.eclipse h (equal_iff.mpr (by rw [sub_zero]))
lemma Dark.tame (h:Dark (n+1) (X*f)): Dark n f :=by intro i p; have he:= h.off (by omega:i+1<n+1); simp only [coeff_succ_X_mul] at he; rw [he,map_zero]
lemma Dark.came (h:Dark (n+2) (X^2*f)): Dark n f :=by
    apply Dark.tame; apply Dark.tame; rw [← mul_assoc,←pow_two]; exact h
lemma scotch (h:Equal n f g): Dark n (f-g):=by intro i p; rw [map_sub,h i p,sub_self,map_zero]
lemma Dark.times (h:IsUnit g) (p:Dark n (g*f)): Dark n f:=by obtain ⟨g,hg⟩:=h; subst hg; have he:=p.rune (g⁻¹:Units (PowerSeries R)); rwa [← mul_assoc,Units.inv_mul,one_mul] at he
end trunc

section
variable [Fintype U][Fintype V]
variable {f:Lawn (U⊕V)→ℝ}
omit [Fintype U] in
lemma Dark.stave (i:U){f:Ink U}(h:Dark n f): Dark n (brush i f):=by intro k p; rw [brush,blot_apply,h.off p,map_zero,map_zero]
-- mixed on every list. redescend V for external removal too

noncomputable def tapping (P:Ink U) : List U→ Ink U
   | []=> P
   | i::l=> brush i (tapping P l)
omit [Fintype U] in
lemma tapped_snoc (P:Ink U)(l:List U)(a:U): tapping P (l++[a])=tapping (brush a P) l:=by induction l with
                                                                                                 | nil=> rfl
                                                                                                 | cons i l h=> simp [tapping,h]
omit [Fintype U] in
lemma tap_tap (P:Ink U)(i:U)(l:List U): tapping (brush i P) l=brush i (tapping P l):=by induction l with
                                                                                              | nil=> rfl
                                                                                              | cons j l ih=> rw [tapping,ih,brush_comm j i,tapping]
omit [Fintype U] in
lemma brush_X (i:U)(P:Ink U) : brush i (X*P) = X*brush i P:=by rw [Derivation.leibniz,show brush i X=0 from blot_X _]; ring
omit [Fintype U] in
lemma tapping_x (P:Ink U)(l:List U): tapping (X*P) l=X*tapping P l:=by induction l with
                                                                             | nil=> rfl
                                                                             | cons i l ih=> rw [tapping,ih,brush_X,tapping]
omit [Fintype U] [Fintype V] in
lemma rootPhi (p: Ink (U⊕V)){i:ℕ}: MvPolynomial.eval (0:U⊕V→ℝ) (coeff i p)=MvPolynomial.eval 0 (coeff i (projectZero p)):=by
   rw [projectZero,coeff_map]; generalize  coeff i p=P
   induction P using MvPolynomial.induction_on with
   | C a=> simp [projectZeroPoly,MvPolynomial.algebraMap_eq]
   | add p q a b=> simp only [map_add,a,b]
   | mul_X p j h=> cases j<;> simp [projectZeroPoly]

/-- disjoint lists remember INTERNAL held; external may be hit repeatedly -/
def Muted (n m:ℕ)(f:Lawn (U⊕V)→ℝ):Prop:= ∀ L:List U,L.length<n → Dark m (projectZero (tapping (jet f) (L.map Sum.inl)))
lemma Muted.internal (h:Green (f:Lawn (U⊕V)→ℝ))(p:Muted (n+1) (m+1) f)(i:U): Muted n m (rub f (.inl i)):=by
    intro L v; apply Dark.tame (R:=POL V); have he:=p (L++[i]) (by simp; omega); rw [List.map_append,List.map_singleton,tapped_snoc,sap h,tapping_x,map_mul,show projectZero (X:Ink (U⊕V))=X from by simp [projectZero]] at he; exact he
lemma Muted.outer (h:Green (f:Lawn (U⊕V)→ℝ))(p:Muted n (m+1) f)(i:V): Muted n m (rub f (.inr i)):=by
    intro L v; apply Dark.tame; have he:=(p L v).stave i; rw [← project_drop,←tap_tap,sap h,tapping_x,map_mul,show projectZero (X:Ink (U⊕V))=X from by simp [projectZero]] at he; exact he
lemma Muted.still (h:Green (f:Lawn (U⊕V)→ℝ))(p:Muted n n f): Dark n (jet f):=by
   induction n generalizing f with
   | zero=> exact fun _ i=>by omega
   | succ n ih=>
     have hy i:Dark n (jet (rub f i)):=by
        cases i with
        | inl i=> exact ih (rubbed h _) (p.internal h i)
        | inr i=> exact ih (rubbed h _) (fun l z=> p.outer h i _ (by omega))
     intro i hi
     apply pext
     · have he:Dark (n+1) (projectZero (jet f)):= p [] (by simp)
       rw [rootPhi,he.off hi,map_zero,map_zero,map_zero]
     intro j; rw [← blot_apply]; change coeff i (brush j (jet f))=_
     rw [sap h,Dark.off (f:=X*jet (rub f j)) (by simpa only [pow_one] using (hy j).turf 1) hi]; simp

-- F grade two + exact restrictions. cut q for z=0; inherited H may only preserve q-j jet.
lemma plateau (f:Lawn (U⊕V)→ℝ)(h:Green f) (a: Dark 5 (projectZero (jet f)))
   (b:∀ i:U,Dark 4 (projectZero (jet (rub f (.inl i))))) (c:∀ i j:U,Dark 3 (projectZero (jet (rub (rub f (.inl j)) (.inl i))))) : Muted 3 5 f:=by
    intro L l; cases L with
    | nil=> exact a
    | cons i L=> cases L with
                  | nil=> simp only [List.map_cons, List.map_nil,tapping,sap h,map_mul,projectZero, map_X]; exact (by simpa only [projectZero,pow_one] using (b i).turf 1)
                  | cons j L=> cases L with
                               | nil=>
                                  simp only [List.map_cons,List.map_nil,tapping,sap h,brush_X,sap (rubbed h _), ← mul_assoc,← pow_two, map_mul,map_pow]
                                  rw [show projectZero (X:Ink (U⊕V))=X by simp [projectZero]]; exact (c i j).turf 2
                               | cons p L=> simp at l; omega

/-! `BrushGrade`: residual after extraction from homogeneous Taylor. All
external rank ≥ 2 gone through second local order. -/
def BrushGrade (p: Ink (U⊕V)) := (∀ i:V,Dark 2 (brush (.inr i) p))∧(∀ i j: V,Dark 3 (brush (.inr i) (brush (.inr j) p)))
lemma BrushGrade.tar (v:Ink (U⊕V)){f:Lawn (U⊕V)→ℝ}(h:Green f)(p:Muted 3 5 f)(r:X^2*v=jet f): BrushGrade v:=by
    have he i: brush i (X^2*(v:Ink (U⊕V)))= X^2 * (brush i v):= by rw [pow_two,mul_assoc,brush_X,brush_X,← mul_assoc]
    have hn i (v:Ink (U⊕V)): brush i (X^2*v)= X^2 * (brush i v):= by rw [pow_two,mul_assoc,brush_X,brush_X,← mul_assoc]
    have ht i:Muted 3 4 (rub f (.inr i)):=p.outer h i
    constructor
    · intro i; apply Dark.came; rw [←he _,r,sap h]
      have hz:Muted 3 3 (rub f (.inr i)) := fun L l=> (ht i L l).faint (by omega)
      simpa only [pow_one] using (hz.still (rubbed h (.inr i))).turf 1
    intro i j; apply Dark.came; rw [← hn,← he,r,sap h,brush_X,sap (rubbed h _),←mul_assoc,← pow_two]; exact (((ht j).outer (rubbed h _) i).still (rubbed (rubbed h _) _)).turf 2
lemma BrushGrade.mesh {f:Lawn (U⊕V)→ℝ}(h:Green f)(p:Dark 3 (projectZero (jet f))): BrushGrade (jet f):=by
    have H:Muted 1 3 f:=by intro L l; cases L with
                                          | nil=> exact p
                                          | cons i L=> simp at l
    have Hz i:Muted 1 2 (rub f (.inr i)):= H.outer h _
    constructor
    · intro i; rw [sap h]; have ht:Muted 1 1 (rub f (.inr i)):= fun l u=>(Hz i l u).faint (by omega)
      simpa only [pow_one] using (ht.still (rubbed h (.inr i))).turf 1
    intro i j; rw [sap h,brush_X,sap (rubbed h _), ← mul_assoc,← pow_two]; exact (((Hz j).outer (rubbed h _) i).still (rubbed (rubbed h _) _)).turf 2
end
end YM.WilsonCoeffUV.Blue.Cameo
