import YM.SchemeRG11.Flock.Pen
/-! Evaluating top, still over real color. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Outlook
open Function Lattice Pert Maxwell Flock Bare Tree Bark Haze Pile Atoll Crest Labels
variable {G:Gauge} {n d:ℕ}
def groveL (m:ℕ) (j:HIndex (m+1))(c:G.ColorIndex) : Taylor G m→ₗ[ℝ] ℝ where
 toFun g:=grove m j g c
 map_add' f g:=by
   let U: TurnArray m→ₗ[ℝ]ℝ:=LinearMap.proj j ∘ₗ reader m
   let x (g:Taylor G m):TurnArray m:=fun a b i=>components g a b i c
   have h : x (f+g)=x f+x g:=by funext a b i; unfold x components; rw [show takeCurl (f+g)=takeCurl f+takeCurl g from congrArg Subtype.val (potential.map_add f g)]; rfl
   change U (x (f+g))= U (x f)+U (x g); exact h ▸ U.map_add (x f) (x g)
 map_smul' t f:=by
   let U: TurnArray m→ₗ[ℝ]ℝ:=LinearMap.proj j ∘ₗ reader m
   let x (g:Taylor G m):TurnArray m:=fun a b i=>components g a b i c
   have h : x (t • f)=t • x f:=by funext a b i; unfold x components; rw [show takeCurl (t • f)=t • takeCurl f from congrArg Subtype.val (potential.map_smul t f)];rfl
   change U (x (t • f))=t • U (x f); exact h ▸ U.map_smul t _
variable (n)
def aloft (x:Sky G n→ℝ)(A:G.El)(v:Sky G n):ℝ:= G.adjoint A (WithLp.toLp 2 fun c=> x (v.1,c)) v.2
open scoped Classical
def wingline (x:Sky G n→ℝ)(b:Sky G n):ℝ:= if lineP b then x b else 0
lemma level_horizontal{k:ℕ}(h:k+1<n)(c e:G.ColorIndex)(l j:HIndex (k+1)):let i:Sky G n:=(⟨⟨k+1,h⟩,Sum.inl l⟩,c)
 groveL k j e (wideLinear G k 1 (0:Cover) (plum i))=(Pi.single (M:=fun _=>G.Color) l (unitColor G c) j) e:=by
 intro i
 rw [show plum i=linkup (plumage (hor l).val (unitColor G c)) from rfl]
 unfold groveL; simp only [LinearMap.coe_mk,AddHom.coe_mk,groove]
lemma level_line(b:Sky G n)(x:Sky G n→ℝ): Level n b (isle n x)=wingline n x b:=by
 rcases b with ⟨⟨⟨k,h⟩,a⟩,c⟩; cases k with
 | zero=>
   cases a with
   | inl i=> haveI:IsEmpty (HIndex 0):=deflate_zero; exact isEmptyElim (α:=HIndex 0) i -- check
   | inr i=> simp [Level,wingline,lineP]
 | succ k=>
   rcases a with j|j
   · let b:Sky G n:= (⟨⟨k+1,h⟩,Sum.inl j⟩,c)
     change groveL k j c (isle n x k)=wingline n x b
     rw [wingline,if_pos (show lineP b from rfl)]; let T(i:Sky G n):= if inkAge i=k+2 then x i else 0
     have he (i:Sky G n): T i * groveL k j c (wideLinear G k 1 0 (plum i)) = Pi.single (M:=fun _=>ℝ) b (x b) i:=by
        rcases i with ⟨⟨⟨t,F⟩,r⟩,c'⟩
        by_cases H:t=k+1
        · subst t; rcases r with l|l
          · let i: Sky G n:= (⟨⟨k+1,F⟩,Sum.inl l⟩,c')
            rw [level_horizontal n h c' c (show HIndex (k+1) from l) j]
            by_cases Hl:l=j
            · subst l; rw [Pi.single_eq_same]; rw [show T i=x i from if_pos rfl,unitPaint]
              by_cases Hp:c=c'
              · subst c; rw [show i=b from rfl,Pi.single_eq_same]; simp
              simp only [Hp,if_false,mul_zero]; rw [Pi.single_eq_of_ne (show i≠b from fun w=>Hp (congrArg Prod.snd w.symm))]
            rw [Pi.single_eq_of_ne (Ne.symm Hl),Pi.single_eq_of_ne (show i≠b from fun w=>Hl (by
                have hk:=congrArg (fun z:Sky G n=>z.1) w
                change (Sigma.mk _ (Sum.inl l): Feather n)=(⟨_,Sum.inl j⟩: Feather n) at hk; simpa using hk))]; simp
          let i: Sky G n:=(⟨⟨k+1,F⟩,Sum.inr l⟩,c')
          obtain ⟨p,_,_,he⟩ := plunges i (by simp [i,lineP]); rw [plum,←he,up_zero,map_zero,mul_zero,Pi.single_eq_of_ne (show i≠b from by simp [i,b])]
        let i: Sky G n:= (⟨⟨t,F⟩,r⟩,c')
        change T i * _=Pi.single (M:=fun _=>ℝ) b (x b) i; rw [show T i=0 from if_neg (show t+1≠k+2 by omega),zero_mul,Pi.single_eq_of_ne (show i≠b from fun w=>H (congrArg (fun z:Sky G n=>z.1.1.val) w))]
     unfold isle soul lump; rw [map_sum,map_sum]
     have hsum : ∑ i:Sky G n,T i * groveL k j c (wideLinear G k 1 0 (plum i))= x b:=by simp_rw [he]; simp [Pi.single_apply]
     refine Eq.trans (Finset.sum_congr rfl (fun u _=>?_)) hsum; rw [map_smul,map_smul];rfl
   simp [Level,wingline,lineP]
lemma level_star (J:Labels.Jet G)(u:G.El)(b:Sky G n):Level n b (colored u J)=aloft n (fun i=>Level n i J) u b:=by
 rcases b with ⟨⟨⟨k,h⟩,a⟩,c⟩; cases k with
 | zero=> unfold aloft; simp only [Level]; rw [show WithLp.toLp 2 (fun _:G.ColorIndex=>(0:ℝ))=(0:G.Color) from rfl,G.adjoint u|>.map_zero];rfl
 | succ k=>
    rcases a with j|j
    · unfold Level aloft; simp only; rw [show colored u J k=Taylor.paint u (J k) from rfl, grove_star]
    unfold aloft; simp only [Level]; rw [show WithLp.toLp 2 (fun _:G.ColorIndex=>(0:ℝ))=(0:G.Color) from rfl,G.adjoint u|>.map_zero];rfl
end YM.SchemeRG11.Outlook
