import YM.MS.Book.Mask

set_option autoImplicit false
noncomputable section
namespace YM.MS.Koszul
open Function Set Finset Book
variable {A R:Type*} [CommRing R]
variable (p:Sector A)
def pencil (F:A→ Raw A R) : Shared A R
| [a]=> F a
| _=> 0
private def prefix1 (T:Op A R): Op A R where
   toFun F l:= allocate p l (pencil (fun a=> T (D a F)))
   map_add' := by
       intro f g; funext l; change allocate p l (R:=R) _=allocate p l (R:=R) _+allocate p l (R:=R) _; rw [← map_add];  congr 1; funext a b; rcases a with _|⟨a,_|_⟩ <;> simp [pencil,map_add]
   map_smul' c F:= by funext l; change allocate p l (R:=R) _= c • allocate p l (R:=R) _; rw [← map_smul]; congr 1; funext a b; rcases a with _|⟨a,_|_⟩ <;> simp [pencil,map_smul]
def fac : ℕ → Op A R| 0=> mask 0 | n+1=> prefix1 p (fac n)
lemma fac_s (F:Raw A R)(n:ℕ)(l:Legs A): fac p (n+1) F l=scatter p l (pencil (fun a=> fac p n (D a F))):= rfl
lemma coined (F:A→ R): rank 1 (fun l:List A=> match l with| [a] => F a| _=>0):=by
   intro l h; rw [mod_int] at h; rcases l with _|⟨a,_|_⟩ <;> first| rfl| (simp at h)
def mono (F:A→R) : Raw A R | [a] => F a| _=>0
lemma grade1 (F:A→R): rank 1 (mono F):= coined F
lemma mlin (F G:A→R): mono (F+G)= mono F+ mono G:= by funext l; rcases l with _|⟨a,_|_⟩ <;> simp [mono]
lemma mcost (F:A→R)(c:R): mono (c • F)= c • mono F:= by funext l; rcases l with _|⟨a,_|_⟩ <;> simp [mono]
lemma fac_support (T:Raw A R)(n:ℕ): rank n (fac p n T):= by
   induction n generalizing T with
   | zero=> exact (by simpa [fac] using rankMod T 0) -- fac unfold
   | succ n ih=>
       intro l hl; rw [fac_s]; rw [scatter_congr p l _ (fun _ _=>(0:R)) ?_]; exact map_zero (allocate ..)
       intro a b ht; obtain he:= split_length ht; rw [mod_int] at hl; rcases a with _|⟨a,_|_⟩; · rfl
       · exact ih (D a T) b (by rw [mod_int]; simp only [List.length_singleton] at he; omega)
       rfl
section
lemma onlyZ (F:Legs A→R)(l:Legs A): scatter p l (fun x y=> if x.length=0 then F y else 0)= F l:= by
   induction l generalizing F with
   | nil=> rw [scatter_nil]; rfl
   | cons i l ih=>rw [scatter_cons]; convert! ih (fun y=> F (i::y)) using 1; congr! 3; rename_i x y; cases x <;> simp
end
lemma fac_one (F:Raw A R)(h:Symm p F)(l:Legs A): scatter p l (pencil fun a=> D a F)=l.length • F l:= by
   induction l generalizing F with
   | nil=>simp [pencil]
   | cons a w ih=>
       let u:Shared A R:=fun l r=> if l.length=0 then F (a::r) else 0; let z:=pencil (fun i=>D i (D a F)); let g:=pencil (fun i=> D i F)
       rw [scatter_cons]; change scatter p w (fun l r=>g (a::l) r+cross (p a) (degree p l)*g l (a::r))=_; rw [show (fun l r=> _)= u+z from ?_] -- may stuck
       swap
       · funext l r; simp only [Pi.add_apply,u,g,z]; rcases l with _|⟨z,_|_⟩; simp [pencil];
         · simp only [pencil,List.length_singleton,one_ne_zero,↓reduceIte, at_D,degree_cons,degree_nil,Bool.xor_false]; rw [show F (z::a::r)=_ from h [] z a r]; simp only [cross_comm (p a) (p z),zero_add,List.nil_append, ← mul_assoc,cross_cross,one_mul,Pi.zero_apply]
         simp [pencil]
       rw [show scatter p w (u+z)=_ from (allocate p w).map_add u z, show allocate p w u= _ from onlyZ p (fun r=>F (a::r)) w, show allocate p w z=_ from ih (D a F) (h.drop _)]; simp [add_smul,add_comm]
lemma sym_fac (F:Raw A R)(h:Symm p F)(n:ℕ): fac p n F=n.factorial • mask n F:= by
   induction n generalizing F with
   | zero=>simp only [fac,Nat.factorial_zero,Nat.cast_zero,one_smul]
   | succ n ih=>
      funext l; by_cases hl:l.length=n+1; swap
      · rw [fac_support p F _ l (by rw [mod_int]; omega)]; rw [Pi.smul_apply,strange l (show (l.length:ℤ)≠↑(n+1:ℕ) from by omega),smul_zero]
      rw [fac_s];
      let Y:= pencil (fun a=> D a F); have he : scatter p l (pencil (fun a=> fac p n (D a F)))=scatter p l (n.factorial • Y):= by
        refine scatter_congr _ _ _ _ fun l' r ht=> ?_; obtain hz:=split_length ht; simp only [Pi.smul_apply,Y]; rcases l' with _|⟨a,_|_⟩; · simp [pencil]
        · dsimp only [pencil]; rw [ih (D a F) (h.drop _),Pi.smul_apply,enough]; simp only [List.length_singleton] at hz; omega
        simp [pencil]
      rw [he, show scatter p l (n.factorial • Y)=n.factorial • (allocate p l Y) from map_nsmul (allocate p l) .., show allocate p l Y=_ from fac_one p F h l]; rw [Pi.smul_apply,enough l (show (l.length:ℤ)=(↑(n+1:ℕ):ℤ) from by rw [hl]),hl,smul_smul,Nat.factorial_succ,mul_comm]
end YM.MS.Koszul
