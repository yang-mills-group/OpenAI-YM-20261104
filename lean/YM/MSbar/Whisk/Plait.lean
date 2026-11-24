import YM.MSbar.Cacao.Gloss
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Whisk
open Function Filter Finset Cacao
open scoped BigOperators Classical
variable {σ ι A:Type} [Fintype σ][Fintype ι]
def Yarn {ι A:Type}[AddCommMonoid A][Fintype ι] (n:ℕ)(f:List ι → A) :A:=match n with
   | 0=>f []
   | n+1=>∑ i:ι, Yarn n (fun L=>f (i::L))
-- notation maybe cap.S.Y.Super.Fin roots repeated.
section
variable [AddCommMonoid A]{f g: List ι→ A}{h: List ι→ℝ}
lemma twilled (n:ℕ)(F:List σ→A):Yarn (n+1) F= ∑ i:σ,Yarn n (fun L=> F (i::L)):=by rw [Yarn]
lemma twillz (F:List σ→A): Yarn 0 F=F []:=rfl
lemma stitch (n:ℕ)(h:∀ L,L.length=n → f L=g L):Yarn n f=Yarn n g:= by
   induction n generalizing f g with
   | zero=> exact h [] rfl
   | succ n ih=> rw [twilled, twilled]; refine sum_congr rfl fun i _=> ih (fun j hh=>h _ (by rw [List.length_cons,hh]))
lemma spool (n:ℕ): Yarn n (fun L:List ι=> (0:A))=0 := by induction n with |zero=> rfl|succ n ih=> rw [twilled]; exact Finset.sum_eq_zero fun i _=> ih
lemma pockets (n:ℕ)(f g : List ι→A): Yarn n (fun i=>f i+g i)=Yarn n f+Yarn n g:=by
    induction n generalizing f g with
    | zero=>rfl
    | succ n ih=>rw [twilled,twilled,twilled,←sum_add_distrib]; exact sum_congr rfl fun j _=> ih (fun i=> f (j::i)) (fun i=>g (j::i))
lemma scarves (n:ℕ)(s:Finset ι)(f:ι→List σ→A) : Yarn n (fun i=>∑ x∈s,f x i)=∑ x∈s, Yarn n (f x):=by
   induction n generalizing f with
   | zero=> rfl
   | succ n ih=> rw [twilled]; simp_rw [twilled]; rw [sum_comm]; -- align
                 apply sum_congr rfl; intro j _; exact ih (fun x i=> f x (j::i)) -- order rw sum_comm on lhs? lhs ∑j,Yarn, no ∑inner.Yarn
end
lemma sheen (n:ℕ)(v:ℝ) (f:List σ→ℝ): Yarn n (fun i=> v*f i)=v*Yarn n f:=by induction n generalizing f with
   | zero=>rfl
   | succ n ih=>rw [twilled,twilled,mul_sum]; exact sum_congr rfl fun j _=> ih (fun i=> f (j::i))
lemma shiny (n:ℕ){f g : List ι→ℝ}(h:∀ l, l.length=n→f l≤ g l): Yarn n f≤ Yarn n g:=by induction n generalizing f g with
   | zero=> exact h [] rfl
   | succ n ih=> rw [twilled,twilled]; exact Finset.sum_le_sum fun j _=> ih (fun l hp=>h (j::l) (by simp [hp]))
lemma luster (n:ℕ){f:List ι→ℝ}(h:∀ l,l.length=n→0≤f l):0 ≤ Yarn n f := (spool (ι:=ι) (A:=ℝ) n).symm.trans_le (shiny n h)
lemma polished (n:ℕ)(f:List ι→ℝ):|Yarn n f|≤ Yarn n (fun i=>|f i|):=by induction n generalizing f with
   | zero=>exact le_rfl
   | succ n ih=> rw [twilled,twilled]; exact (Finset.abs_sum_le_sum_abs ..).trans (sum_le_sum fun i _=> ih (fun v=> f (i::v)))
-- parts.Compressor select sides, preserves punct sites.

def takeout (b:Bool) (f:List Bool)(l:List σ):List σ := match f,l with
    | [],_=>[]
    | _::_,[]=>[]
    | h::f,a::l=> if h=b then a :: takeout b f l else takeout b f l
lemma spark {i:σ}(l:List σ)(h:i∈l)(f : List Bool)(hh:f.length=l.length): i∈takeout true f l ∨ i∈takeout false f l:=by
    induction l generalizing f with
    | nil=> simp at h
    | cons a l ih=> cases f with
                    | nil=>simp at hh
                    | cons c f=> simp only [List.length_cons, Nat.add_right_cancel_iff] at hh; cases h with
                                 | head=>cases c<;>simp [takeout]
                                 | tail _ ht=> obtain hh|hh:= ih ht f hh
                                               left; cases c<;> simp [takeout,hh]
                                               right; cases c<;> simp [takeout,hh]
def parts (c : Bool) (l:List Bool):ℕ:=List.length (l.filter (· == c))
lemma part_le(c:Bool)(l:List Bool): parts c l≤l.length:= List.length_filter_le ..
lemma sunset (c : Bool)(h:List Bool)(l:List σ)(hh:h.length=l.length): (takeout c h l).length=parts c h :=by induction l generalizing h with
    | nil=> rw [show h=[] by simpa using hh]; simp [takeout,parts]
    | cons a l ih=> cases h with
                    | nil=>simp at hh
                    | cons p h=>simp only [List.length_cons,Nat.add_right_cancel_iff] at hh; by_cases ht:p=c<;>simp [takeout,ht,parts,List.filter_cons,ih h hh] <;> rfl
lemma knot(n:ℕ)(l : List Bool)(h:l.length=n)(f g:List σ→ℝ):
    Yarn n (fun i=> f (takeout true l i)*g (takeout false l i))= Yarn (parts true l) f * Yarn (parts false l) g:=by
    induction n generalizing f g l with
    | zero=> rw [show l=[] by simpa using h]; rfl
    | succ n ih=> cases l with
                   | nil=>simp at h
                   | cons c l=>
                      simp only [List.length_cons, Nat.add_right_cancel_iff] at h; rw [twilled]; cases c
                      · simp only [takeout, reduceCtorEq, ↓reduceIte]; rw [show parts true (false :: l)=parts true l by simp [parts], show parts false (false::l)=parts false l+1 by simp [parts],twilled,mul_sum]; exact sum_congr rfl fun i _=>ih l h f (fun j=>g (i::j))
                      · simp only [takeout, reduceCtorEq, ↓reduceIte]; rw [show parts true (true ::l)=parts true l+1 by simp [parts], show parts false (true :: l)=parts false l by simp [parts],twilled,sum_mul]; exact sum_congr rfl fun i _=>ih l h (fun j=> f (i::j)) g
-- useful ∂ Lap.PL: put at end
lemma bothEnds [AddCommMonoid A] (n:ℕ)(f:List σ→A): ∑ i:σ,Yarn n (fun l=> f (l++[i]))= Yarn (n+1) f:=by
   induction n generalizing f with
   | zero=> rw [twilled];rfl
   | succ n ih=> rw [twilled (n+1)]; simp_rw [twilled n]; rw [sum_comm]; apply Finset.sum_congr rfl; intro i _
                 -- inspect direction
                 exact ih (fun l=> f (i::l))|>.trans (twilled n _)
end YM.MSbar.Whisk
noncomputable section
namespace YM.MSbar.Whisk
open Function Filter Finset
open scoped BigOperators Classical
variable {ι σ A B:Type} [Fintype ι][Fintype σ]
lemma pool [AddCommMonoid A] (m n :ℕ)(f:List ι→ List σ→A): Yarn m (fun i=> Yarn n (f i))=Yarn n (fun j=> Yarn m (fun i =>f i j)):=by
    induction m generalizing f with
    | zero=>rfl
    | succ m ih=>
       rw [twilled]; conv_rhs => arg 2; ext; rw [twilled m]
       rw [scarves]; exact Finset.sum_congr rfl fun i _=> ih (fun L j=> f (i::L) j)
lemma total_books (n:ℕ)(t:ℝ): Yarn (ι:=ι) n (fun _=> t)=(Fintype.card ι:ℝ)^n*t:=by
    induction n with |zero=> rw [twillz];simp|succ n ih=>rw [twilled]; simp only [ih,sum_const,nsmul_eq_mul,card_univ, pow_succ]; ring
lemma spun [AddCommMonoid A][AddCommMonoid B](g:A→+B)(n:ℕ)(f:List σ→A): g (Yarn n f)=Yarn n (fun i=>g (f i)) := by induction n generalizing f with
   | zero=>rfl
   | succ n ih=> rw [twilled,twilled,map_sum]; exact Finset.sum_congr rfl fun i _=> ih (fun j=> f (i::j))
end YM.MSbar.Whisk
