import YM.MS.Book.Ranks
/-!
# Hamiltonian of a free Q₂ in general momentum space

`tree` evaluation when singleton. Inherits d-pack net too. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Plane
open Function Filter Set Finset Koszul Cylinder Lab Flux
variable {A P B R:Type}[CommRing R] [AddCommGroup P][Fintype A]{p:Sector A}{K:Flux A P R}
def solos (T:Charge p P R)(F:Row A P R)(l r:Legs (Mode A P)): R:= match l with
   | [a] => ∑ x:A,T.table a.1 x a.2* F ((x,a.2)::r)
   | _=> 0
lemma onlyEmpty (F:Legs B→R)(l:Legs B)(p:Sector B): scatter p l (fun x y=> if x.length=0 then F y else 0)= F l:= by
   induction l generalizing F with
   | nil=>rw [scatter_nil]; rfl
   | cons i l ih=> rw [scatter_cons]; convert! ih (fun y=> F (i::y)) using 1; congr! 3; rename_i x y; cases x <;> simp
omit [AddCommGroup P] in
lemma onlyFree (T:Charge p P R)(F:Row A P R)(h:Symm (field p) F)(l: Legs (Mode A P)): scatter (field p) l (solos T F) = T.raise F l:= by
   induction l generalizing F with
   | nil=> simp [solos,Charge.raise]
   | cons a l ih=>
     let A0 x y:= solos T F (a::x) y; let T₁ x y:= cross (field p a) (degree (field p) x)*solos T F x (a::y); let X:=allocate (field p) l (R:=R)
     have hV x r:T₁ x r= cross true (p a.1)* solos T (D a F) x r:= by
         cases x with
         | nil=> simp [T₁,solos]
         | cons i l=> cases l with
           | cons j l=> simp [T₁,solos]
           | nil=> simp only [T₁,solos,Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; by_cases hx:T.table i.1 j i.2=0; simp [hx]; rw [at_D,show F ((j,i.2)::a::r)=cross (p j) (p a.1) * F (a::(j,i.2)::r) from h [] (j,i.2) a r] -- maybe nil_append
                   have hp:= T.from_opposite _ _ _ hx; simp only [field, hp, degree_cons,degree_nil]; cases hp:p a.1 <;> cases hu:p i.1 <;> simp
     have he: A0= fun x r=> if x.length=0 then ∑ x:A, T.table a.1 x a.2*F ((x,a.2)::r) else 0:=by funext x y; cases x <;> simp [A0,solos]
     rw [scatter_cons]; change X (A0+T₁)=_; rw [map_add,he]; have hh (f:Legs (Mode A P)→R): X (fun x y=> if x.length=0 then f y else 0)=f l:= onlyEmpty f l _; rw [hh,show T₁= (cross true (p a.1):R) • (solos T (D a F)) from funext fun x=> funext (fun y=> hV x y),map_smul,show X (solos T (D a F))=_ from ih (D a F) (h.drop _), show T.raise F (a::l)= _ from T.act_at F a.1 a.2 l]; rfl

lemma singleFac (g:Row A P R)(h:Book.rank 2 g)(F:Row A P R)(T:Charge p P R)(hv: ∀ i l, attaches p K g F [i] l=solos T F [i] l)(he: Symm (field p) F) : tree p K g F=T.raise F := by
    funext l; rw [← onlyFree T F he]; apply scatter_congr; intro a b _; by_cases hx:a.length=1; obtain ⟨v,rfl⟩:= List.length_eq_one_iff.mp hx; exact hv _ _
    unfold attaches; dsimp only; have ht x: g (x::a)=0:= h _ (by rw [Book.mod_int]; simp; omega)
    simp_rw [ht,mul_zero,zero_mul,mul_zero,add_zero, Finset.sum_const_zero]; cases a with| nil=> rfl| cons i a=>cases a with| nil=>exact (hx rfl).elim| cons b _=>rfl
end YM.MS.Plane
