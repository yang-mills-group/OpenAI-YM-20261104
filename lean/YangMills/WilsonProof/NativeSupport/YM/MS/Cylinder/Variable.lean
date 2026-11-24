import YangMills.WilsonProof.NativeSupport.YM.MS.Cylinder.Ferry

/-!
# Variables (=sources with parity) and constants in both algebras

Haar jet calculus treats only commuting subset. BV derivatives reproduced here. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Cylinder
open Function Set Finset Koszul
variable {A R B : Type*}[CommRing R] {p:Sector A} {f:Raw A R}
open Classical in
def atLetter (i:A): Raw A R| [x]=>if i=x then 1 else 0 | _=> 0
lemma speaks (i:A): atLetter i [i]=(1:R):=if_pos rfl
lemma notNamed (i:A){j:A}(h:j≠i): atLetter i [j]=(0:R):=if_neg (Ne.symm h)
lemma speaks_p (i:A): Pure p (p i) (atLetter i (R:=R)):= by
    intro l h; cases l with
    | nil=> rfl
    | cons a l=> cases l with
      | nil=> exact notNamed i (fun hi=> h (by simp [hi]))
      | cons b l=> rfl
lemma speaks_s (i:A): Symm p (atLetter i (R:=R)):= fun l _ _ _=> by cases l <;> simp [atLetter]
lemma hear (i:A): D i (atLetter i (R:=R))=coin 1:= by funext l; cases l; exact speaks i; rfl
lemma unheard (i:A){j:A}(h:j≠i): D j (atLetter i (R:=R))=0:=by funext l; cases l; exact notNamed _ h; rfl
lemma near_letter (i:A): Uses {i} (atLetter i (R:=R)):= by
    rintro l j hj hv; cases l with
    | nil=>exact (List.not_mem_nil hj).elim
    | cons a l=> cases l with
      | nil=> simp only [List.mem_singleton] at hj; exact notNamed _ (hj ▸ hv)
      | cons b l=>rfl
def single (i:A) : Cyl A R:= ⟨atLetter i, packed (s:={i}) (by simp only [Finset.coe_singleton,near_letter])⟩
def piece (c:R) : Cyl A R:= ⟨coin c, packed (s:=∅) (fun l i hi _=> by cases l; simp_all; rfl)⟩
lemma overhear (i:A): enter i (single i (R:=R))=piece 1:=Subtype.ext (hear i)
lemma pass_over (i:A){j:A}(h:j≠i): enter j (single i (R:=R))=0:= Subtype.ext (unheard i h)
lemma couple_stone (F:Cyl A R)(c:R): couple p (piece c) F=c • F:= Subtype.ext (coin_product ..)
lemma coin_nod (i:A)(c:R): D i (coin c)=0:= funext fun _=> rfl
lemma coin_turn (T:B→A→R)(c:R): shade T (piece c)= coin c:= by
    apply ext_D; simp [piece,coin]; intro i; have he j:enter j (piece c (A:=A))=0:= Subtype.ext (coin_nod j c)
    obtain ⟨s,hs⟩:=fromCyl (piece c (A:=A)); rw [shade_drop T _ _ hs]; simp_rw [he,map_zero,smul_zero,coin_nod,Finset.sum_const_zero]
lemma coin_settled (r:A→B)(c:R) : Ferry r (piece c)=piece c:=Subtype.ext (coin_turn (way r) c)
lemma names (T:B→A→R)(i:A)(j:B): D j (shade T (single i))= T j i • coin 1 := by
   classical
   obtain h:= near_letter (R:=R) i; have hv : Uses (↑({i}: Finset A):Set A) (single i (R:=R)).val:= by simpa [single] using h
   rw [shade_drop T _ _ hv,Finset.sum_singleton,overhear,coin_turn]
lemma name (T:B→A→R)(i:A)(j:B) : shade T (single i) [j]=T j i:= by rw [D_eval j (shade T _), names]; simp [coin]
lemma escort (r:A→B)(i:A): Ferry r (single i (R:=R))= single (r i) := by
   apply Subtype.ext; apply ext_D; simp [single,atLetter]; intro j; by_cases he:j=r i
   · change _= D j (atLetter _); rw [he,hear,sailed,names,only,one_smul]
   · change _= D j (atLetter _); rw [unheard _ he,sailed,names,need r he,zero_smul]
end YM.MS.Cylinder
