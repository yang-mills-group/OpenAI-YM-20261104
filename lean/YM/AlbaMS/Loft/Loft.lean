import YM.AlbaMS.Super.Journal
import YM.AlbaMS.Super.Rune

/-!
# Point and graph master, paired coordinates

Minimal canonical pairing. No antighost: the Faddeev ghosts are read on a
Lagrangian using longitudinal K; no ghost derivative including gauge setting
here. Delta oriented; sum across all whenever Fintype variables avail. Uses
`R` general (rational scalars only for halve). Goes to theory's actual algebra
through `RingHom`s and stencils. Never do rank induction on correctness of
master laws in application.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Loft
open Set Function Finset Bric Bric.Coil
open scoped BigOperators Classical
variable {E B R T W : Type*} [CommRing R]
abbrev Place (E B : Type*) := (E ⊕ E) ⊕ (B ⊕ B)
namespace Place
-- E for bosonic A, B for gauge generators!
abbrev a (i:E): Place E B := .inl (.inl i)
abbrev k (i:E): Place E B := .inl (.inr i)
abbrev c (j:B): Place E B := .inr (.inl j)
abbrev l (j:B): Place E B := .inr (.inr j)
end Place

def ø {E B : Type*} : Place E B → Bool:= Sum.elim (Sum.elim (fun _=>false) (fun _=>true)) (Sum.elim (fun _=>true) (fun _=>false))
def number {E B : Type*} : Place E B→ℤ:= Sum.elim (Sum.elim (fun _=>0) (fun _=> -1)) (Sum.elim (fun _=>1) (fun _=> -2))
def prim {E B : Type*} : Place E B→Bool:= Sum.elim (Sum.elim (fun _=>true) (fun _=>false)) (Sum.elim (fun _=>true) (fun _=>false))
abbrev Floor (E B R : Type*) [CommRing R] := Coil (@ø E B) R
abbrev EvenT (F : Floor E B R) := Tone false F
abbrev OddT (F : Floor E B R) := Tone true F
abbrev Observe (F : Floor E B R) := Pure number (0:ℤ) F
abbrev A (R : Type*) [CommRing R](i:E): Floor E B R:= varC R ø (Place.a i)
abbrev K (R : Type*) [CommRing R](i:E): Floor E B R:= varC R ø (Place.k i)
abbrev C (R : Type*) [CommRing R](j:B): Floor E B R:= varC R ø (Place.c j)
abbrev L (R : Type*) [CommRing R](j:B): Floor E B R:= varC R ø (Place.l j)
abbrev DA (i:E): Module.End R (Floor E B R):= D (Place.a i)
abbrev DK (i:E): Module.End R (Floor E B R):= D (Place.k i)
abbrev DC (j:B): Module.End R (Floor E B R):= D (Place.c j)
abbrev DL (j:B): Module.End R (Floor E B R):= D (Place.l j)

-- independence predicates equivalent to kernel support. Use derivatives easiest (at all Coils, not rank-capped)
def Under (F : Floor E B R):Prop:=(∀ i, DK i F=0) ∧ ∀ i,DL i F=0
def SimpleT (F : Floor E B R):Prop:= Under F ∧ ∀ i,DC i F=0
namespace Under
variable {F G : Floor E B R}
lemma zero : Under (0:Floor E B R):= ⟨fun _=> map_zero _,fun _=>map_zero _⟩
lemma simple (h:SimpleT F): Under F:=h.1
lemma add (h:Under F)(H:Under G):Under (F+G):=⟨fun i=> by rw [map_add,h.1 i,H.1 i,add_zero],fun i=> by rw [map_add,h.2 i,H.2 i,add_zero]⟩
lemma smul (h:Under F)(r:R):Under (r • F):= ⟨fun i=>by rw [map_smul,h.1 i, smul_zero], fun i=>by rw [map_smul,h.2 i,smul_zero]⟩ -- fix
lemma sum {N:Finset W} (U:W→Floor E B R)(h:∀ i∈N,Under (U i)): Under (∑ i∈N,U i):= ⟨fun _=> (map_sum _ _ N).trans (Finset.sum_eq_zero (fun i hi=> (h i hi).1 _)),fun _=> (map_sum _ _ N).trans (Finset.sum_eq_zero (fun i hi=> (h i hi).2 _))⟩
lemma mul (h:Under F)(H:Under G): Under (F*G):= ⟨fun i=>by rw [show DK i (F*G)=DK i F*G+plane true F*DK i G from rfl,h.1 i,H.1 i]; simp, fun i=> by rw [show DL i (F*G)=DL i F*G+F* DL i G from rfl,H.2 i,h.2 i];simp⟩
lemma c (j:B): Under (E:=E) (C R j):=by constructor <;> intro i <;> simp [C,DK,DL,Place.c,Place.k,Place.l]
end Under

def oriented (R : Type*) [CommRing R](v w : Place E B) : R:= match v with
 | .inl (.inl i)=> if w=Place.k i then 1 else 0
 | .inr (.inl i)=> if w=Place.l i then -1 else 0
 | _=>0
lemma lead : Graded (@ø E B) true (oriented R) := by -- fix
  rintro ((i|i)|(j|j)) x h
  all_goals first| exact False.elim (h rfl)| simp only [oriented] at h
  all_goals split at h <;> first| exact False.elim (h rfl)| (subst x;rfl)

variable [Fintype E] [Fintype B]
lemma orient_sum (F : Place E B → Place E B→ Floor E B R):
    (∑ i:Place E B,∑ j:Place E B, oriented R i j • F i j)= (∑ i:E, F (Place.a i) (Place.k i)) - ∑ j:B, F (Place.c j) (Place.l j):= by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type,Fintype.sum_sum_type]; simp only [oriented,ite_smul,one_smul,neg_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,if_true,Finset.sum_const_zero,add_zero]; rw [Finset.sum_neg_distrib,sub_eq_add_neg]

abbrev delta : Module.End R (Floor E B R):= touch (oriented R) Finset.univ
abbrev coupling (F : Floor E B R) : Module.End R (Floor E B R):= tether true (oriented R) Finset.univ F
lemma dots (F : Floor E B R): delta F=(∑ i:E, DA i (DK i F))-∑ j:B,DC j (DL j F):=by
  unfold delta; rw [touch_apply,orient_sum]; refine congr_arg₂ _ (Finset.sum_congr rfl fun i _=>?_) (Finset.sum_congr rfl fun i _=>?_); exact DD F ..; exact DD F ..
lemma connects (F G: Floor E B R)(h:EvenT F): coupling F G = ((∑ i:E, DK i F * DA i G) + ∑ i:E, DA i F*DK i G) - ((∑ i:B, DL i F * DC i G)+∑ i:B, DC i F* DL i G):=by
  unfold coupling; rw [from_tether, from_cross _ _ _ _ _ lead, orient_sum]; simp_rw [← Finset.sum_add_distrib]; refine congr_arg₂ _ (Finset.sum_congr rfl (fun i _=>?_)) (Finset.sum_congr rfl (fun j _=>?_))
  · change (plane true (DA i F))*DK i G+ DK i (plane false F)*DA i G=_; rw [polar_false]; rw [(show EvenT (DA i F) from h.dz (Place.a i)).pl]; exact add_comm .. -- zero simp
  change (plane false (DC j F))* DL j G+ DL j (plane true F)*DC j G=_; rw [polar_false,h.pl]; exact add_comm ..

end YM.MSBar.Loft
