import Mathlib.Algebra.BigOperators.NatAntidiagonal
import YM.MS.KoszulIndex

set_option autoImplicit false
noncomputable section
namespace YM.MS.Book
open Function Set Finset Koszul
variable {A R: Type*} [CommRing R]
variable {F H: Raw A R} {h:ℤ}
def mask (h:ℤ) : Op A R where
    toFun F l:= if (l.length:ℤ)=h then F l else 0
    map_add' F H:= by ext l; split <;> simp [*]
    map_smul' c F:= by ext l; split <;> simp [*]
lemma enough (l:List A) (h':(l.length:ℤ)=h) : mask h F l= F l:= if_pos h'
lemma strange (l:List A) (h':(l.length:ℤ) ≠ h) : mask h F l=0:= if_neg h'
lemma mod_int (l:List A) : chargeInt (fun _=>1) l=(l.length:ℤ):=by induction l with | nil=>rfl| cons i l ih=>simp [ih, add_comm]
abbrev rank (h:ℤ)(F: Raw A R):= Rails (fun _=>1) h F
lemma rankMod (F:Raw A R) (v:ℤ): rank v (mask v F):= fun l H=> strange _ ((mod_int l) ▸ H)
lemma rank_hat {F:Raw A R} (h:ℤ): rank h F↔ mask h F=F:= by
   refine ⟨fun H=> ?_,fun H l he=>?_⟩; · ext l; by_cases he:(l.length:ℤ)=h; exact enough _ he; exact (strange _ he).trans (H _ (by rw [mod_int]; exact he)).symm
   rw [← H]; apply strange l; rwa [mod_int] at he
end YM.MS.Book
