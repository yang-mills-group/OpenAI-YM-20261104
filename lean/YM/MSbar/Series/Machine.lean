import YM.MSbar.Series.Pitch
/-! One- and two-loop identities suffice, constructed in every kernel solver.
Prolong for ℏ, coefficient orders, intrinsic-momentum grade through series algebra. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Category
open Function Finset Filter
open scoped BigOperators Classical
variable (X Y Z: Type*) [AddCommGroup X][Module ℂ X][AddCommGroup Y][Module ℂ Y][AddCommGroup Z][Module ℂ Z]
-- working spaces. static identities
abbrev Homo (X Y: Type*) [AddCommGroup X][Module ℂ X][AddCommGroup Y][Module ℂ Y]:= X→ₗ[ℂ] Y
abbrev Tree:= Homo X (Homo Y Z)
structure Machine where
   /-- lap P on grade 0 -/
   white : Homo X X
   /-- lap P on grade 1 -/
   blue : Homo Y Y
   /-- Δ low BV -/
   red : Homo X Y
   dot : Homo X Y
   /-- tree P on grades 0,0 and 0,1 -/
   bond : Tree X X X
   mix : Tree X Y Y
   /-- bracket low BV -/
   bracket : Tree X X Y
   splice : Tree X X Y
   /-- linearized BRST -/
   brst : Homo X Y
variable {X Y Z}
structure Calculus (M:Machine X Y): Prop where
   sb (x y:X): M.bond x y=M.bond y x
   sk (x y:X): M.bracket x y=M.bracket y x
   commute (x:X): M.blue (M.red x)=M.red (M.white x)
   leap (x:X): M.brst (M.white x)= M.blue (M.brst x)+M.dot x
   tandem (x:X): M.blue (M.bracket x x)+(2:ℂ) • M.mix x (M.red x)=M.red (M.bond x x)+(2:ℂ) • M.bracket x (M.white x)
   third (x:X): M.mix x (M.bracket x x)=M.bracket x (M.bond x x)
   checkpoint (x:X) : M.brst (M.bond x x)=M.splice x x+(2:ℂ) • M.mix x (M.brst x)

def propagate (M:Machine X Y)(s:Bool): Machine (Form X) (Form Y) := ⟨post s M.white,post s M.blue,post s M.red,post s M.dot,knot M.bond,knot M.mix,knot M.bracket,knot M.splice,act M.brst⟩
namespace Calculus
variable {M:Machine X Y} (h: Calculus M)(s:Bool)
include h
lemma next : Calculus (propagate M s):=by
    constructor
    · intro x y; funext n; let H:=Pitch.ish_pitch n x; let J:=Pitch.ish_pitch n y; exact (H.knot J M.bond).eq (J.knot H _) (fun c=> h.sb ..)
    · intro x y; funext n; let H:=Pitch.ish_pitch n x; let J:=Pitch.ish_pitch n y; exact (H.knot J M.bracket).eq (J.knot H _) (fun c=> h.sk ..)
    · intro x; funext n; let H:=Pitch.ish_pitch n x; refine Pitch.eq ((H.post s M.red).post s M.blue) ((H.post s M.white).post s M.red) ?_; intro c; simp only [map_smul,h.commute]
    · intro x; funext n; let H:=Pitch.ish_pitch n x; refine Pitch.eq ((H.post s M.white).points M.brst) (((H.points M.brst).post s M.blue).add (H.post s M.dot)) ?_; intro c; simp only [map_smul,h.leap,Pi.add_apply,smul_add]
    · intro x; funext n; let H:=Pitch.ish_pitch n x; refine Pitch.eq (((H.knot H M.bracket).post s M.blue).add ((H.knot (H.post s M.red) M.mix).scale 2)) (((H.knot H M.bond).post s M.red).add ((H.knot (H.post s M.white) M.bracket).scale 2)) ?_
      intro c; simp only [Pi.add_apply,map_smul,smul_comm (2:ℂ) (if s then c else 1), ← smul_add,h.tandem]
    · intro x; funext n; let H:=Pitch.ish_pitch n x; exact Pitch.eq (H.knot (H.knot H M.bracket) M.mix) (H.knot (H.knot H M.bond) M.bracket) (fun c=> h.third (ish n x c))
    intro x; funext n; let H:=Pitch.ish_pitch n x; exact Pitch.eq ((H.knot H M.bond).points M.brst) ((H.knot H M.splice).add ((H.knot (H.points M.brst) M.mix).scale 2)) (fun c=> h.checkpoint (ish n x c))
end Calculus
end YM.MSbar.Category
