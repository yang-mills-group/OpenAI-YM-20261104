import YM.Integration.WilsonOriginalAlternativeNames
import YM.Extra.MULTISOURCE_TRAJECTORIES.Initial
import YM.Next.MULTISOURCE.First

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeExtraction
open Finset Function Marker RG05Readout.Many WilsonOriginalAlternativeNames
open scoped Classical BigOperators
variable {V:Type} [Fintype V] [DecidableEq V] (R:Census V)

def entry (C:V→ℂ) (j:V×Port) := if j.2=0 then 0 else if j.2=1 then C j.1 else -C j.1

def ink (C:V→ℂ) : Poly (board R) :=
  ∑ j:V×Port,Poly.send ((board R).fire j) (entry C j)

def word (p:V→ℂ) : Poly R := Poly.inject fun s=>∏ i∈s.val,p i

def stamped (p:Poly R) (C:V→ℂ) :=inheritAll R p * Poly.pass (ink R C)

theorem sheet (c:V→Port) (C:V→ℂ) : read R c (Poly.pass (ink R C)) =
    word R (fun i=>entry C (i,c i)) := by
  ext s
  rw [read_part,ink,Extra.Trajectories.pass_fire]
  change (∏ j∈s.val.image (pin c),entry C j)=_
  rw [Finset.prod_image (pin c).injective.injOn];rfl

theorem full (c:V→Port) (p:Poly R) (C:V→ℂ) : read R c (stamped R p C)=
    Multi.dilation R (fun i=>retain (c i)) p * word R (fun i=>entry C (i,c i)) := by
  rw [stamped,map_mul,elected,sheet]

theorem original (p:Poly R) (C:V→ℂ) : read R (fun _=>0) (stamped R p C)=p := by
  rw [full]
  have kept:Multi.dilation R (fun _=>retain 0) p=p:=by
    ext s;rw [Multi.dilation_part];simp [retain]
  have zero:word R (fun i=>entry C (i,0))=1:=by
    ext s
    change (∏i∈s.val,entry C (i,0))=(Poly.send R.quiet 1).part s
    rw [Poly.part_send]
    by_cases h:s=R.quiet
    · subst s;simp [Census.quiet]
    obtain ⟨i,hi⟩ : s.val.Nonempty := Finset.nonempty_iff_ne_empty.mpr (fun h'=>h (Subtype.ext h'))
    rw [if_neg h,Finset.prod_eq_zero hi (by simp [entry])]
  rw [kept,zero,mul_one]

theorem trial (p:Poly R) (C:V→ℂ) (s:R.Mode) :
    (read R (fun _=>1) (stamped R p C)).part s = p.part R.quiet * ∏i∈s.val,C i := by
  rw [full]
  have none:Multi.dilation R (fun _=>retain 1) p=Poly.send R.quiet (p.part R.quiet):=by
    ext t;rw [Multi.dilation_part,Poly.part_send]
    by_cases h:t=R.quiet
    · subst t;simp [Census.quiet]
    obtain ⟨i,hi⟩ : t.val.Nonempty := Finset.nonempty_iff_ne_empty.mpr (fun h'=>h (Subtype.ext h'))
    rw [if_neg h,Finset.prod_eq_zero hi (by simp [retain]),zero_mul]
  rw [none,show Poly.send R.quiet (p.part R.quiet)=p.part R.quiet • (1:Poly R)
    by
      ext t;rw [Poly.part_send,Poly.part_smul]
      change _=_ * (Poly.send R.quiet 1).part t
      rw [Poly.part_send];split <;> simp,smul_mul_assoc,one_mul,Poly.part_smul]
  simp [word,Poly.part,Poly.inject,entry]

theorem signed (p:Poly R) (C:V→ℂ) (v:V) :
    (read R (fun _=>2) (stamped R p C)).part (R.fire v) =
      p.part (R.fire v) - p.part R.quiet*C v := by
  rw [full,Multi.first_mul,Multi.dilation_part,Multi.dilation_part]
  simp [word,Poly.part,Poly.inject,retain,entry,Census.fire,Census.quiet]
  ring

theorem mixed (p:Poly R) (C:V→ℂ) (s:R.Mode) :
    (read R (fun _=>2) (stamped R p C)).part s =
      ∑ a:R.Mode,∑ b:R.Mode,if Poly.merges a b s then p.part a*(∏i∈b.val,-C i) else 0 := by
  have kept:Multi.dilation R (fun _=>retain 2) p=p:=by
    ext a;rw [Multi.dilation_part];simp [retain]
  rw [full,kept,Poly.part_mul]
  simp [word,Poly.part,Poly.inject,entry]

end YM.Integration.WilsonOriginalAlternativeExtraction
