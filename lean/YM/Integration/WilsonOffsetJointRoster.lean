import YM.Integration.WilsonOffsetLampRoster

/-! The same intact finite Wilson roster at both locations: the unchanged
exterior is an original occupied subfamily evaluated on the same fine field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOffsetJointRoster
open Function Finset Lattice RG Wilson Labels Next.Foundations RGComparison.Core16.Spool
open WilsonConditionalTaylorLabels
open scoped Classical BigOperators
variable {G:Gauge} {n:Side}

def one (a:Roster G) (i:Fin a.length) (o:Site n) (U:Config G n):ℂ:=
  (localSection G (a.get i).1).evaluate (Pi.single (a.get i).2 1) (expandAt o U)
def field (a:Roster G) (s:Finset (Fin a.length)) (o:Fin a.length→Site n) (U:Config G n):ℂ:=
  tally (packet ⟨a,s⟩) (fun j=>o j.val) U

theorem finite (a:Roster G) (s:Finset (Fin a.length)) (o:Fin a.length→Site n) (U:Config G n):
    field a s o U=∏j∈s,one a j (o j) U:=by
  change (∏j:↥s,one a j.val (o j.val) U)=_
  exact Finset.prod_coe_sort s (fun j=>one a j (o j) U)

theorem inserted (a:Roster G) (s:Finset (Fin a.length)) (i:Fin a.length) (hi:i∈s)
    (o:Fin a.length→Site n) (z:Site n) (U:Config G n):
    field a s (Function.update o i z) U=field a (s.erase i) o U*one a i z U:=by
  let g:=fun j=>one a j (Function.update o i z j) U
  calc _=(∏j∈s.erase i,g j)*g i:=(finite a s _ U).trans (Finset.prod_erase_mul s g hi).symm
       _=_:=by
         rw [finite]
         apply congrArg₂ (·*·)
         · apply Finset.prod_congr rfl;intro j hj
           simp only [g,Function.update_of_ne (Finset.mem_erase.mp hj).1]
         · simp [g]

theorem paired (a:Roster G) (s:Finset (Fin a.length)) (i:Fin a.length) (hi:i∈s)
    (o:Fin a.length→Site n) (z e:Site n) (U:Config G n):
    field a s (Function.update o i z) U-field a s (Function.update o i e) U=
      field a (s.erase i) o U*(one a i z U-one a i e U):=by
  rw [inserted a s i hi,inserted a s i hi];ring

end YM.Integration.WilsonOffsetJointRoster
