import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphFields
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.GraphLabelPorts
open YM YM.FVA2 YM.XSpace YM.XSpace.Normalize
open YangMills.MSbar IssuedMaxwell.Reports
open scoped Classical
variable (g:YangMills.GaugeGroup){n m:ℕ}

def datum (q:Ordinary.Label (B g)):(B g).toCoordinates.Pol:=q.2.val
theorem left (a:Fin n→Ordinary.Label (B g))(b:Fin m→Ordinary.Label (B g))(i:Fin n):
    datum g (Fin.append a b (Fin.castAdd m i))=datum g (a i):=
  congrArg (datum g) (Fin.append_left a b i)
theorem right (a:Fin n→Ordinary.Label (B g))(b:Fin m→Ordinary.Label (B g))(i:Fin m):
    datum g (Fin.append a b (Fin.natAdd n i))=datum g (b i):=
  congrArg (datum g) (Fin.append_right a b i)

theorem stock (a:Fin n→Ordinary.Label (B g))(b:Fin m→Ordinary.Label (B g))
    (H:ℕ)(h₀:∀i,(a i).1≤H)(h₁:∀i,(b i).1≤H)(room:∀i,(Fin.append a b i).1≤H):
    (fun i=>up (room i) (Fin.append a b i).2)=
    Fin.append (fun i=>up (h₀ i) (a i).2) (fun i=>up (h₁ i) (b i).2):=by
  funext i
  apply Subtype.ext
  change datum g (Fin.append a b i)= (Fin.append (fun j=>up (h₀ j) (a j).2) (fun j=>up (h₁ j) (b j).2) i).val
  refine Fin.addCases ?_ ?_ i
  · intro j
    rw [left,Fin.append_left]
    rfl
  · intro j
    rw [right,Fin.append_right]
    rfl

theorem transfer (a:Fin n→Ordinary.Label (B g))(b c:Fin m→Ordinary.Label (B g))(same:∀i,datum g (b i)=datum g (c i)):
    ∀i,datum g (Fin.append a b i)=datum g (Fin.append a c i):=by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    rw [left,left]
  · intro j
    rw [right,right]
    exact same j
end IssuedMaxwell.GraphLabelPorts
end
