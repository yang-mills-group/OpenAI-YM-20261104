import YM.RegulatorIR.Step.Grid

/-! Naturality of the full diagram sums under an exact change of link labels. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalCoordinateHeat
open Function RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Packet RegulatorIR.Budget.Tuple
open RegulatorIR.Diagram
open scoped BigOperators Classical
variable {X Y:Type}(q:X≃Y){r s:ℕ}

def row (T:Packet Y r):Packet X r:=fun z=>T (q ∘ z)
def line (K:Layer Y Y):Layer X X:=fun x y=>K (q x) (q y)
def ranks (T:Ranked Y):Ranked X:=fun r=>row q (T r)
def orders (T:Orders Y):Orders X:=fun i=>ranks q (T i)

private theorem cons (z:Tuple X r)(x:X):q ∘ Fin.cons x z=Fin.cons (q x) (q ∘ z):=by
  funext i
  refine Fin.cases ?_ (fun j=>?_) i <;> simp

theorem symmetric (T:Packet Y r):Packet.symmetry (row q T)=row q (Packet.symmetry T):=by
  funext z
  rw [symmetry_at]
  unfold row
  rw [symmetry_at]
  rfl

theorem ray (T:Packet Y r)(K:Layer Y Y)(i:Fin r):
    Packet.ray i (row q T) (line q K)=row q (Packet.ray i T K):=by
  funext z
  unfold row Packet.ray Packet.swivel line
  rw [←q.tsum_eq (fun y=>K ((q ∘ z) i) y*T (update (q ∘ z) i y))]
  apply tsum_congr
  intro y
  have h:q ∘ update z i y=update (q ∘ z) i (q y):=by
    funext v
    by_cases a:v=i <;> simp [a,Function.update_of_ne]
  dsimp only
  rw [h];rfl

theorem draft (T:Packet Y r)(K:Layer Y Y):
    Packet.draft (line q K) (row q T)=row q (Packet.draft K T):=by
  have h (xs:List (Fin r)):drawing (row q T) (line q K) xs=row q (drawing T K xs):=by
    induction xs with
    | nil=>rfl
    | cons a b ih=>simp only [drawing,ih,ray]
  unfold Packet.draft
  rw [h,symmetric]

theorem loop (T:Packet Y (r+2))(K:Layer Y Y):
    Packet.loop (row q T) (line q K)=row q (Packet.loop T K):=by
  funext z
  unfold Packet.loop row
  dsimp only
  rw [←(q.prodCongr q).tsum_eq (fun w=>curve T K (q ∘ z) w)]
  apply tsum_congr
  rintro ⟨a,b⟩
  simp only [curve,line,linked,cons,Equiv.prodCongr_apply,Prod.map_apply]

theorem splice (T:Packet Y (r+1))(U:Packet Y (s+1)):
    Packet.splice (row q T) (row q U)=row q (Packet.splice T U):=by
  funext z
  unfold Packet.splice row
  dsimp only
  rw [←q.tsum_eq (fun x=>lace T U (cutLeft (q ∘ z)) (cutRight (q ∘ z)) x)]
  apply tsum_congr
  intro x
  simp only [lace,cons]
  rfl

theorem knot (K:Layer Y Y)(T:Packet Y (r+1))(U:Packet Y (s+1)):
    Packet.knot (line q K) (row q T) (row q U)=row q (Packet.knot K T U):=by
  unfold Packet.knot;rw [ray,splice]

end YM.Integration.WilsonIndependentConditionalCoordinateHeat
