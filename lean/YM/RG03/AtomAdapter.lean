import YM.RG03.Aggregate

/-!
# Raw circuit words vs actual `RG.Atom` and signed channels

Current results compare path factors at the same U; no change of representation is inferred by
just projecting independent full-group variables. For elementary positive slots the distinguished
value of k is precisely the projection of the transported *matrix defect*, although higher path
correction words may involve products inside this projection. Both orientation reversal in a pull
and inverse-link dependence at every intermediate site are retained.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG03.Square
open RG Wilson Boards Tight PathWords Next.Scheduling.Wages Lattice Function
open scoped Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{n:Side}{k:ℕ}

def slot (s:Slot): Circuit:=⟨s.walk,posDir s.plaq.val.1,posDir s.plaq.val.2⟩

lemma slotEval (s:Slot)(o:Site n)(U:Config G n): s.atSite U o = projector G ((slot s).defect o U) := by
  rw [hangs, Circuit.defect,map_sub, ← Path.picture]
  change projector G (G.mat (travel U o (detour s))) = projector G (G.mat (travel U o (detour s))) - _
  rw [show projector G (1:G.Mat)=G.curvature 1 from rfl,G.curvature_unit,sub_zero]
lemma projector_conjugated (h:G.El)(x:G.Mat) :
    projector G (G.mat h*x*G.mat h⁻¹) = G.adjoint h (projector G x) := by
  let S (y:G.Mat) := (1/2:ℝ)•(y-star y)
  change G.projectColor (S (G.mat h*x*G.mat h⁻¹))=_
  rw [show S (G.mat h*x*G.mat h⁻¹)=G.conjugate h (S x) from ?_,G.project_conjugate]
  · rfl
  unfold S Gauge.conjugate; simp [star_mul,G.mat_inv, mul_assoc, mul_sub,sub_mul]

def ledger (a:Atom G k): Board (Fin k) := fun j=>[slot (a.leg j)]
def colorLead (G:Gauge)(i:G.ColorIndex):G.Mat→ₗ[ℝ]ℝ := (EuclideanSpace.proj i).toLinearMap.comp (projector G).toLinearMap
def ticket (a:Atom G k): Token G ℝ (Fin k) := ∑ b:Fin k→_, a.coeff b • (MultilinearMap.mkPiAlgebra ℝ (Fin k) ℝ).compLinearMap
  (fun j=>colorLead G (b j))
lemma showTicket (a:Atom G k)(z:Fin k→G.Mat): ticket a z=a.poly (fun i=> projector G (z i)) := by
  unfold ticket Atom.poly
  simp only [_root_.sum_apply,_root_.smul_apply,smul_eq_mul, MultilinearMap.compLinearMap_apply,MultilinearMap.mkPiAlgebra_apply]
  rfl

lemma presentation (a:Atom G k)(U:Config G n)(o:Site n):
    a.unmasked U o=Boards.price (ticket a) (ledger a) o U := by
  unfold Atom.unmasked Boards.price; rw [showTicket]; congr 1
  exact funext (fun i=> by rw [slotEval]; congr 1; simp [arrayValue,ledger])
lemma invariant (a:Atom G k)(ha:a.Invariant) : Tight.Together (ticket a) := by
  intro u z; simp_rw [showTicket,projector_conjugated]; apply ha

-- Signed rotations for complete tuples

def bent (s:Signed)(c:Circuit):Circuit := ⟨c.prefix'.map (fun a=>a.rotate s),c.a.rotate s,c.b.rotate s⟩
lemma reverse_bent (s:Signed)(w:Walk) : Lattice.reverse (w.map (fun a=>a.rotate s))=(Lattice.reverse w).map (fun a=>a.rotate s) :=
  show _=_ from (by simp only [Lattice.reverse,← List.map_reverse,List.map_map]; exact List.map_congr_left fun i _=>i.rev_rotate s |>.symm)
lemma walk_bent (s:Signed)(c:Circuit) : (bent s c).path=c.path.map (fun a=>a.rotate s) := by
  unfold Circuit.path; simp [bent,List.map_append,oriented,Step.rev_rotate,reverse_bent]
lemma circuit_pulled (s:Signed)(c:Circuit)(o b:Site n)(U:Config G n) : c.defect o (pull s b U) = (bent s c).defect (affine s b o) U := by simp only [Circuit.defect,Circuit.raw,Circuit.holonomy,travel_pull,walk_bent]
lemma word_pulled (s:Signed)(q:Word)(o b:Site n)(U:Config G n): value q o (pull s b U) = value (q.map (bent s)) (affine s b o) U := by
   induction q <;> simp_all [circuit_pulled]
lemma array_pulled {ι E:Type*}[AddCommMonoid E][Module ℝ E](T:Token G E ι)(w:Board ι)(o:Site n)(U:Config G n)(s:Signed)(b:Site n):
    Boards.price T w o (pull s b U)=price T (fun i=>(w i).map (bent s)) (affine s b o) U := congr_arg T (funext fun _=>word_pulled ..)
lemma atom_pulled (a:Atom G k) (o:Site n)(U:Config G n)(s:Signed)(b:Site n):
    a.unmasked (pull s b U) o=Boards.price (ticket a) (fun i=>(ledger a i).map (bent s)) (affine s b o) U := by rw [presentation, array_pulled]
end YM.RG03.Square
