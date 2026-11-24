import YangMills.WilsonProof.NativeSupport.JointDatedMask
import YangMills.WilsonProof.NativeSupport.JointTerminalDirection

/-! Ordinary evaluation of a square-zero polynomial on disjoint date
alphabets. The disjointness is essential for multiplicativity. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.JointShadow
open Function Finset Marker Packet Extra.Trajectories
open scoped Classical BigOperators
variable {V J:Type} [Fintype V] [DecidableEq V]
local notation "B" => Stock.census V
def openAt (a:V → ℂ) (P:Poly B) : ℂ:=∑ s:Finset V,(∏ i∈s,a i)*P.part (tag s)
def confined (A:Finset V) (P:Poly B):Prop:=∀ s:Finset V,P.part (tag s) ≠ 0 → s ⊆ A

theorem open_send (a:V → ℂ) (s:Finset V) (c:ℂ):openAt a (Poly.send (tag s) c)=(∏ i∈s,a i)*c := by
  unfold openAt
  rw [sum_eq_single s]
  · rw [Poly.part_send,if_pos rfl]
  · intro t _ ne
    rw [Poly.part_send,if_neg (fun eq=>ne (congrArg Subtype.val eq)),mul_zero]
  · simp

theorem open_sum (a:V → ℂ) (p:Finset J) (F:J → Poly B):openAt a (∑ k∈p,F k)=∑ k∈p,openAt a (F k) := by
  simp only [openAt,Poly.part_sum,mul_sum]
  rw [sum_comm]

theorem open_scalar (a:V → ℂ) (z:ℂ) (P:Poly B):openAt a (z • P)=z*openAt a P := by
  unfold openAt
  rw [mul_sum]
  apply sum_congr rfl
  intro s _
  rw [Poly.part_smul]
  ring

theorem open_diagonal (a b:V → ℂ) (P:Poly B):openAt a (diagonal b P)=openAt (fun i=>a i*b i) P := by
  apply sum_congr rfl
  intro s _
  rw [on_part,prod_mul_distrib,mul_assoc]

theorem confined_iff (A:Finset V) (P:Poly B):confined A P ↔ diagonal (only A) P=P := by
  constructor
  · intro h
    ext q
    change (diagonal (only A) P).part (tag q.val)=_
    rw [mask_part]
    by_cases yes:q.val ⊆ A
    · rw [if_pos yes]
    · rw [if_neg yes];exact (not_ne_iff.mp (fun nz=>yes (h _ nz))).symm
  · intro h s nz
    have own:=congrArg (fun Q:Poly B=>Q.part (tag s)) h
    change (diagonal (only A) P).part (tag s)=P.part (tag s) at own
    rw [mask_part] at own
    by_contra no
    rw [if_neg no] at own
    exact nz own.symm

theorem open_on (a b:V → ℂ) (A:Finset V) (P:Poly B) (h:confined A P) (same:∀ i∈A,a i=b i) :
    openAt a P=openAt b P := by
  apply sum_congr rfl
  intro s _
  by_cases nz:P.part (tag s)=0
  · rw [nz,mul_zero,mul_zero]
  · rw [prod_congr rfl (fun i hi=>same i (h s nz hi))]

private theorem resolution (P:Poly B):(∑ s:Finset V,Poly.send (tag s) (P.part (tag s)))=P := by
  ext p
  rw [Poly.part_sum,sum_eq_single p.val]
  · rw [Poly.part_send,if_pos (show p=tag p.val from rfl)]
  · intro t _ ne
    rw [Poly.part_send,if_neg (fun eq=>ne (congrArg Subtype.val eq).symm)]
  · simp

private theorem open_separated (a:V → ℂ) (P Q:Poly B) (A D:Finset V) (apart:Disjoint A D)
    (p:confined A P) (q:confined D Q) : openAt a (P*Q)=openAt a P*openAt a Q := by
  let f (s:Finset V):=Poly.send (tag s) (P.part (tag s))
  let g (s:Finset V):=Poly.send (tag s) (Q.part (tag s))
  have z (s:Finset V):Poly.send (tag s) (0:ℂ)=0:=by ext j;rw [Poly.part_send];split <;> rfl
  have pair (s t:Finset V):openAt a (f s*g t)=openAt a (f s)*openAt a (g t) := by
    dsimp only [f,g]
    rw [open_send,open_send]
    by_cases ps:P.part (tag s)=0
    · simp only [ps,z,zero_mul,mul_zero,openAt,Poly.part_nil,sum_const_zero]
    by_cases qt:Q.part (tag t)=0
    · simp only [qt,z,mul_zero,openAt,Poly.part_nil,sum_const_zero]
    have d:=apart.mono (p s ps) (q t qt)
    rw [tagged_mul _ _ (tag (s∪t)) ⟨d,rfl⟩,open_send,prod_union d]
    ring
  calc
    _ = openAt a ((∑ s,f s)*(∑ t,g t)) := congrArg (openAt a) (congrArg₂ (·*·) (resolution P).symm (resolution Q).symm)
    _ = ∑ s,∑ t,openAt a (f s*g t) := by simp_rw [sum_mul,mul_sum,open_sum]
    _ = (∑ s,openAt a (f s))*(∑ t,openAt a (g t)) := by simp_rw [pair,sum_mul,mul_sum]
    _ = _ := by rw [←open_sum,←open_sum,resolution,resolution]

variable [DecidableEq J]
theorem open_plant (a:V → ℂ) (P:Poly B) (A:Finset V) (p:confined A P) (b:J → V) (c:J → ℂ)
    (inject:Injective b) (F:Finset J) (free:∀ j∈F,b j∉A) :
    openAt a (P*∏ j∈F,(1+Poly.send ((Stock.census V).fire (b j)) (c j)))=
    openAt a P*∏ j∈F,(1+a (b j)*c j) := by
  let z (j:J):Poly B:=1+Poly.send ((Stock.census V).fire (b j)) (c j)
  have letter (j:J) (S:Finset V) (hit:b j∈S):diagonal (only S) (z j)=z j := by
    change diagonal _ (1+Poly.send (tag {b j}) _)=_
    rw [map_add,map_one,on_monomial,prod_singleton,only,if_pos hit,one_smul]
    rfl
  have no (j:J) : openAt a (z j)=1+a (b j)*c j := by
    have one:openAt a (1:Poly B)=1 := by
      change openAt a (Poly.send (tag ∅) 1)=1
      rw [open_send,prod_empty,one_mul]
    change openAt a (1+Poly.send (tag {b j}) (c j))=_
    rw [show ∀ P Q:Poly B,openAt a (P+Q)=openAt a P+openAt a Q from
      fun P Q=>by simp only [openAt,Poly.part_plus,mul_add,sum_add_distrib],one,open_send,prod_singleton]
  induction F using Finset.induction with
  | empty => simp
  | @insert j F hj ih =>
    let A':=A∪F.image b
    let Q:=P*∏ i∈F,z i
    have sj:b j∉A' := by
      rintro mem
      rcases mem_union.mp mem with d|d
      · exact free j (mem_insert_self ..) d
      · obtain ⟨k,hk,e⟩:=mem_image.mp d;exact hj ((inject e) ▸ hk)
    have old:confined A' Q := by
      apply (confined_iff ..).2
      have ok:confined A' P:=fun t nt=>(p t nt).trans subset_union_left
      dsimp only [Q]
      rw [map_mul,map_prod,(confined_iff _ _).1 ok]
      exact congrArg (fun v:Poly B=>P*v) (prod_congr rfl fun i hi=>letter i A' (mem_union_right _ (mem_image_of_mem _ hi)))
    have single:confined {b j} (z j):=(confined_iff ..).2 (letter j _ (mem_singleton_self _))
    rw [prod_insert hj,prod_insert hj,show P*(z j*∏ i∈F,z i)=Q*z j by dsimp only [Q];ring,
      open_separated a Q (z j) A' {b j} (disjoint_singleton_right.mpr sj) old single,no]
    rw [show openAt a Q=openAt a P*∏ i∈F,(1+a (b i)*c i) from ih (fun i hi=>free i (mem_insert_of_mem hi))]
    ring

end YM.Integration.InletSusceptibility.JointShadow
