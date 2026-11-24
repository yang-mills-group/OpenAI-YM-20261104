import YM.PertExtension.SymbolMatch

/-! Elementary orthogonal projection identity counting only positive plaquette orientations. -/
noncomputable section
set_option autoImplicit false
namespace YM.PertExtension.LatticePT.Air
open Function Finset Lattice
open scoped Topology BigOperators Classical NNReal
abbrev Ribbon := Axis → ℂ
def wedge (u v : Ribbon) (i j) := u i * v j - u j * v i

theorem half (U : Axis×Axis→ ℂ)(h:∀ i j,U (i,j)=U (j,i))(hz:∀ i,U (i,i)=0) :
    (∑ p : Axis×Axis, U p)=(2:ℂ)*∑ p:PlaqAxes,U p.val :=by
    let W:= Axis×Axis;let S:Finset W:= Finset.univ
    let p(s:W):Prop:=s.1<s.2
    let A:=S.filter p
    let B:=S.filter (fun v=>p v.swap)
    let C:=∑ v∈ A,U v
    have hf : ∑ v∈ B, U v=C:= by
       have hs v: v∈ B ↔ v.swap∈A:= by dsimp [A,B,S];simp
       have he:Bijective (Prod.swap (α:=Axis) (β:=Axis)):= ⟨Prod.swap_injective,Prod.swap_surjective⟩
       exact sum_bijective Prod.swap he hs fun v _=> h v.1 v.2
    have hc:= sum_add_sum_compl A U
    have hB:∑ v∈ Aᶜ,U v=∑ v∈ B,U v:= by
        symm; apply Finset.sum_subset (show B ⊆ Aᶜ from fun i hi=> Finset.mem_compl.mpr (fun ht=> lt_asymm (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp ht).2))
        intro i hi h; apply (eq_or_ne i.1 i.2).elim
        · intro he; change _=0; exact (congr_arg U (show i=(i.1,i.1) from Prod.ext rfl he.symm)).trans (hz i.1)
        intro he; obtain h'|h':=he.lt_or_gt
        · exact (Finset.mem_compl.mp hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h'⟩)).elim
        exact (h (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h'⟩)).elim
    have Hv : C=∑ i: PlaqAxes,U i.val := Finset.sum_subtype A (by simp [A,S,p]) U
    rw [hf] at hB; rw [two_mul,← hc,hB,←Hv]

-- inclusion in complement

theorem double (d t z w : Ribbon) :
    ∑ p: PlaqAxes,(wedge d z p.val.1 p.val.2)*(wedge t w p.val.1 p.val.2)= ∑ i:Axis,∑ j:Axis,z j*(d i*(t i*w j-t j*w i)):= by
   let f (p:Axis×Axis):=wedge t w p.1 p.2
   have h (i j): f (j,i)= -f (i,j):=by unfold f wedge; ring
   let U (p:Axis×Axis):= (wedge d z p.1 p.2) * (wedge t w p.1 p.2)
   let V (p:Axis×Axis):= z p.2 *(d p.1 * f p)
   have hu i j : U (i,j)=U (j,i):=by unfold U wedge; dsimp only;ring
   have he := half U hu (fun i=>by dsimp [U,wedge]; ring)
   have hv (i j:Axis): U (i,j)= V (i,j)+V (j,i):= by unfold U V f wedge;dsimp only;ring
   have hr: (∑ p:Axis×Axis,U p)= ∑ i,∑ j, U (i,j):= Fintype.sum_prod_type U
   let a:= ∑ p:PlaqAxes,U p.val
   have hh : (∑ i: Axis,∑ j: Axis,U (i,j))=(∑ i,∑ j,V (i,j))+(∑ i,∑ j,V (j,i)):=by simp only [hv,Finset.sum_add_distrib]
   change (∑ p:Axis×Axis,U p)=2*a at he
   rw [hr,hh] at he
   let b:=∑ i,∑ j,V (i,j);let b':=∑ i,∑ j,V (j,i)
   change b+b'=2*a at he
   change a=b
   have ht:b=b':=Finset.sum_comm
   apply mul_left_cancel₀ (a:=(2:ℂ)) two_ne_zero (he.symm.trans ?_);rw [←ht];ring

def brief (t : Ribbon)(μ ν:Axis)(i:Axis):ℂ:=(if i=ν then t μ else 0) - if i=μ then t ν else 0
lemma single (k i:Axis)(c:ℂ) : (if i=k then c else 0)=Pi.single (M:=fun _=>ℂ) k c i := by by_cases h:i=k; subst k; simp;rw [if_neg h, Pi.single_eq_of_ne h]
lemma selects (k : Axis) (T : Ribbon)(c:ℂ) : ∑ i:Axis,(if i=k then c else 0) * T i=c*T k := by rw [sum_eq_single_of_mem k (mem_univ k) (fun i _ h=>by simp [h])]; simp
lemma drops (t T:Ribbon)(μ ν:Axis) : (∑ j,brief t μ ν j*T j)=(t μ*T ν - t ν*T μ):= by unfold brief;simp_rw [sub_mul,Finset.sum_sub_distrib,selects]
lemma vanished (t : Ribbon) (μ ν:Axis) : (∑ j,brief t μ ν j*t j)=0:= by rw [drops];ring
lemma expands (d t w:Ribbon)(μ ν:Axis) :
    ∑ p: PlaqAxes,(wedge d (brief t μ ν) p.val.1 p.val.2)*(wedge t w p.val.1 p.val.2) = (∑ i:Axis,d i*t i) * (t μ*w ν-t ν*w μ) := by
  let z:=brief t μ ν
  have he : ∀ (T:ℂ),∑ i:Axis,d i*(t i * T)=(∑ i:Axis,d i*t i)*T:=by
     intro T; rw [Finset.sum_mul];simp_rw [mul_assoc]
  rw [double];change (∑ i:Axis,∑ j:Axis,z j*(d i*(t i*w j-t j*w i)))=_
  have hc i j:z j*(d i*(t i*w j-t j*w i))= (z j*w j)*(d i*t i)- (z j*t j)*(d i*w i):=by ring
  simp_rw [hc,Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [← Finset.mul_sum,← Finset.mul_sum];dsimp only [z];rw [vanished,drops,zero_mul,sub_zero,mul_comm]

end YM.PertExtension.LatticePT.Air
