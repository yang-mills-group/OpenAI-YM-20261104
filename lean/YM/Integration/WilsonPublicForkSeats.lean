import YM.Integration.WilsonPublicForkRooms
import YM.OPE.Trees.Association

/-! The measured near roster, with its genuine distant field retained on both ordinary faces. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPublicForkSeats
open Function Finset Filter Set Table Spec OPE OPE.Arboreal OPE.Prescription
open WilsonPublicForkGeometry WilsonPublicForkGeometry.Node WilsonPublicForkRooms
open scoped Classical Topology BigOperators
variable {I:Type} [Fintype I]
def tip (I:Type):Finset (Node I):={far}
private def soleSeat (I:Type):(↥(tip I)⊕Fin 0)≃Unit where
  toFun:=fun _=>()
  invFun:=fun _=>.inl ⟨far,by simp [tip]⟩
  left_inv:=fun j=>by
    rcases j with ⟨a,ha⟩|a
    · have eq:a=far:=by simpa [tip] using ha
      subst a;rfl
    · exact a.elim0
  right_inv:=fun j=>by cases j;rfl
def bare {V:Type}:Fin 0→V:=Fin.elim0
omit [Fintype I] in
private lemma seated {T V:Type}(f:T→V)(g:Node I→V):
    (beside f (sole (g far))) ∘ Equiv.sumCongr (Equiv.refl T) (soleSeat I)=
      beside f (beside (crop g (tip I)) (bare:Fin 0→V)):=by
  funext o
  rcases o with i|(⟨j,hj⟩|j)
  · rfl
  · have h:j=far:=by simpa [tip] using hj
    subst j;rfl
  · exact j.elim0
variable {G:Gauge}{L:Register G}{S A:Table L}{Q:DiffPlan S}
omit [Fintype I] in
theorem returned {T:Type}[Fintype T](ha:A.Symmetric)(p:T→L.Token)(x:T→E4)(q:Node I→L.Token)(X:Node I→E4)
    (hx:Injective (beside x (sole (X far)))):
    observe A (beside x (beside (crop X (tip I)) (bare:Fin 0→E4)))
      (beside p (beside (crop q (tip I)) (bare:Fin 0→L.Token)))=
      observe A (beside x (sole (X far))) (beside p (sole (q far))):=by
  have seen:=OPE.perm_observe A ha (Equiv.sumCongr (Equiv.refl T) (soleSeat I)) (beside p (sole (q far))) hx
  rwa [seated,seated] at seen

omit [Fintype I] in
private lemma withEmpty {b:Finset (Node I)} {X:Node I→E4}(h:Injective (crop X b)):
    Injective (beside (crop X b) (bare:Fin 0→E4)):=by
  exact beside_distinct.mpr ⟨h,fun i=>i.elim0,fun _ j=>j.elim0⟩

theorem full (ha:A.Symmetric)(p:Node I→L.Token)(X:Node I→E4)
    (hc:Injective (crop X (frame I).leaves))(hh:Injective (beside (crop X (near I)) (sole (X far)))):
    whole A (frame I).leaves X p (bare:Fin 0→E4) bare=
      observe A (beside (crop X (near I)) (sole (X far))) (beside (crop p (near I)) (sole (p far))):=by
  have union:near I∪tip I=(frame I).leaves:=by rw [WilsonPublicForkGeometry.leaves];ext u;simp [tip,or_comm]
  have separate:Disjoint (near I) (tip I):=by
    rw [Finset.disjoint_left];intro u hu hv
    have e:u=far:=by simpa [tip] using hv
    subst u;exact other_near.2.2 hu
  rw [logs_combine (a:=near I) (b:=tip I) (c:=(frame I).leaves) (p:=p) (q:=bare) A ha
    (by ext i;simpa only [Finset.mem_union] using Finset.ext_iff.mp union i) separate (withEmpty hc)]
  exact returned ha (crop p (near I)) (crop X (near I)) p X hh

theorem cut (P:Prescription Q)(ha:A.Symmetric)(p:Node I→L.Token)(X:Node I→E4)(w:Mode Q)
    (hc:Injective (crop X (outer I)))(hh:Injective (beside (sole (X child)) (sole (X far)))):
    whole A (outer I) X (update p child (P.letter w)) (bare:Fin 0→E4) bare=
      observe A (beside (sole (X child)) (sole (X far))) (beside (sole (P.letter w)) (sole (p far))):=by
  have union:insert child (tip I)=outer I:=rfl
  have distinct:(child:Node I)∉tip I:=by simp [tip]
  have ret:=one_combine (p:=p) (w:=w) (q:=bare) (i:=(child:Node I)) (b:=tip I) (c:=outer I) A ha P
    (by ext i;simpa only [Finset.mem_insert] using Finset.ext_iff.mp union i) distinct (withEmpty hc)
  refine Eq.trans ?_ (ret.trans ?_)
  · congr 1
    funext i
    by_cases eq:i=child <;> simp [Function.update,eq]
  · exact returned ha (sole (P.letter w)) (sole (X child)) p X hh

theorem distinct {r t M δ:ℝ}{x:I→E4}{z:E4}(rp:0<r)(rt:r≤t)(dp:0<δ)
    (hx:∀i,‖x i‖≤M)(away:2*δ≤‖z‖)(sep:∀i j,i≠j→δ≤‖x i-x j‖)(gap:r*M≤t*δ):
    let X:=WilsonPublicForkGeometry.position r t x z
    Injective (crop X (frame I).leaves) ∧ Injective (beside (crop X (near I)) (sole (X far))) ∧
    Injective (crop X (outer I)) ∧ Injective (beside (sole (X child)) (sole (X far))):=by
  let X:=WilsonPublicForkGeometry.position r t x z
  have tp:=rp.trans_le rt
  have nz:0<‖z‖:=by linarith
  have outerDiff:X child≠X far:=Ne.symm (smul_ne_zero tp.ne' (norm_pos_iff.mp nz))
  have hit (u:Node I)(hu:u∈near I):X u≠X far:=by
    obtain ⟨i,hi⟩:=names (⟨u,hu⟩:↥(near I))
    change u=leaf i at hi;subst u
    intro eq
    have n:=congrArg norm eq
    change ‖r • x i‖=‖t • z‖ at n
    rw [norm_smul,norm_smul,Real.norm_of_nonneg rp.le,Real.norm_of_nonneg tp.le] at n
    have big:t*δ<t*‖z‖:=mul_lt_mul_of_pos_left (by linarith) tp
    exact big.not_ge ((n ▸ mul_le_mul_of_nonneg_left (hx i) rp.le).trans gap)
  have innerInj:Injective (crop X (near I)):=by
    intro u v eq
    by_contra ne
    have dist:=(WilsonPublicForkRooms.inner (t:=t) (z:=z) rp hx sep).2 u v ne
    change δ*r≤‖crop X (near I) u-crop X (near I) v‖ at dist
    rw [eq,sub_self,norm_zero] at dist
    exact (mul_pos dp rp).not_ge dist
  have leafInj (i j:Node I)(hi:i∈near I)(hj:j∈near I)(eq:X i=X j):i=j:=
    congrArg Subtype.val (innerInj (a₁:=⟨i,hi⟩) (a₂:=⟨j,hj⟩) eq)
  refine ⟨?_,beside_distinct.mpr ⟨innerInj,fun _ _ _=>Subsingleton.elim ..,fun i _=>hit i.1 i.2⟩,?_,
    beside_distinct.mpr ⟨fun _ _ _=>Subsingleton.elim ..,fun _ _ _=>Subsingleton.elim ..,fun _ _=>outerDiff⟩⟩
  · rintro ⟨i,hi⟩ ⟨j,hj⟩ eq
    change X i=X j at eq; apply Subtype.ext
    rw [WilsonPublicForkGeometry.leaves,Finset.mem_insert] at hi hj
    rcases hi with rfl|hi <;> rcases hj with rfl|hj
    · rfl
    · exact ((hit j hj) eq.symm).elim
    · exact ((hit i hi) eq).elim
    · exact leafInj i j hi hj eq
  · rintro ⟨i,hi⟩ ⟨j,hj⟩ eq
    change X i=X j at eq; apply Subtype.ext
    rcases (by simpa [outer] using hi : i=child ∨ i=far) with rfl|rfl <;>
      rcases (by simpa [outer] using hj : j=child ∨ j=far) with rfl|rfl
    · rfl
    · exact (outerDiff eq).elim
    · exact (outerDiff eq.symm).elim
    · rfl

end YM.Integration.WilsonPublicForkSeats
