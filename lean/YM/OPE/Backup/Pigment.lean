import YM.OPE.Backup.Karat
/-! # Relabelling after heading on several comparison columns

Marker map relation can fuse ANY linear comparison (budgets on complete
joint Play). Also retrieval on ONE branch of the same Poly for detector use.
Use plain ring hom on all-polys. Bud rules need only cover lifts of admissible
monomial with nonzero weights; thus pressure backgrounds agree across
comparison copies.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Muster
open Function Filter Finset Lattice RG Wilson Pressure MeasureTheory
open Push Marker Accent Menu Extra.Multi Extra.Trajectories Ribbon Source
open Extra.Histories PhysicalNext.Repeat Lotus GridApprox.Nil OPE.Backup
open scoped Topology BigOperators Classical
variable {I J : Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]
local notation "X"=> (Bud I)
local notation "Y"=> (Bud J)
variable (A:I→J) (s:I→ℂ)
namespace Pigment
def batch (p:(Bud I).Mode) : (Bud J).Mode := ⟨p.val.image A,mem_univ _⟩
def mark (p:(X).Mode) := ∏ i∈p.val, Poly.send ((Y).fire (A i)) (s i)
def budgetMap (F:Poly (Bud I)) : Poly (Bud J):= ∑ i:(X).Mode,F.part i • mark A s i -- pipe syntax
private lemma factor (F:Poly (Bud I))(p) : (budgetMap A s F).part p= ∑ i:(X).Mode,F.part i*(mark A s i).part p:= by unfold budgetMap; simp_rw [Poly.part_sum,Poly.part_smul]

def homL : Poly (Bud I)→L[ℂ] Poly (Bud J):= LinearMap.toContinuousLinearMap ({
    toFun:= budgetMap A s
    map_add':= fun a b=>by simp_rw [budgetMap,Poly.part_plus,add_smul,sum_add_distrib]
    map_smul':= fun a b=>by change budgetMap A s (a • b)=a • budgetMap A s b; simp_rw [budgetMap,Poly.part_smul,mul_smul,Finset.smul_sum] } : Poly (Bud I)→ₗ[ℂ] Poly (Bud J))
local notation "F"=> homL A s
lemma hom_eq (p:Poly X): F p=budgetMap A s p:=rfl
lemma part_of (p:Poly X)(x): (F p).part x=∑ i:(X).Mode,p.part i * (mark A s i).part x:= factor A s p x
lemma sent (p:(Bud I).Mode)(x:ℂ) : F (Poly.send p x)= x • mark A s p := by
   rw [hom_eq]; unfold budgetMap; rw [sum_eq_single p]; rotate_left
   · intro i _ hi; rw [Poly.part_send,if_neg hi,zero_smul]
   · simp
   simp
lemma fires (i:I) (x:ℂ) : F (Poly.send (X|>.fire i) x) = Poly.send ((Y).fire (A i)) (s i*x):=by
   rw [sent,mark,(show (X|>.fire i).val={i} from rfl),prod_singleton,Menu.sent,mul_comm]
lemma one : F 1=1:=by change F (Poly.send (X|>.quiet) 1)=_; rw [sent,mark]; change _ • (∏ i∈ (∅:Finset I),_) = _; simp
lemma mates (x y:(Bud I).Mode)(a b:ℂ) : F ((Poly.send x a)*(Poly.send y b))= F (Poly.send x a) * F (Poly.send y b) := by
   by_cases h: Disjoint x.val y.val
   · let z:(Bud I).Mode:=⟨x.val∪y.val,mem_univ _⟩; rw [tagged_mul x y z ⟨h,rfl⟩, sent,sent,sent,smul_mul_smul_comm]; congr 1; exact prod_union h
   have he : Poly.send x a * Poly.send y b=0:=not_not.mp (mt merges_of_tagged_mul (by rintro ⟨i,hh,ht⟩; exact h hh)); rw [he,map_zero,sent,sent,smul_mul_smul_comm]; obtain ⟨i,hx,hy⟩:=not_disjoint_iff.mp h; let z (i:I):=Poly.send ((Y).fire (A i)) (s i); let x' :=∏ j∈ x.val.erase i,z j; let y':=∏ j∈ y.val.erase i,z j
   have hZ:z i*z i = 0:=not_not.mp (mt merges_of_tagged_mul (by rintro ⟨j,hk,ht⟩; exact Finset.disjoint_left.mp hk (mem_singleton_self (A i)) (mem_singleton_self _)))
   rw [show mark A s x=z i*x' from (mul_prod_erase _ z hx).symm,show mark A s y=z i*y' from (mul_prod_erase _ z hy).symm, mul_mul_mul_comm,hZ]; simp
lemma preserves (p q:Poly X) : F (p*q)=F p*F q:=by
   rw [← Poly.studs p,← Poly.studs q]; simp_rw [Finset.mul_sum,Finset.sum_mul,map_sum,mates]
   rw [Finset.mul_sum]; simp_rw [Finset.sum_mul]
lemma preserves_pow (p:Poly X)(n:ℕ) : F (p^n)= F p^n:=by induction n with
   | zero=> simpa using one A s
   | succ n ih=>rw [pow_succ,pow_succ,preserves,ih]
lemma preserves_prod {ι:Type*}(t:Finset ι)(p:ι→Poly X) : F (∏ i∈t,p i)=∏ i∈t,F (p i):=by induction t using Finset.induction_on with
   | empty=>simpa using one A s
   | @insert i t hi ih=>rw [prod_insert hi,prod_insert hi,preserves,ih]
lemma symbol (p:(Bud I).Mode) : mark A s p= if Set.InjOn A p.val then Poly.send (batch A p) (∏ i∈p.val,s i) else 0 := by
   let u i:=(Y).fire (A i); have he:Fits u p.val ↔ Set.InjOn A p.val:=by
      constructor
      · intro ht i hi j hj hh; by_contra hx; exact disjoint_left.mp (ht.1 hi hj hx) (mem_singleton_self (A i)) (hh.symm ▸ mem_singleton_self _)
      intro hx; refine ⟨fun i hi j hj hz=>Finset.disjoint_left.mpr ?_,mem_univ _⟩; intro k h₁ h₂; exact hz (hx hi hj ((mem_singleton.mp h₁).symm.trans (mem_singleton.mp h₂)))
   split
   next hz=> refine (tagged_prod u p.val (he.mpr hz) s).trans ?_; apply congr_arg (fun i=> Poly.send i _); apply Subtype.ext; ext; simp [eq_comm,unionTag,u,Census.fire,batch]
   next hz=> exact not_not.mp (fun hx=>hz (he.mp (fits_of_tagged_prod u hx)))
lemma remembered (p:(Bud I).Mode) {i} (he:(mark A s p).part i ≠ 0): Set.InjOn A p.val ∧ i=batch A p ∧ ∀ i∈ p.val,s i ≠ 0:=by
   rw [symbol] at he; split at he; swap; · exact (he rfl).elim
   next h=> rw [Poly.part_send] at he; split at he; next hi=> exact ⟨h,hi,fun i hi hx=> he (prod_eq_zero hi hx)⟩
            contradiction -- indentation
lemma cardinal (p) {i} (he:(mark A s p).part i ≠ 0): i.val.card=p.val.card:= by obtain ⟨hh,rfl,_⟩:= remembered A s p he; exact card_image_of_injOn hh -- `rfl` which?
lemma source_lit (x:Poly X)(i) (he: (F x).part i≠0):∃ p:(Bud I).Mode,x.part p≠0 ∧ (mark A s p).part i≠0:=by
    rw [part_of] at he; obtain ⟨p,-,hp⟩:= Finset.exists_ne_zero_of_sum_ne_zero he; exact ⟨p,left_ne_zero_of_mul hp,right_ne_zero_of_mul hp⟩
lemma highly (p:Poly X)(hp:rises p) : rises (F p):=fun i hi=> by
   obtain ⟨q,hq,hX⟩:=source_lit A s p i hi; rw [cardinal _ _ _ hX]; exact hp q hq
lemma quiet (p:Poly X)(hp:p.part (X|>.quiet)=0): (F p).part (Y|>.quiet)=0:=by
   by_contra hx; obtain ⟨i,hi,hx⟩:=source_lit A s p _ hx; have he:=cardinal _ _ _ hx; exact hi ((show i= (X|>.quiet) from Subtype.ext (card_eq_zero.mp he.symm)) ▸ hp)
private lemma pass_long {I:Type}[Fintype I][DecidableEq I](p:Poly (Bud I))(he:p.part (Bud I|>.quiet)=0)(n:ℕ)(ht:Fintype.card I≤n): Poly.pass p=∑ i∈range (n+1),(i.factorial:ℂ)⁻¹ • p^i:=by
    induction ht with
    | refl=>rfl
    | @step n ht ih=> rw [sum_range_succ, Poly.stops p he (n+1) (Nat.lt_succ_of_le ht),smul_zero,add_zero]; exact ih
lemma passes (p:Poly X) (hp:p.part (X|>.quiet)=0): F (Poly.pass p)= Poly.pass (F p):= by
   let n:=max (Fintype.card I) (Fintype.card J); rw [pass_long p hp n (le_max_left ..),pass_long (F p) (quiet A s p hp) n (le_max_right ..),map_sum]; simp_rw [map_smul,preserves_pow]
lemma pushes {G:Gauge}{c f:Side}(S:StepData c f)(μ:ℝ)(U:Config G c){p:Config G f→Poly X}(hK:S.IsKernel μ G)(h:Integrable p (prior G _)) : F (S.push μ p U)= S.push μ (F ∘ p) U:=by
   unfold StepData.push; let L:=(F).restrictScalars ℝ; have hh:= L.integral_comp_comm (StepData.push_slice hK U p h); simp_rw [map_smul] at hh; exact hh.symm
lemma matching (L:Ward X) (T:Ward Y) (p q:Poly X)(hp:L.Writes p q) (h:∀ i:(Bud I).Mode,T.ready (batch A i)→ Set.InjOn A i.val → (∀ j∈i.val,s j ≠ 0) →L.ready i): T.Writes (F p) (F q):=by
   intro i hi; rw [part_of,part_of]; refine sum_congr rfl fun j _=> ?_; by_cases hh:(mark A s j).part i=0; · rw [hh,mul_zero,mul_zero]
   obtain ⟨hx,hξ,he⟩:= remembered A s j hh; rw [hp j (h _ (hξ ▸ hi) hx he)]
end Pigment
end YM.MergeProof.Ribbons.ManyCopies.Muster
