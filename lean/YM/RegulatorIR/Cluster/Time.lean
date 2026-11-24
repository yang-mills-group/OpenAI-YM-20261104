import YM.RegulatorIR.Cluster.Combine
import YM.RegulatorIR.Cluster.Air

/-! Last-polynomial step at full heat time. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Cluster
open MvPolynomial Function Budget Budget.Packet Budget.Layer Budget.Tuple Diagram Diagram.Interval Gradient Train Finset Filter Brief
open scoped BigOperators Topology ENNReal NNReal Classical
variable {X Y Z:Type}{a b r p e n:ℕ}

def Remains (T:Rhythm X)(s:ℕ→ℕ): Prop:=∀ k e, s e<k→∀ j,T k e j=0
lemma remain_rank {a b:ℕ}(T U:Rhythm X) (ht:Remains T (fun e=>a+3*e))(hu:Remains U (fun e=>b+3*e)): Remains (composeT T U) (fun e=> a+b+3*e):=by
 intro k e h r; by_contra! hv
 obtain ⟨i,hi,H⟩:= Finset.exists_ne_zero_of_sum_ne_zero hv; obtain ⟨j,hj,he⟩:= Finset.exists_ne_zero_of_sum_ne_zero H; obtain ⟨s,_,hf⟩:= Finset.exists_ne_zero_of_sum_ne_zero he
 obtain ⟨_,hf,hg⟩:= pie_comes _ _ _ _ hf; have ha:¬ a+3*j.1 < i.1:=fun h=>hf (ht _ _ h _); have hh:¬ b+3*j.2 < i.2:=fun h=>hg (hu _ _ h _); have hp:= mem_antidiagonal.mp hi;have hm:=mem_antidiagonal.mp hj;dsimp only at h;omega

namespace Brief
variable {T U:Rhythm X}
lemma markend (K:Layer X X)(V W:Orders X)(h:Vacuum V)(b:Bool)(ht:Ranks a W): Remains (markHeat K (logHeat K V b) W) (fun e=> a+3*e):= fun k e he r=> Classical.byContradiction (fun hd=> by have := (marked_cap a K V h W ht _ e r k hd).2; dsimp only at he;omega)
lemma rem_tile (f:Y↪X){c:ℕ→ℕ}(T:Rhythm X)(h:Remains T c):Remains (restrictT f T) c:= fun k e he j=>by unfold restrictT; rw [h k e he j]; rfl
lemma heated_ranks (T:Rhythm X)(h:∀ t e,Within (e+a) (T t e))(c:ℕ→ℕ): Ranks a (heated c T):=by intro e r he; obtain ⟨i,_,hp⟩:=Finset.exists_ne_zero_of_sum_ne_zero he; exact h i e r hp
lemma heated_sym (T: Rhythm X)(h:∀ t,gradedSymmetric (T t))(c:ℕ→ℕ): gradedSymmetric (heated c T):=fun e r=>symmetric_sum (fun i _=> h i e r)
variable [Fintype X]
private lemma printed_heats {Q:EPS X}(c:ℕ→ℕ)(h:Reads a T Q)(hh:Remains T c) : printed a (heated c T)= PowerSeries.map (Polynomial.evalRingHom 1) Q:=by
 ext1 e; rw [PowerSeries.coeff_map,printed, PowerSeries.coeff_mk]
 have he : PowerSeries.coeff e Q=∑ i∈range (c e+1), Polynomial.monomial i (packed (T i e) (e+a)):= by
    ext1 i; simp_rw [h.score i e,Polynomial.finsetSum_coeff]; by_cases hv:i∈range (c e+1)
    · simp only [Polynomial.coeff_monomial, Finset.sum_ite_eq',hv,ite_true]
    have hp: ¬ i<c e+1:=fun hi=>hv (mem_range.mpr hi)
    simp [Polynomial.coeff_monomial, hh i e (by omega),hp,packed]
 rw [he,map_sum,show heated c T e= ∑ i∈range (c e+1),T i e by ext1; simp [heated,Finset.sum_apply], pack_sum]; simp

private lemma heat_print (T U: Rhythm X) {d g:ℕ}(h:Brief a T)(hh: Brief b U) (ht:Remains T (fun e=> d+3*e))(hv: Remains U (fun e=> g+3*e)):
 heated (fun e=>d+g+3*e) (composeT T U)=accord (heated (fun e=>d+3*e) T) (heated (fun e=>g+3*e) U):=by
 obtain ⟨f,F⟩:= h.readable; obtain ⟨z,H⟩:=hh.readable
 have hQ:=Reads.composition F H
 apply printed_equal (heated_ranks _ hQ.ranks _) (rank_pair (heated_ranks _ h.ranks _) (heated_ranks _ hh.ranks _)) (heated_sym _ (compose_sym T U) _) (accord_sym _ _)
 rw [print_mul (heated_ranks _ h.ranks _) (heated_ranks _ hh.ranks _),printed_heats _ hQ (remain_rank T U ht hv),printed_heats _ F ht, printed_heats _ H hv,map_mul]
omit [Fintype X] in
lemma time_once (T U:Rhythm X) {d g:ℕ}(h: Brief a T)(hh:Brief b U)(ht:Remains T (fun e=>d+3*e))(hv:Remains U (fun e=>g+3*e)): heated (fun e=>d+g+3*e) (composeT T U)=accord (heated (fun e=>d+3*e) T) (heated (fun e=>g+3*e) U):=by
 have h' (F:Finset X)(e i) (Q:Rhythm X) c: crop (tile F) (heated c Q e i) = heated c (restrictT (tile F) Q) e i:=by rw [heated,crop_sum];rfl
 have H (F:Finset X) e i: crop (tile F) (heated (fun e=>d+g+3*e) (composeT T U) e i)=crop (tile F) (accord (heated (fun e=>d+3*e) T) (heated (fun e=>g+3*e) U) e i):=by
   rw [crop_orders,h',trim_twice]; simp_rw [h'];rw [heat_print _ _ (trim _ h) (trim _ hh) (rem_tile _ _ ht) (rem_tile _ _ hv)]
 ext1 e;ext1 r;ext1 x
 exact congr_fun (H (univ.image x) e r) (fun i=>⟨x i, mem_image_of_mem x (mem_univ i)⟩)
end Brief
end YM.RegulatorIR.Cluster
