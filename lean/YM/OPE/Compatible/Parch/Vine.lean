import YM.OPE.Compatible.Emu.Wear
import YM.OPE.Compatible.Glow.Gear
/-!
# Real Banks. Varying periods, static charges, no β or period-dependent
height constants. Account in the UV field scale.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Claw
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Tensor Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Variance
variable {i j r d m k l:ℕ}
section
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
abbrev rank (g:E→F)(j:ℕ): E→F:= Tensor.diagonal (Tensor.coeff g j 0)
def Tall (f:E→F)(d:ℕ):Prop:=∃ P:ℕ→E→F,(∀ j≤d,∃ A:Tensor.T E F j,P j=diagonal A) ∧∀ x,f x=∑ j∈ range (d+1),P j x
lemma tall_of (p:(j:ℕ)→T E F j): Tall (fun i=>∑ j∈range (d+1),diagonal (p j) i) d:=⟨fun j=>diagonal (p j),fun j _=>⟨p j,rfl⟩,fun _=>rfl⟩
variable {f g:E→F}
namespace Tall
lemma tag {f:E→F}{k d:ℕ}(h:k≤d)(hf:f=rank f k): Tall f d:=by
        let Q(j:ℕ)(x:E):= if k=j then rank f k x else 0; refine ⟨Q,fun j _=>?_,fun x=>?_ ⟩
        · by_cases he:k=j; · subst j; exact ⟨Tensor.coeff f k 0,funext fun i=>if_pos rfl⟩
          exact ⟨0,funext fun x=>if_neg he⟩
        rw[sum_eq_single k]; exact (congr_fun hf x).trans (if_pos rfl).symm; exacts [fun b _ hb=>if_neg (Ne.symm hb),fun hs=>False.elim (hs (mem_range.mpr (by omega)))]
lemma stock (h:Tall f d) : ∃ P:(j:ℕ)→T E F j,f=∑ j∈range (d+1), diagonal (P j):=by
        obtain ⟨Q,hQ,hP⟩:=h; choose! D hD using hQ; refine ⟨D,funext fun i=>?_⟩; rw [Finset.sum_apply,hP]; exact sum_congr rfl fun j hj=> congr_fun (hD j (by have h:= mem_range.mp hj; omega)) _
lemma neat (h:Tall f d):ContDiff ℝ ω f:=by obtain ⟨P,hP⟩:= stock h; rw[hP]; rw [show (∑ j∈range (d+1),diagonal (P j))=(fun x=>∑ j∈range (d+1),diagonal (P j) x) from funext fun i=> Finset.sum_apply _ _ _]; apply ContDiff.sum; intro i _; exact Tensor.diag_smooth (P i) _ -- deprecated?
lemma mono (h:Tall f k)(hv:k≤d):Tall f d:=by
       obtain ⟨P,hP⟩:= stock h; let q(i:ℕ):= if i ≤ k then P i else 0; have he:f= fun x=>∑ i∈range (d+1),diagonal (q i) x:=by
            rw [hP]; funext x; rw[Finset.sum_apply]; apply (sum_congr rfl ?_).trans (Finset.sum_subset (f:=fun j=>Tensor.diagonal (q j) x) (Finset.range_mono (Nat.add_le_add_right hv 1)) ?_)
            · intro j hj; have he:j<k+1:= mem_range.mp hj; rw [show q j=P j from if_pos (by omega)]
            intro j hv hx; rw[show q j=0 from if_neg (fun h=> hx (mem_range.mpr (by omega)))]; rfl
       rw [he];apply tall_of
lemma bite (h:Tall f d)(hv:Tall g d):Tall (f-g) d:=by
       obtain ⟨P,hP⟩:= stock h; obtain ⟨Q,hQ⟩:=stock hv; have hl:f-g=fun x=>∑ i∈ range (d+1),diagonal (P i-Q i) x:=by
            rw [hP,hQ]; funext x; rw [Pi.sub_apply,Finset.sum_apply,Finset.sum_apply,← Finset.sum_sub_distrib];rfl
       rw [hl]; exact tall_of (fun i=>P i - Q i)
lemma bread0 : Tall (0:E→F) d:=by have ht:=tall_of (fun i=>(0:T E F i)) (d:=d); simpa [Tensor.diagonal] using! ht
lemma blend (h:Tall f d)(hv:Tall g d): Tall (f+g) d:=by rw [show f+g=f-(0-g) by simp]; exact bite h (bite bread0 hv)
lemma drop (h:ContDiff ℝ ω f)(he:∀ x:E,∀ t:ℝ,f (t • x)=(t^r) • f x): rank f k= if k=r then f else 0:=by
       funext x; unfold rank; rw[← WardBin.leading_tensor x f (h.contDiffAt.of_le le_top),show (fun t:ℝ=> f (t • x))= _ from funext (he x),WardBin.lead_monomial]; split_ifs <;>rfl
lemma homish(h:ContDiff ℝ ω f)(he:∀ x:E,∀ t:ℝ,f (t • x)=(t^r) • f x): Tall f r:=tag (k:=r) le_rfl ((drop h he).trans (if_pos rfl)).symm
lemma pint (h:ContDiff ℝ ω f)(he:∀ x:E,∀ t:ℝ,f (t • x)=(t^r) • f x): diagonal (Tensor.coeff f r 0)=f:= (drop h he).trans (if_pos rfl)
lemma loan (A:T E F k) (hp:k ≤ d):Tall (diagonal A) d:= (homish (diag_smooth A _) (homogeneous A)).mono hp
lemma sums {I:Type}(A:Finset I)(v:I→E→F)(h:∀ i∈A,Tall (v i) d):Tall (∑ i∈A,v i) d:=by
       induction A using Finset.induction_on with
       | empty=>rw[sum_empty];exact bread0
       | insert i s hi ih=>rw [sum_insert hi]; exact blend (h _ (mem_insert_self ..)) (ih (fun i hi=> h _ (mem_insert_of_mem hi)))
lemma scaled (t:ℝ)(h:Tall f d): Tall (t • f) d:=by obtain ⟨P,hP⟩:= stock h; let q(i:ℕ):=t • P i; rw [hP,Finset.smul_sum]; apply sums; exact fun i hi=> show Tall (diagonal (q i)) d from loan _ (by have ht:= mem_range.mp hi;omega)
lemma wing (P:(i:ℕ)→T E F i)(h:f=∑ i∈range (d+1),diagonal (P i))(j:ℕ): rank f j = if j ≤ d then diagonal (P j) else 0:=by
        rw [h]; funext x; rw[rank,Tensor.coeff_sum _ _ _ _ (fun i _=> (diag_smooth (P i) _).contDiffAt)]; unfold diagonal; rw [_root_.sum_apply]; let G(i:ℕ):= Tensor.diagonal (P i); have ht(i:ℕ): rank (G i) j x= if j=i then G i x else 0:=by rw [drop (r:=i) (diag_smooth ..) (homogeneous _)]; split_ifs<;>rfl
        change (∑ i∈range (d+1),rank (G i) j x)=_; split_ifs with hp
        · rw [sum_eq_single j]; exact (ht j).trans (if_pos rfl); exacts[fun i _ hi=> (ht i).trans (if_neg (Ne.symm hi)),fun hj=>False.elim (hj (mem_range.mpr (by omega)))]
        exact sum_eq_zero fun i hi=>by have heq:=mem_range.mp hi; exact (ht i).trans (if_neg (by omega))
lemma allot(h:Tall f d): f= ∑ i∈range (d+1),rank f i:=by obtain ⟨P,hP⟩:= stock h; exact hP.trans (sum_congr rfl (fun i hi=> ((wing P hP i).trans (if_pos (by have he:=mem_range.mp hi;omega))).symm))
lemma dropT(h:Tall f d)(hz:rank f d=0) : Tall f (d-1):=by
       by_cases hf:d=0; · subst d; exact h
       have he: f= ∑ i∈range d, rank f i := (allot h).trans (((sum_range_succ ..).trans (congr_arg _ hz)).trans (add_zero _)) -- unif
       have hp:Tall (∑ i∈range d,rank f i) (d-1):= sums _ _ (fun i hi=>loan _ (by have ht:= mem_range.mp hi;omega))
       rw[← he] at hp; exact hp
end Tall
end
end YM.OPE.Claw
