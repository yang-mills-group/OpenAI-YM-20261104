import YM.FVA2.O.Ward.Transit
import YM.MS.Heat.GridStation
/-!
# Square on indexed coefficients
Parallel to MS.Book.Ell, but in the full kernel convention (no space box).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Ward
open MS Function Filter Set Finset MS.Plane MS.Koszul Flux MeasureTheory MS.Heat MS.Book Convolve Signal
variable {A P: Type} [AddCommGroup P][Fintype A][MeasurableSpace P]
variable {p:Sector A}{K L:Flux A P ℂ}{F H:T (Row A P ℂ)}{Q:Charge p P ℂ}
structure Wise (μ: Measure P)(F:Row A P ℂ) (K:Flux A P ℂ) (Q:Charge p P ℂ) : Prop where
    pay : Pass K F μ
    repeated : Pass K (orbit K μ F) μ
    high : Pass K (Q.raise F) μ
    flip l: Integrable (fun u:P×P=>trc K u.1 (trc K u.2 F) l) (μ.prod μ)
    sym : Symm (field p) F
lemma unaries (μ: Measure P)[SigmaFinite μ](F:Row A P ℂ)(h:Wise μ F L Q)
    (hz:∀ F:Row A P ℂ,Q.raise (Q.raise F)=0)(hk:closed L p true)
    (hs:∀ q (F:Row A P ℂ),Q.raise (trc L q F)= - trc L q (Q.raise F)) :
    (rack K L Q μ).J ((rack K L Q μ).J F) = 0 := by
    change (Q.raise + orbit L μ) ((Q.raise + orbit L μ) F)=0
    simp only [map_add,hz,LinearMap.add_apply]
    rw [finite_cc μ h.repeated,finite_cc μ h.high,finite_cc μ h.pay,pass_Z Q hs μ h.pay,zeroCcy hk h.sym μ h.pay]; · abel
    exact h.flip
lemma branches (μ:Measure P) (F H:Row A P ℂ) (hf:Wise μ F L Q)(hg:Wise μ H L Q)(hp:Pure (field p) false F)
    (hk:closed L p true)(hr: Reverse L p)(h:Heat.Route L L p F H μ)
    (hs:∀ q (F:Row A P ℂ), Q.raise (trc L q F)= - trc L q (Q.raise F)): let A:= (rack K L Q μ);
    A.J (A.C F H) + A.C F (A.J H) + A.C (A.J F) H=0 := by
    intro M; change (Q.raise+orbit L μ) (boulevard p L F H)+boulevard p L F ((Q.raise+orbit L μ) H)+boulevard p L ((Q.raise+orbit L μ) F) H=0
    simp only [LinearMap.add_apply,map_add]; simp only [ blvd ]
    rw [finite_cc μ ( t_bounce hk hr hf.sym hg.sym hp μ hf.pay hg.pay h ), finite_cc μ hf.pay, finite_cc μ hg.pay, slide_Z Q hp hk hs]; linear_combination (norm:=abel) bounce hk hr hf.sym hg.sym hp μ hf.pay hg.pay h
variable (μ:Measure P)
local notation "B" => rack K L Q μ
lemma square_at [SigmaFinite μ] (k:ℕ)(hpH:∀ i ≤ k, Wise μ (H i) L Q)(F':∀ i ≤ k,Wise μ (F i) L Q)
    (he:∀ i ≤ k,Pure (field p) false (F i)) (hz:∀ F:Row A P ℂ,Q.raise (Q.raise F)=0)(hk:closed L p true)(hr:Reverse L p)(h:∀ i j, i+j=k → Heat.Route L L p (F i) (H j) μ)(hs:∀ q (F:Row A P ℂ),Q.raise (trc L q F)= - trc L q (Q.raise F)):
    (B).res F ((B).res F H) k = - (pairW (B).C ((B).matCont F) H k) := by
    let D:= promote (B).J; let X:=(B).C; let T0:= pairW X; let W := T0 F (T0 F H)
    have hu : (D (D H)) k=0:= unaries (K:=K) μ _ (hpH k le_rfl) hz hk hs
    change (D (D H+T0 F H)+ T0 F (D H+T0 F H)) k= -(T0 (D F+(2:ℂ)⁻¹ • T0 F F) H k)
    simp_rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,Pi.add_apply, Pi.smul_apply]; rw [hu];
    have hd : (D (T0 F H) k+T0 F (D H) k)+ T0 (D F) H k=0:= by
       change (B).J (∑ i∈antidiagonal k,X (F i.1) (H i.2)) + (∑ i∈antidiagonal k,X (F i.1) ((B).J (H i.2))) + (∑ i∈antidiagonal k,X ((B).J (F i.1)) (H i.2)) =0
       simp_rw [map_sum,← Finset.sum_add_distrib]; exact Finset.sum_eq_zero fun i hi=> by
           obtain hx:= Finset.mem_antidiagonal.mp hi; exact branches (K:=K) μ _ _ (F' _ (by omega)) (hpH _ (by omega)) (he _ (by omega)) hk hr (h _ _ hx) hs
    have hu' : W k+W k+ T0 (T0 F F) H k=0:= by
        let M a b c:= X (F a) (X (F b) (H c))
        have hp : W k= ∑ i∈antidiagonal k,∑ j∈antidiagonal i.2,M i.1 j.1 j.2:= by unfold M W T0; rw [paired]; simp_rw [paired,map_sum]
        rw [hp,Convolve.associate]
        nth_rw 2 [show (∑ i∈antidiagonal k,∑ j∈antidiagonal i.1,M j.1 j.2 i.2)=∑ i∈antidiagonal k,∑ j∈antidiagonal i.1,M j.2 j.1 i.2 from Finset.sum_congr rfl (fun i _=> (Finset.Nat.sum_antidiagonal_swap (n:=i.1) (f:=fun j=> M j.1 j.2 i.2)).symm)]
        unfold T0; simp_rw [paired,map_sum,LinearMap.sum_apply,← Finset.sum_add_distrib]; exact Finset.sum_eq_zero fun d hd=> Finset.sum_eq_zero fun i hi=> by
           have hu:= Finset.mem_antidiagonal.mp hd; have ht:= Finset.mem_antidiagonal.mp hi
           -- order in switch
           exact crossSelf hk (F' _ (by omega)).sym (he _ (by omega)) (F' _ (by omega)).sym (he _ (by omega)) (hpH _ (by omega)).sym
    have hp := congr_arg ((2:ℂ)⁻¹ • ·) hu'; simp only [smul_add,smul_zero] at hp; rw [← add_smul] at hp; unfold W at hp; rw [show (2:ℂ)⁻¹+(2:ℂ)⁻¹=1 by norm_num,one_smul] at hp; linear_combination (norm:=abel) hd + hp
end YM.FVA2.O.Ward
