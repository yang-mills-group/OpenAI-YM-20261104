import YM.Trace.Fock.Stripe
/-! Distributional annihilator and positive-time branch separation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option pp.universes false
namespace YM.Trace.Shell
open Filter MeasureTheory Function Set YM Boundary Complex
variable {n m q : ℕ}
private lemma closesOn (H : Mom→ℂ) {q : ℕ} (r : filterRapid) (hr : (momentLM q) r=0) (a b: polySlot q→ℂ) (h : H=ᶠ[ae ν] fun p=> (‖p‖:ℂ)*slotPacket a p + slotPacket b p) : ∫ p, r.val p * H p ∂ν = 0 := by
   let K (c : polySlot q→ℂ) (i : Bool) x := ∑ j, c j * (r.val x * momentEntry (i,j) x)
   have hi (c : polySlot q→ℂ) (i : Bool) : Integrable (K c i) ν := integrable_finsetSum _ (fun j _=> (rapid_product_integrable _ _).const_mul _)
   have hK c i : (∫ p, K c i p∂ν)=0 := by
         rw [integral_finsetSum _ (fun j _=> (rapid_product_integrable ..).const_mul _)]
         exact Finset.sum_eq_zero (fun j _=> by
             simp_rw [MeasureTheory.integral_const_mul]
             exact mul_eq_zero_of_right _ (congrFun hr (i,j)))
   rw [(integral_congr_ae (g:=fun p => K a true p + K b false p) (h.mono fun p hp=> (by dsimp [K]; rw [hp]; simp_rw [momentEntry, slotPacket]; simp only [ite_true,Bool.false_eq_true,ite_false,one_mul, Finset.mul_sum, mul_add, Finset.sum_add_distrib, Prod.snd,Prod.fst]; congr! 2 <;> ring))),integral_add (hi ..) (hi ..),hK,hK,add_zero]
variable (w : Fin (n+1)→filterRapid) (v : Test4→L[ℂ] Sum m) (k : @Angle m (n+1)) (hv : FieldImage v)
def Supplied (g : filterRapid) := ∃ f : Test4, Eligible f ∧ g=rapidRay (Probe.hat f)
include hv
lemma annihilator_core : ∃ q : ℕ, ∀ i : Fin (n+1), ∀ w : Fin (n+1) → filterRapid, (momentLM q) (w i)=0 →
     (∀ j, j≠i → Supplied (w j)) → stripeIntegral v k w=0 := by
 obtain ⟨N,hN⟩:= controlled_slice v hv k
 obtain ⟨q,hq⟩:=bounded_bare_packets N
 refine ⟨q,fun i w hx hW=>?_⟩
 choose t ht hT using fun j=> hW (i.succAbove j) (by simp)
 have hs := hq (rowA v k t i) (rowB v k t i) ⟨by fun_prop,(hN ..).1⟩ ⟨by fun_prop,(hN ..).2⟩ (fun f hf=> sliced_match v hv k t i ht f hf)
 have hb : sliceTest v k w i = rowA v k t i := by
    unfold sliceTest rowA testedMinus testJoint
    simp_rw [comp_apply, hT, rapidRay]
 rw [stripe_cut v k hv w i,hb]
 rcases hs with ⟨a,b,hs⟩
 exact closesOn _ (w i) hx a b hs

private lemma unblock_one {q : ℕ} {i : Fin (n+1)} (h : ∀ w : Fin (n+1) → filterRapid, momentLM q (w i)=0 →
    (∀ j, j≠i → Supplied (w j)) → stripeIntegral v k w=0) : ∀ w, momentLM q (w i)=0 → stripeIntegral v k w=0 := by
    suffices H : ∀ s : Finset (Fin (n+1)), ∀ w : Fin (n+1)→ filterRapid, momentLM q (w i)=0 → (∀ j∉s, j≠i → Supplied (w j)) → stripeIntegral v k w=0 by
       exact fun w hw=> H Finset.univ w hw (by simp)
    intro t; induction t using Finset.cons_induction_on with
    | empty => exact fun w hw hh=> h w hw (hh · (Finset.notMem_empty _) ·)
    | cons i' s ht IH =>
         intro w hw hh
         by_cases hi : i' = i
         · subst i'; exact IH w hw (by intro j hj hh'; exact hh j (by simpa only [Finset.mem_cons,not_or] using (⟨hh',hj⟩)) hh')
         obtain ⟨N,hN⟩:=replacementControl v k hv i'
         have hA := pureZero (sliceTest v k w i') (hN w)
         suffices HS : sliceTest v k w i'=ᶠ[ae ν] fun _=> 0 by
            rw [stripe_cut v k hv w i']
            exact Eq.trans (integral_congr_ae (HS.mono fun p hp=> show (w i').val p * _=0 from by rw [hp,mul_zero])) (integral_zero Mom ℂ)
         refine hA (fun φ hφ=> ?_)
         let w' := update w i' (rapidRay (Probe.hat φ))
         have hMx := IH w' (by dsimp only [w']; rwa [Function.update_of_ne (Ne.symm hi)])
         rw [← slice_update v k w i' (rapidRay (Probe.hat φ)) ]
         have hk (p:Mom) : (Probe.hat φ) (ray p) = (w' i').val p := by dsimp only [w']; rw [update_self]; rfl
         simp_rw [hk]
         change (∫ p,(w' i').val p * sliceTest v k w' i' p∂ν) = _
         rw [← stripe_cut v k hv w' i']
         refine hMx (fun j hj hJ=>?_)
         by_cases hj' : j=i'
         · subst j; unfold w'; exact ⟨φ,hφ, update_self _ _ _⟩
         unfold w'; rw [update_of_ne hj']
         exact hh j (show j∉Finset.cons i' s _ by simpa using ⟨hj',hj⟩) hJ

lemma stripe_factors : ∃ q, ∀ i, ∀ w : Fin (n+1)→filterRapid, momentLM q (w i)=0 → stripeIntegral v k w=0 := by
 obtain ⟨q,hq⟩:= annihilator_core v k hv
 exact ⟨q,fun i=>unblock_one v k hv (hq i)⟩
end YM.Trace.Shell
