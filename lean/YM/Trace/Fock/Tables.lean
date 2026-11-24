import YM.Trace.Fock.Annihilator
noncomputable section
set_option maxHeartbeats 500000
set_option autoImplicit false
namespace YM.Trace.Shell
open Filter MeasureTheory Function Set YM Boundary Complex
open scoped ENNReal Pointwise Topology BigOperators
variable {m n : ℕ}
abbrev chartIdx (m n : ℕ) := Fin n → momentSlot m
def chartValue (c : chartIdx m n → ℂ) (x:Cords n) := ∑ i, c i * ∏ l, momentEntry (i l) (x l)
@[fun_prop] lemma chartValue_cont (c : chartIdx m n→ℂ) : Continuous (chartValue c) := by unfold chartValue; fun_prop
private lemma has_relay (m : ℕ) : ∃ u : (momentSlot m→ℂ)→ₗ[ℂ] filterRapid, ∀ x, (momentLM m) (u (momentLM m x))=momentLM m x := by
 let P := (momentLM m).range
 obtain ⟨g,hg⟩:= (momentLM m).rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict _)
 refine ⟨g.comp P.subtype.leftInverse,fun x=> ?_⟩
 have hh := LinearMap.ext_iff.mp hg ((momentLM m).rangeRestrict x)
 change P.subtype ((momentLM m).rangeRestrict (g (P.subtype.leftInverse (P.subtype ((momentLM m).rangeRestrict x)))))=P.subtype ((momentLM m).rangeRestrict x)
 rw [LinearMap.leftInverse_apply_of_inj P.ker_subtype]; exact congrArg P.subtype hh
private lemma chartSplit (F : MultilinearMap ℂ (fun _:Fin n=>filterRapid) ℂ)
       (m) (hF : ∀ i, ∀ w, momentLM m (w i)=0 → F w=0): ∃ c : chartIdx m n→ℂ, ∀ w,
       F w=∑ i, c i * ∏ l, (momentLM m (w l) (i l)) := by
   classical
   obtain ⟨u,hu⟩:=has_relay m
   let A := u.comp (momentLM m)
   have hA (x) : momentLM m (x-A x)=0 := by rw [map_sub,sub_eq_zero]; exact (hu _).symm
   let piece (s : Finset (Fin n)) (w : Fin n→filterRapid) i := if i∈s then A (w i) else w i
   have eqP (s : Finset (Fin n)) (w) : F (piece s w)=F w := by
       induction s using Finset.induction_on with
       | empty => simpa only [piece,Finset.notMem_empty,ite_false]
       | insert i s hi I =>
            rw [← I]
            have hh := hF i (update (piece s w) i ((w i)-A (w i))) (by rw [update_self]; exact hA _)
            rw [F.map_update_sub,sub_eq_zero] at hh
            have h₁ : update (piece s w) i (w i)=piece s w := by simp only [piece, Function.update_eq_self_iff, if_neg hi]
            have h₂ : update (piece s w) i (A (w i))=piece (insert i s) w := by unfold piece; ext j; by_cases hj:j=i <;> simp [update_apply,hj]
            rw [h₁,h₂] at hh; exact hh.symm
   have eqP' (w) : F (fun i=>A (w i)) = F w := by simpa only [piece, Finset.mem_univ,ite_true] using (eqP Finset.univ w)
   let basis (i : momentSlot m) : momentSlot m → ℂ:= Pi.single i (1:ℂ)
   let t (i) : filterRapid := u (basis i)
   have expand (x) : A x = ∑ i : momentSlot m, (momentLM m x i) • t i := by
        unfold A t
        have e : momentLM m x=∑ i, (momentLM m x i) • basis i := by
              funext i
              simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
              simpa only [basis,Pi.single_apply,ite_true,mul_one] using (Finset.sum_eq_single (f:=fun j:momentSlot m => (momentLM m x j)*(basis j i)) (s:=Finset.univ) i (fun j hj h=>by simp [basis,h]) (by simp)).symm
        calc _ = u (∑ i, (momentLM m x i) • basis i) := congrArg u e
             _ = _ := by rw [map_sum]; simp only [map_smul]
   refine ⟨fun χ=>F (fun k=>t (χ k)),fun w=>?_⟩
   rw [← eqP' w]; simp_rw [fun i=> expand (w i), F.map_sum, F.map_smul_univ]; congr! 1; rw [smul_eq_mul,mul_comm]
variable (v : Test4→L[ℂ] Sum m) (hv : FieldImage v) (k : @Angle m (n+1)) (w:Fin (n+1) → filterRapid)
include hv
lemma chart_testable {s : ℕ} (c : chartIdx s (n+1) → ℂ) : Integrable (fun x=> chartValue c x * testJoint w x) (νpow _) := by
    let ψ i (x:Cords (n+1)) := c i * ∏ j : Fin (n+1), (w j).val (x j) * momentEntry (i j) (x j)
    have ht i : Integrable (ψ i) (νpow _) := Integrable.fintype_prod_dep (fun k=> rapid_product_integrable (i k) (w k)) |>.const_mul _
    suffices hE : (fun x=> chartValue c x * testJoint w x) = fun x=> ∑ i, ψ i x by rw [hE]; exact integrable_finsetSum _ (fun _ _=>ht _)
    funext x; unfold chartValue testJoint; rw [Finset.sum_mul]; congr 1; funext i; unfold ψ; rw [mul_assoc,Finset.prod_mul_distrib,mul_comm (∏ _∈_, momentEntry ..)]

lemma chartEvidence : ∃ q : ℕ, ∃ c : chartIdx q (n+1) → ℂ, ∀ w, stripeIntegral v k w = ∫ x, chartValue c x * testJoint w x ∂νpow (n+1) := by
    obtain ⟨q,hq⟩:=stripe_factors v k hv
    obtain ⟨c,hc⟩:= chartSplit (stripeMap v k hv) q (fun i w=>hq i w)
    refine ⟨q,c,fun w=> ?_⟩
    change stripeMap v k hv w = _
    rw [hc]; unfold chartValue testJoint; simp_rw [Finset.sum_mul,mul_assoc,← Finset.prod_mul_distrib]
    have hM (i : chartIdx q (n+1)) (j) : Integrable (fun x => momentEntry (i j) x * (w j).val x) ν := by simpa only [mul_comm _ ((w j).val _)] using! rapid_product_integrable _ _
    rw [integral_finsetSum _ (fun i _=>Integrable.fintype_prod (fun k=> hM i k) |>.const_mul _)]
    congr! 2 with i
    rw [MeasureTheory.integral_const_mul, integral_fintype_prod_eq_prod (fun j x=>momentEntry (i j) x * (w j).val x)]; congr! 2 <;> exact integral_congr_ae (.of_forall (fun _=> mul_comm ..))
end YM.Trace.Shell
