import YM.Trace.Fock.Relative
import YM.Trace.Fock.Budget

/-!
Transversality and the plain Fourier kernels after localization. The polarization
sum is eliminated on actual slot components, not by strengthening Eq. nfl.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace YM.Trace.Shell
open YM Boundary Function MeasureTheory Filter Set Complex Equiv
open scoped Topology BigOperators InnerProductSpace Pointwise
variable {m n : ℕ}
abbrev Angle := Fin n→Mode m
def spatialReplace (I : @Angle m n) (i : Fin n) (s : SpaceAxis) := Function.update I i ((I i).1, s)
lemma directTransverse (v : Test4→L[ℂ] Sum m) (h : FieldImage v) (n) : ∀ᵐ x∂νpow n,
     ∀ i I, ∑ j : SpaceAxis, (((x i j):ℝ):ℂ)*(fullWave v n x) (spatialReplace I i j) = 0 := by
     let g := Classical.choose (plus_fits (V:=E4))
     have hS := Classical.choose_spec (plus_fits (V:=E4))
     refine ((ae_all_iff.mpr (fun i=>fullWave_of_CC v h (g i) (hS.1 i) n)).and (ae_all_iff.mpr (fun i=>h.across (g i) n))).mono (fun x hx=>?_)
     intro i I
     obtain ⟨j,hj⟩:=hS.2 (total x)
     apply mul_left_cancel₀ (a:=(plus (g j) (total x))) hj
     convert hx.2 j i I
     · rw [hx.1 j,Finset.mul_sum]; dsimp only; exact Finset.sum_congr rfl (fun i _=> by rw [PiLp.smul_apply,smul_eq_mul,mul_left_comm]; rfl)
     rw [mul_zero]
lemma proj_auth (x : Mom) (z : SpaceAxis→ℂ) (hz : ∑ j : SpaceAxis, (↑(x j) : ℂ) * z j = 0) (w : SpaceAxis→ℂ) :
    (∑ j : SpaceAxis, (∑ k, (↑(projKernel x j k):ℂ) * w k) * z j) = ∑ j, w j*z j := calc
    _ = ∑ k, w k * ∑ j, (projKernel x j k:ℂ) * z j := by
      simp_rw [Finset.sum_mul]; rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl (fun i hi=> Finset.sum_congr rfl (fun j hj=> by ring))
    _ = _ := by
      refine Finset.sum_congr rfl (fun j _ => congr_arg (w j * ·) ?_)
      unfold projKernel; push_cast
      simp_rw [sub_mul,Finset.sum_sub_distrib]
      suffices HH : ∑ k,(↑(x j)* ↑(x k) / (↑‖x‖^2:ℂ)) * z k = 0 by rw [HH,sub_zero]; simp [apply_ite Complex.ofReal, ite_mul]
      have H := congr_arg (fun t : ℂ=>↑(x j)/((‖x‖:ℂ)^2) * t) hz
      exact Eq.trans (Finset.sum_congr rfl fun i _=> by change (↑(x j)* ↑(x i)/((↑‖x‖)^2:ℂ)) * z i = ↑(x j)/(↑‖x‖)^2 * (↑(x i)*z i); ring)
            ((Finset.mul_sum ..|>.symm).trans (H.trans (by ring)))

private def switch (i : Fin n) : Equiv.Perm (@Angle m n × SpaceAxis) := {
    toFun y := (spatialReplace y.1 i y.2, (y.1 i).2)
    invFun y := (spatialReplace y.1 i y.2, (y.1 i).2)
    left_inv y := by ext1; swap; simp [spatialReplace]; funext j; by_cases h:j=i <;> simp [h,spatialReplace]
    right_inv y := by ext1; swap; simp [spatialReplace]; funext j; by_cases h:j=i <;> simp [h,spatialReplace] }
private lemma sum_count (b : Angle→ℂ) (i : Fin n) : ∑ u : @Angle m n, ∑ j, b (spatialReplace u i j) = 3 * ∑ u : @Angle m n, b u := by
    convert (Equiv.sum_comp (switch (m:=m) i) (fun t=> b t.1)) using 1 <;>
        simp [switch,Fintype.sum_prod_type,Finset.mul_sum]
private lemma sum_under (b d : @Angle m n → ℂ) (i : Fin n)
    (h : ∀ I, ∑ j, b (spatialReplace I i j) = ∑ j, d (spatialReplace I i j)) : ∑ j,b j=∑ j,d j := by
     apply mul_left_cancel₀ (a:=(3:ℂ)) (by norm_num)
     rw [← sum_count _ i, ← sum_count _ i]; exact Finset.sum_congr rfl (fun j _=> h j)

private def piece (x : Cords n) (w : ∀ j:Fin n, Mode m → ℂ) (A : Finset (Fin n)) (i : Fin n) (p : Mode m) :=
        if i ∈ A then ∑ j, (projKernel (x i) p.2 j : ℂ) * w i (p.1, j) else w i p
private def testedSum (x : Cords n) (z : Fiber m n) (w : ∀ j, Mode m→ℂ) (A : Finset (Fin n)) := ∑ p,
        (∏ j, piece x w A j (p j)) * z p
private lemma erase_factor (x : Cords n) (z : Fiber m n) (w : ∀ j:Fin n, Mode m→ℂ)
    (hz : ∀ i K, ∑ j : SpaceAxis, (((x i j):ℝ):ℂ) * z (spatialReplace K i j)=0) (i : Fin n) (s : Finset (Fin n)) (hi : i∉s) :
    testedSum x z w (insert i s)=testedSum x z w s := by
    unfold testedSum
    refine sum_under (i:=i) _ _ (fun I=> ?_)
    let g j := piece x w s j (I j)
    let L := ∏ j ∈ (Finset.univ:Finset (Fin n)) \ {i}, g j
    have hL (A) (U) : (U=insert i s ∨ U=s) → let J := spatialReplace I i A;
       (∏ j, piece x w U j (J j)) = piece x w U i (J i) * L := by
       intro h J
       suffices hE : (fun j=>piece x w U j (J j))=Function.update g i (piece x w U i (J i)) by
          rw [hE]; exact Finset.prod_update_of_mem (Finset.mem_univ i) _ _
       funext j; by_cases hj : j=i
       · rw [hj,update_self]
       rw [update_of_ne hj]; simp_rw [show J j=I j from Function.update_of_ne hj ..]
       rcases h with (rfl|rfl); simp [piece,g,hj]; rfl
    let C := fun j => z (spatialReplace I i j)
    let c := (I i).1
    have hB := proj_auth (x i) C (hz i I) (fun j=>w i (c,j))
    have H : ∀ (U:Finset (Fin n)), U=insert i s ∨ U=s →
        ∑ j,(∏ t, piece x w U t ((spatialReplace I i j) t))* z (spatialReplace I i j)= (∑ j, piece x w U i ((spatialReplace I i j) i)*C j)*L := fun U hu => by
          rw [Finset.sum_mul]; simp_rw [show ∀ j, ∏ t,piece x w U t ((spatialReplace I i j) t)= _ from fun j:SpaceAxis=> hL j U hu]
          exact Finset.sum_congr rfl (fun k _ => by dsimp only [C]; ring)
    rw [H _ (Or.inl rfl),H _ (Or.inr rfl)]
    exact congr_arg (· * L) (by simpa [piece,hi, spatialReplace] using! hB)

private lemma decompose_sum {n m:ℕ} (x : Cords n) (z : Fiber m n) (w : ∀ j:Fin n, Mode m→ℂ)
    (hz : ∀ i K, ∑ j : SpaceAxis, (((x i j):ℝ):ℂ) * z (spatialReplace K i j)=0) (s : Finset (Fin n)) :
    testedSum x z w s=testedSum x z w ∅ := by
      induction s using Finset.induction_on with
      | empty => rfl
      | insert i s hi hs => exact erase_factor x z w hz i s hi |>.trans hs
noncomputable def spread (v : @Mixed n m) (x : Cords n) (k : @Angle m n) := ∏ i, (‖x i‖:ℂ) * plus (v i (k i)) (ray (x i))
lemma plain_inner {n m:ℕ} (x : Cords n) (z : Fiber m n) (v : @Mixed n m)
    (hz : ∀ i K, ∑ j : SpaceAxis, (((x i j):ℝ):ℂ) * z (spatialReplace K i j)=0) :
    inner ℂ (productMany v x) z= ∑ k:@Angle m n, star (spread v x k) * z k := by
    rw [PiLp.inner_apply]
    simp_rw [show ∀ i : Fin n → Mode m, (productMany v x) i = ∏ j, (jet (x j) (v j) (i j)) from fun _=> rfl,RCLike.inner_apply,map_prod]
    symm -- easier RHS
    let w (i) (j) := (starRingEnd ℂ) (plus (v i j) (ray (x i)))
    have he (i j) : (starRingEnd ℂ) (jet (x i) (v i) j) = (‖x i‖:ℂ) * piece x w Finset.univ i j := by
          unfold piece; simp [jet, Complex.real_smul,w] -- real_smul
    let L := ∏ j, (‖x j‖:ℂ)
    have h := decompose_sum x z w hz Finset.univ
    simp_rw [he,Finset.prod_mul_distrib, mul_left_comm (z _:ℂ)]
    unfold spread; push_cast -- star_prod
    calc _ = L * ∑ k:@Angle m n, (∏ i, (starRingEnd ℂ) (plus (v i (k i)) (ray (x i)))) * z k := ?_
         _ = L * testedSum x z w ∅ := by simp [testedSum,piece,w]
         _ = _ := ?_
    · rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun k _ => ?_); dsimp only; rw [star_def, map_prod]; simp only [map_mul,Finset.prod_mul_distrib, Complex.conj_ofReal]; unfold L; ring -- fix
    · rw [←h,testedSum,Finset.mul_sum]; apply Finset.sum_congr rfl (fun k _=> ?_); dsimp only [L]; ring
lemma plain_inner_flip (x:Cords n) (z:Fiber m n) (v:@Mixed n m)
    (hz : ∀ i K, ∑ j : SpaceAxis, (((x i j):ℝ):ℂ) * z (spatialReplace K i j)=0) :
    inner ℂ z (productMany v x)=∑ k:@Angle m n, star (z k) * spread v x k := by
    rw [show inner ℂ _ _=star (inner ℂ (productMany v x) z) from inner_conj_symm _ _|>.symm, plain_inner x z v hz,star_def, map_sum]
    simp only [map_mul,starRingEnd_apply, ← star_def,star_star,mul_comm (spread ..)]
end YM.Trace.Shell
