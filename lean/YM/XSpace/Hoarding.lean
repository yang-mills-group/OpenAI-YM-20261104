import YM.XSpace.Terrain
/-! # H & real compatibility of independent amplitudes before positioning -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Structure1
open Filter Set Function Lattice Chart2 Mu Normalize Foundation JetGauge Outline Shade Future Hoops
open scoped Topology BigOperators Classical
variable {G:Gauge} (W:Initialize G) (d:ℕ)(a:ℝ) (x: Cover){j n :ℕ}
private lemma swirls (s:Signed)(p q:HP G j)(h:(q:Maxwell.WickPol G)= Maxwell.Free.reflectPol s.ortho p.val) : weave s (star0 W a j x p) = star0 W a j (s.act x) q ∧ weave s (star1 W a j x p)= star1 W a j (s.act x) q:=by
  let S:= W.surveys j; have he : Prelude.startField S q=Labels.tensor s.ortho (Prelude.startField S p):= by rw [Prelude.startField, show Price.preparedL q= _ from On.section_turn s ((Normalize.en le_rfl) p) ((Normalize.en le_rfl) q) h.symm, S.wick_signed]; rfl
  simp_rw [base_mark0, base_mark1]; change weave s (base a^j • p0 S x _)= _ • p0 S _ (Prelude.startField S q).val ∧ weave s (base a^j • p1 S x _)= _ • p1 S _ (Prelude.startField S q).val; rw [he,map_smul,map_smul,(hymn_text S s _ x).1,(hymn_text S s _ x).2]; trivial
private lemma coast (p q:HP G j)(h:(q:Maxwell.WickPol G)= Maxwell.Free.realForm p.val) : shore G (star0 W a j x p)= star0 W a j x q ∧ shore G (star1 W a j x p) = star1 W a j x q:=by
  let S:= W.surveys j; have he : Prelude.startField S q= Labels.realBar (Prelude.startField S p):=by
    rw [Prelude.startField, show Price.preparedL q=Labels.realBar (Price.preparedL p) from On.section_real _ _ h.symm,S.wick_real]
  have hf (p:Stamp G): shore G (base a^j • p)=base a^j • shore G p := by rw [← MvPolynomial.C_mul',← MvPolynomial.C_mul',map_mul]; simp [shore,Taylor.conjPol,base]
  simp_rw [base_mark0,base_mark1,hf]; change _ • shore G (p0 S x _)= _ • p0 S _ (Prelude.startField S q).val ∧ _ • shore G (p1 S x _)= _ • p1 S _ (Prelude.startField S q).val; rw [he,(salutations S _ x).1,(salutations S _ x).2]; trivial
lemma angular_mark (p:Sec G d)(s:Signed): weave s (μ0 W d a x p)= μ0 W d a (s.act x) (ori s.ortho d p) ∧ weave s (μ1 W d a x p)= μ1 W d a (s.act x) (ori s.ortho d p):=by
  simp only [μ0,μ1,assemble,LinearMap.sum_apply,map_sum,LinearMap.comp_apply]; exact ⟨Finset.sum_congr rfl (fun i _=> (swirls W a x s _ _ (part_ori ..)).1),Finset.sum_congr rfl fun i _=> (swirls W a x s _ _ (part_ori ..)).2⟩
lemma realm_mark (p:Sec G d): shore G (μ0 W d a x p)= μ0 W d a x (reel d p)∧ shore G (μ1 W d a x p)= μ1 W d a x (reel d p):=by
  simp only [μ0,μ1,assemble,LinearMap.sum_apply,map_sum,LinearMap.comp_apply]; exact ⟨Finset.sum_congr rfl (fun i _=> (coast W a x _ _ (part_reel ..)).1),Finset.sum_congr rfl fun i _=> (coast W a x _ _ (part_reel ..)).2⟩
variable (x:Fin n→Cover)(s:Signed)(p:Tags G d n)
lemma season (b z : Fin n→ Sec G d→ₗ[ℂ] Stamp G) (q: Tags G d n)(L: Stamp G→+* Stamp G) (h:∀ i,z i (q i)=L (b i (p i))) : wind d z q= L (wind d b p):=by rw [winds,winds,map_prod]; simp_rw [h]
lemma oriented_blossom : blossom0 W d a (fun i=> s.act (x i)) (ori s.ortho d ∘ p)= blossom0 W d a x p:=by unfold blossom0; rw [LinearMap.compMultilinearMap_apply, season _ p _ _ (ori s.ortho d ∘ p) (weave s).toRingHom (fun i=> (angular_mark W d a (x i) (p i) s).1.symm)]; apply weaves
lemma oriented_snow (q:Face ℤ): snow W d a (fun i=>s.act (x i)) (Face.send s 0 q) (ori s.ortho d ∘ p)= snow W d a x q p:=by unfold snow; rw [LinearMap.compMultilinearMap_apply, season _ p _ _ (ori s.ortho d ∘ p) (weave s).toRingHom (fun i=> (angular_mark W d a (x i) (p i) s).1.symm)]; change E (Mu.root G) (V3 G (Face.send s 0 q)*weave s (wind d (fun i=> μ0 W d a (x i)) p)) = E (Mu.root G) (V3 G q * (wind d (fun i=> μ0 W d a (x i)) p)); rw [← weaves_V, ← map_mul]; exact weaves s _
lemma oriented_first : replied W a (fun i=> s.act (x i)) d (ori s.ortho d ∘ p)= replied W a x d p:=by
  simp only [replied,blossom1, sub_apply,sum_apply,LinearMap.compMultilinearMap_apply]; apply congr_arg₂ (·-·)
  · refine Finset.sum_congr rfl fun i _=>?_ ; rw [season _ p _ _ _ (weave s).toRingHom]; exact weaves s _
    intro j; by_cases h:j=i; subst j; rw [update_self,update_self]; exact (angular_mark W d a (x i) (p i) s).2.symm; rw [update_of_ne h,update_of_ne h]; exact (angular_mark W d a (x j) (p j) s).1.symm
  rw [← Equiv.sum_comp (PlaqAxes.transform s)]; refine Finset.sum_congr rfl fun i _=>?_ ; unfold integralPart; simp only [MultilinearMap.mk'_apply]; rw [← Equiv.tsum_eq (phase (R:=ℤ) s i)]; apply tsum_congr; intro u; exact (rises s i u) ▸ oriented_snow W d a x s p (u,i)
lemma winter0 : blossom0 W d a x (reel d ∘ p)= star (blossom0 W d a x p):=by unfold blossom0; rw [LinearMap.compMultilinearMap_apply, season _ p _ _ (reel d ∘ p) (shore G) (fun i=> (realm_mark W d a (x i) (p i)).1.symm)]; apply vex
lemma winter1 : replied W a x d (reel d ∘ p)=star (replied W a x d p):=by
  have he(q:Face ℤ): snow W d a x q (reel d ∘ p)= star (snow W d a x q p):= by
    unfold snow; rw [LinearMap.compMultilinearMap_apply, season _ p _ _ (reel d ∘ p) (shore G) (fun i=> (realm_mark W d a (x i) (p i)).1.symm)]; change E (Mu.root G) (V3 G q * shore G (wind d (fun i=> μ0 W d a (x i)) p))= star (E (Mu.root G) (V3 G q* (wind d (fun i=> μ0 W d a (x i)) p))); nth_rw 1 [← vex_V]; rw [← map_mul]; exact vex _
  simp only [replied,blossom1, sub_apply,sum_apply, LinearMap.compMultilinearMap_apply, star_sub, star_sum]; apply congr_arg₂ (·-·)
  · refine Finset.sum_congr rfl fun i _=>?_ ; rw [season _ p _ _ _ (shore G)]; apply vex
    intro j; by_cases h:j=i; subst j; simp only [update_self]; exact (realm_mark W d a (x i) (p i)).2.symm; simp only [update_of_ne h]; exact (realm_mark W d a (x j) (p j)).1.symm
  refine Finset.sum_congr rfl fun i _=>?_ ; unfold integralPart; simp_rw [MultilinearMap.mk'_apply,he,tsum_star]

abbrev atlas (x:Fin n→jobs d): Fin n→ℕ:=fun i=>(x i).val -- U
lemma whom (T V:Point G d n)(h:∀ (j:Fin n→ℕ)(q:∀ i,HP G (j i))(hj:∀ i,j i≤d),T (shells j q hj)=V (shells j q hj)): T=V:=by ext1 p; rw [calls T p,calls V p]; exact Finset.sum_congr rfl fun i _=> h ..
lemma blossom_plus (y:Cover): blossom0 W d a (fun i=> y+x i)=blossom0 W d a x:= whom _ _ _ fun j q h=> by rw [blossoms,blossoms,base_plus]
lemma reply_plus (y:Cover): replied W a (fun i=> y+x i) d=replied W a x d:= whom _ _ _ fun j q h=> by rw [raw1,raw1,whole_plus]
end YM.XSpace.Structure1
