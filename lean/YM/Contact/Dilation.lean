import YM.Contact.RowTrial

/-! Change of only the normal variable in the joint test space. -/
set_option autoImplicit false
noncomputable section
open Set Function Filter MeasureTheory
open scoped ContDiff BigOperators Topology
namespace YM.Contacts.Patch
variable {A B:Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
def expand (r:ℝ) (z:A × B):=(r • z.1,z.2)
@[fun_prop] lemma smooth_expand {n:ℕ∞ω}(r:ℝ):ContDiff ℝ n (expand (A:=A) (B:=B) r):=(contDiff_const (c:=r) (E:=A×B)|>.smul contDiff_fst).prodMk contDiff_snd
def normalized (A:Type*)[AddCommGroup A][Module ℝ A] (r:ℝ):= (r^(normal A))⁻¹
lemma expand_compact {r:ℝ}(hr:r>0) (φ:Trial (A × B)):HasCompactSupport (fun x=> φ (expand r⁻¹ x)):= (φ.hasCompactSupport.image (smooth_expand r (A:=A) (B:=B) (n:=0)|>.continuous)).of_isClosed_subset (isClosed_tsupport _) (fun _ h=> ⟨_,tsupport_comp_subset_preimage _ ((smooth_expand r⁻¹ (n:=0)|>.continuous)) h,Prod.ext (smul_inv_smul₀ hr.ne' _) rfl⟩)
set_option maxHeartbeats 1100000 in
def review (r:ℝ) : Trial (A×B) →ₗ[ℂ] Trial (A×B) := if hr:0<r then
   {toFun:= fun φ=> ⟨fun x=>(normalized A r) • φ (expand r⁻¹ x), (contDiff_const (c:=(normalized A r))).smul (φ.contDiff.comp (smooth_expand _)), show HasCompactSupport ((fun _=>normalized A r) • (fun x=> φ (expand r⁻¹ x))) from (expand_compact hr φ).smul_left, fun _ _ => trivial⟩
    -- fix smul_left type R realm
    map_add':= fun φ ψ=>TestFunction.ext fun x=>show _ • (φ (expand r⁻¹ x)+ψ (expand r⁻¹ x)) = _ from smul_add ..
    map_smul':=fun c φ=>TestFunction.ext fun x=>show (normalized A r:ℝ) • (c • φ (expand r⁻¹ x)) = _ from smul_comm ..}
               else 0
variable [FiniteDimensional ℝ A][FiniteDimensional ℝ B]
omit [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] in
lemma reviewed {r:ℝ}(hr:0<r) (φ:Trial (A×B))(x:A×B):review r φ x= normalized A r • φ (expand r⁻¹ x):=by simp_rw [review,dif_pos hr];rfl
omit [FiniteDimensional ℝ B] in
lemma shrink_remainder (s r:ℝ)(hr:0<r)(m:ℤ)(φ:Trial A)(x:A):
     remainder s m (shrinking r φ) x=(normalized A r) • remainder (s/r) m φ (r⁻¹ • x):=by
   rw [remainder,shrinking_apply,shrink_apply,remainder,smul_sub];congr 1
   rw [taylorCut,taylorCut]; split_ifs <;> try rw [smul_zero]
   have hf:(s/r)⁻¹*r⁻¹=s⁻¹:=by rw [inv_div,div_eq_mul_inv];field_simp
   have hc:chi s x=chi (s/r) (r⁻¹ • x):=by simp only [chi, smul_smul,hf]
   simp only [shrinking_fun,polynomial,jet_shrink,smul_zero,Finset.smul_sum,hc]; exact Finset.sum_congr rfl (fun i _=>smul_comm ..)
omit [FiniteDimensional ℝ B] in
lemma change_row (s r:ℝ)(hr:0<r)(m:ℤ)(φ:Trial (A×B))(y:A×B):row s m (review r φ) y = normalized A r • row (s/r) m φ (expand r⁻¹ y):= by
      unfold row; rw [show slice (review r φ) y.2 = shrinking r (slice φ y.2) from TestFunction.ext (fun x=> reviewed hr φ _),shrink_remainder _ _ hr];rfl

variable [MeasureSpace A][MeasureSpace B][BorelSpace A][BorelSpace B][μ : (volume:Measure A).IsAddHaarMeasure][ν: IsFiniteMeasureOnCompacts (volume:Measure B)]
include μ ν
lemma normal_map (r:ℝ)(hr:r>0): Measure.map (expand r (A:=A) (B:=B)) volume = ENNReal.ofReal (normalized A r) • volume:=by
       change Measure.map (Prod.map (fun x:A => r • x) (id:B→B)) ((volume:Measure A).prod (volume:Measure B))=_
       rw [← Measure.map_prod_map _ _ (by fun_prop) measurable_id, volume.map_addHaar_smul hr.ne',Measure.map_id,abs_of_nonneg (inv_pos.mpr (pow_pos hr _)).le, Measure.prod_smul_left];rfl

omit μ ν in
lemma expand_embed {r:ℝ}(hr:r>0):MeasurableEmbedding (expand r (A:=A) (B:=B)):=((Homeomorph.smul (Units.mk0 r hr.ne')|>.prodCongr (Homeomorph.refl B)).toMeasurableEquiv).measurableEmbedding
-- needs Borel A and B! fix

variable {G:Type*}[NormedAddCommGroup G][NormedSpace ℝ G]
def equiv (A B:Type*) [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B][FiniteDimensional ℝ A][FiniteDimensional ℝ B][MeasurableSpace A][MeasurableSpace B][BorelSpace A][BorelSpace B]{r:ℝ}(hr:r>0): A×B ≃ᵐ (A×B):=((Homeomorph.smul (Units.mk0 r⁻¹ (inv_pos.mpr hr).ne')).prodCongr (Homeomorph.refl B)).toMeasurableEquiv

lemma changed_integral {r:ℝ}(hr: r>0) (g:A×B→G): normalized A r • ∫ z,(g (expand r⁻¹ z)) = ∫ y,g y := by
      conv_lhs=> arg 2; rw [show (fun z=>g (expand (A:=A) r⁻¹ z))= (fun y=>(fun z=>g (equiv A B (r:=r) hr z)) y) from rfl, ← integral_map_equiv]
      rw [show ⇑(equiv A B hr)=expand r⁻¹ from rfl,normal_map (B:=_) r⁻¹ (inv_pos.mpr hr), integral_smul_measure]
      rw [ENNReal.toReal_ofReal (by unfold normalized; positivity),smul_smul]; unfold normalized; rw [inv_pow,inv_inv,inv_mul_cancel₀ (pow_pos hr _).ne',one_smul]


lemma expand_preserving {r:ℝ}(hr:r>0):Measure.QuasiMeasurePreserving (expand (A:=A) (B:=B) r) := ⟨(smooth_expand r (A:=A) (B:=B) (n:=0)|>.continuous.measurable), by simp [Measure.AbsolutelyContinuous,normal_map (A:=A) (B:=B) r hr]; exact fun _ h => Or.inr h⟩
lemma expand_integrable {r:ℝ}(hr:r>0){g:A×B→G}(hg:Integrable g): Integrable (fun x=> g (expand r x)) := (expand_embed (A:=A) (B:=B) hr).integrable_map_iff.mp (normal_map (A:=A) (B:=B) _ hr ▸ hg.smul_measure (by simp))
omit [NormedAddCommGroup A] [NormedSpace ℝ A][FiniteDimensional ℝ A][MeasureSpace A][BorelSpace A] μ ν in
lemma normalized_norm {A:Type*}[AddCommGroup A][Module ℝ A] {r:ℝ}(hr: r>0) (g:G): ‖normalized A r • g‖ = normalized A r • ‖g‖:=by rw[norm_smul]; rw[Real.norm_of_nonneg (by unfold normalized;positivity),smul_eq_mul]

end YM.Contacts.Patch
