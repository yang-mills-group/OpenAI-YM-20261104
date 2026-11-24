import YM.MS.Osc.Wave
import YM.MS.Tone.Haar
/-!
# Discrete momentum measure, pitch b
We integrate smooth extensions. Cost independent spectra of reciprocal lattice. Compare
any order Taylor via snapping and translations with averaged origin. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Osc.Snap
open Set Filter Function Finset Metric MeasureTheory Real ENNReal
open Momentum Tone Lattice Landau Native
open scoped Topology ContDiff
variable {I E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {p q b:ℝ}{i j:Cover}
abbrev planeF : Measure QP:= covMeasure Axis
def whole (b:ℝ) : Cover →+ QP := b • (⟨⟨Tone.embed, by ext; simp [Tone.embed]⟩, emb_add⟩: Cover →+QP)
lemma at_whole (b:ℝ)(x:Cover)(k:Axis): whole b x k = b* (x k:ℝ) := rfl
def back (b:ℝ)(p:QP): Cover:= fun i=>⌊p i/b⌋
lemma back_m : Measurable (back b):= by unfold back; apply measurable_pi_lambda; intro i; fun_prop
lemma whole_m : Measurable (whole b):= measurable_of_countable _
def Tick (b:ℝ): QP→QP:= whole b ∘ back b
lemma tick_m : Measurable (Tick b):= whole_m.comp back_m
-- boxes
variable (h:0<b)
include h
lemma bo (q:QP)(i:Cover): back b (whole b i+q)=i+ back b q:= by ext j; change ⌊(_+_) /b⌋ = (i j + _); rw [at_whole,add_div,mul_comm b, mul_div_cancel_right₀ (i j:ℝ) h.ne', Int.floor_intCast_add]; rfl -- simp?
lemma maxS (q:QP): ‖Tick b q - q‖≤ b:= by
    apply (pi_norm_le_iff_of_nonneg h.le).mpr; intro i; rw [norm_eq_abs]; apply abs_le.mpr; change -b≤ b * ( (⌊q i/b⌋:ℤ):ℝ) - q i ∧ _; obtain ht := (le_div_iff₀ h).mp (Int.floor_le (q i/b)); obtain hz:= (div_lt_iff₀ h).mp ( Int.lt_floor_add_one (q i/b) ); change _ ∧ b * (⌊q i/b⌋:ℤ) - q i ≤ b; constructor <;> nlinarith
omit h
abbrev rail (b:ℝ): Measure QP:= planeF.map (Tick b)
instance rail_inf : SFinite (rail b):= inferInstanceAs (SFinite (Measure.map _ planeF))
include h
lemma boom (i: Cover) : Equ (rail b) (whole b i) := by
   let F:= fun q:QP=> whole b i+q; have hf : Measurable F:= by unfold F; fun_prop
   have hv : F ∘ Tick b = Tick b ∘ F := by funext q; simp only [ Tick, comp_apply,F,bo h, map_add]
   have ht : Equ planeF (whole b i):= by exact measurePreserving_add_left planeF _ -- name
   exact ⟨ hf, by change Measure.map F ( Measure.map (Tick b) _) = _; rw [ Measure.map_map hf tick_m,hv,← Measure.map_map tick_m hf]; change Measure.map (Tick b) (Measure.map (fun q:QP=> whole b i+q) planeF)=_; rw [ht.map_eq]⟩ -- inference
-- boxes
omit h
abbrev Box (b:ℝ)(i:Cover): Set QP:= back b ⁻¹' {i}
abbrev Shell (b:ℝ)(i:Cover): Measure QP := planeF.restrict (Box b i)
lemma box_m (i:Cover): MeasurableSet (Box b i):= back_m (measurableSet_singleton _)
lemma one_box (b:ℝ)(q:QP): q∈Box b (back b q):= rfl
lemma def_box (q:QP)(i:Cover): q∈Box b i↔ back b q=i:= Iff.rfl
lemma pub : Pairwise (Disjoint on Box b) := by intro i j he; apply Set.disjoint_left.mpr; intro u hv hz; exact he ( hv.symm.trans hz ) -- hv : in region
lemma sum_shell (b:ℝ) : planeF = Measure.sum ( fun i:Cover=> Shell b i ):= by
   nth_rw 1 [← Measure.restrict_univ (μ:=planeF)]; rw [show (Set.univ:Set QP)=⋃ i:Cover,Box b i from by ext q; simp,Measure.restrict_iUnion pub (fun i=> box_m i)]
include h
lemma floor0 (x:ℝ) : ⌊x/b⌋=0 ↔ 0≤x ∧ x<b:= by rw [Int.floor_eq_iff]; constructor <;> rintro ⟨hx,hX⟩; refine ⟨ (by simpa using ( le_div_iff₀ h).mp hx), by simpa using (div_lt_iff₀ h).mp hX⟩; exact ⟨ (le_div_iff₀ h).mpr (by simpa), (div_lt_iff₀ h).mpr (by simpa) ⟩
lemma shellsB : Box b 0= Set.pi Set.univ (fun _:Axis=> Set.Ico 0 b):= by ext q; simp only [Set.mem_pi, Set.mem_univ,true_imp_iff,def_box,funext_iff,back,Pi.zero_apply,floor0 h]; rfl
lemma runner (i:Cover) : MeasurePreserving (MeasurableEquiv.addLeft (whole b i)) ( Shell b 0 ) ( Shell b i ) := by
    let F:= MeasurableEquiv.addLeft (whole b i); have hp : Shell b 0= planeF.restrict (F ⁻¹' Box b i):= by rw [show F ⁻¹' Box b i=Box b 0 from ?_]; ext x; simp only [Set.mem_preimage]; change back b (whole b i+x)=i ↔ back b x=0; rw [bo h]; simp only [add_eq_left]
    have hF : MeasurePreserving F planeF planeF:= measurePreserving_add_left planeF _; rw [hp]; exact ⟨hF.measurable,by rw [ ← F.measurableEmbedding.restrict_map, hF.map_eq] ⟩
def amountB (b:ℝ): ℝ := (2*π)⁻¹^4*b^4
lemma amount_pos : 0<amountB b:= by unfold amountB; positivity
lemma mass_box (i:Cover): Shell b i Set.univ= ENNReal.ofReal (amountB b):= by
    rw [ ← (runner h i).map_eq, MeasurableEquiv.map_apply, preimage_univ,Shell,Measure.restrict_apply_univ,shellsB h]; simp [ planeF,covMeasure, volume_pi_pi, amountB,Axis ]; rw [ ← ENNReal.ofReal_pow h.le, ← ENNReal.ofReal_mul (by positivity) ]; simp [← inv_pow, mul_pow]; -- π maybe
lemma Rview : rail b = Measure.sum (fun i: Cover=> ENNReal.ofReal (amountB b) • Measure.dirac (whole b i)):= by
    rw [rail,sum_shell b,Measure.map_sum tick_m.aemeasurable]; congr 1; funext i; have ht : (Tick b)=ᵐ[Shell b i] (fun _=> whole b i) := (ae_restrict_mem (box_m i)).mono (fun p hp=> congr_arg _ (show back b p=i from hp)); rw [Measure.map_congr ht,Measure.map_const,mass_box h i] -- name order
-- averaged translate; kernel cost irrespective Ω and angular properties.
def region (b:ℝ): Measure QP := ENNReal.ofReal (amountB b)⁻¹ • Shell b 0
lemma μback : ENNReal.ofReal (amountB b) • region b= Shell b 0:= by rw [region,smul_smul, ← ENNReal.ofReal_mul (amount_pos h).le]; simp [(amount_pos h).ne']
lemma μprob : IsProbabilityMeasure (region b) := ⟨ by rw [region,Measure.smul_apply,mass_box h,smul_eq_mul, ← ENNReal.ofReal_mul (inv_nonneg.mpr (amount_pos h).le)]; simp [(amount_pos h).ne']⟩
lemma average_b : MeasurePreserving (fun q:QP × QP=> q.1+q.2) ( (rail b).prod (region b) ) planeF := by
    haveI : IsProbabilityMeasure (region b):= μprob h; let ψ := fun p: QP × QP=>p.1+p.2; have hψ: Measurable ψ:= by unfold ψ; fun_prop
    refine ⟨hψ,?_⟩; change Measure.map ψ _=_; rw [Rview h,Measure.prod_sum_left,Measure.map_sum hψ.aemeasurable,sum_shell (b:=b)]; apply congr_arg Measure.sum; funext i; rw [ Measure.prod_smul_left,Measure.dirac_prod,Measure.map_smul, Measure.map_map hψ (by fun_prop), ← Measure.map_smul, μback h]; -- order patch
    exact (runner h i).map_eq
end YM.MS.Osc.Snap
