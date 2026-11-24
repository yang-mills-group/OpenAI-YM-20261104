import YM.MS.Fiddle.Bell
import YM.MS.City.Routes
/-!
# Folding momentum torus. Use City periodic chart.VP.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Fiddle
open Function Set Filter Finset Metric Real MeasureTheory Momentum Tone Landau Osc Osc.Snap Lattice
open scoped Topology ContDiff
variable {E:Type}[ NormedAddCommGroup E][NormedSpace ℝ E]{i:Cover}{v:QP}{b:ℝ}
lemma whole_t (i:Cover): whole tier i=Tone.rep i:= rfl
variable {μ:Measure QP}
abbrev Coasts (μ:Measure QP): Prop:=∀ i:Cover, Equ μ (rep i)
def stone (c:QP): QP≃ᵐ QP:= MeasurableEquiv.addLeft c
lemma spins (h:Coasts μ)(i:Cover): MeasurePreserving (stone ( whole tier i )) (μ.restrict deck) (μ.restrict (Box tier i)):= by
    let K:= stone (whole tier i); have hk: K ⁻¹' Box tier i = deck:= by ext x; change back tier (whole tier i+x)=i ↔ back tier x=0; rw [bo rising]; simp
    have he : MeasurePreserving K μ μ:= h i; exact ⟨he.measurable, by nth_rw 2 [← he.map_eq]; change Measure.map K (μ.restrict deck)=_; rw [K.restrict_map, hk]⟩ -- order rw maybe deck both
lemma crystal {F:QP→E}(h:Coasts μ)(hv: ∀ i:Cover,Periodic F (rep i))(hp: Integrable (fun i=> aisle i • F i) μ): (∫ i, aisle i • F i ∂μ ) = ∫ i in deck, F i ∂μ := by
   let G i:= aisle i • F i; let μ'(i:Cover):=μ.restrict (Box tier i); let V i p:= G (p+ whole tier i); have hS(i:Cover): (∫ p,G p ∂μ' i)=(∫ p,V i p ∂μ' 0):= by rw [← (spins h i).integral_comp']; exact integral_congr_ae (Filter.Eventually.of_forall fun p=> congr_arg G ( add_comm (whole tier i) p ))
   have hk(i:Cover): Integrable (V i) (μ.restrict deck):= by rw [show V i=G∘ stone (whole tier i) from funext fun p=>congr_arg G (add_comm p _)]; exact (spins h i).integrable_comp_of_integrable hp.restrict
   have he: μ=Measure.sum μ':= by nth_rw 1 [← Measure.restrict_univ (μ:= μ)]; rw [show (Set.univ:Set QP)=⋃ i:Cover,Box tier i from by ext q; simp, Measure.restrict_iUnion pub (fun i=>box_m i)] -- recursion simp?
   change (∫ i,G i ∂μ)=_; nth_rw 1 [he]; rw [ integral_sum_measure (show Integrable G (Measure.sum μ') from he ▸ hp) ]; simp_rw [hS]; rw [tsum_eq_sum (s:= Shells) (fun i hi=> ?_)]; swap; · rw [show (∫ p,V i p ∂μ' 0)=∫ p,(0:E)∂μ' 0 from ?_]; simp; exact integral_congr_ae (( ae_restrict_mem (box_m 0)).mono fun p hp=> by simp [V,G,door_off hi (show p∈deck from hp)] )
   change (∑ i∈Shells,∫ p in deck,V i p∂μ)=_; rw [ ← integral_finsetSum _ (fun i _=> hk i) ]; refine integral_congr_ae (( ae_restrict_mem (box_m 0)).mono fun p hp=>?_); change ∑ i∈ Shells, aisle (p + whole tier i) • F (p+whole tier i)=F p; simp_rw [show ∀ i: Cover,F (p+whole tier i)=F p from fun i=>hv i p, ← Finset.sum_smul]; rw [show _=_ from merit hp,one_smul] -- rewrite changed whole
lemma hemi : Coasts planeF:= fun i=> measurePreserving_add_left planeF (rep i) -- unused i
-- move Deck by π via triangle unit ball
abbrev north : QP:= fun _=>π
lemma trim_w : firstZone Axis=ᵐ[planeF]( stone north ⁻¹' deck):= by
   have hH : ∀ᵐ p ∂planeF,p∉sphere 0 π:= by simpa only [ae_iff, Classical.not_not, setOf_mem_eq] using Measure.addHaar_sphere_of_ne_zero planeF 0 Real.pi_pos.ne'
   filter_upwards [hH] with p hp
   have hz: ‖p‖≠π:= fun h=> hp (by simpa using h);
   apply propext; change p∈ firstZone Axis ↔ p∈ ( stone north ⁻¹' deck ); rw [inside_i,Set.mem_preimage, deck, shellsB rising];
   constructor; · intro h i _; have hx:‖p‖<π:=lt_of_le_of_ne ((pi_norm_le_iff_of_nonneg Real.pi_pos.le).mpr h) hz; have ht: |p i|<π:= lt_of_le_of_lt ( norm_le_pi_norm p i ) hx; obtain ⟨hi,hk⟩:= abs_lt.mp ht; change 0≤π+p i ∧ π+p i<2*π; constructor <;> linarith
   intro h i; obtain ht:= h i (Set.mem_univ _); change 0≤π+p i ∧ π+p i<2*π at ht; apply abs_le.mpr; constructor <;> linarith
lemma deck_c : MeasurePreserving (stone north) μzone (planeF.restrict deck):= by
    let K:=( stone north ); have he : MeasurePreserving K planeF planeF:= measurePreserving_add_left ..; exact ⟨ he.measurable, by rw [ show μzone = planeF.restrict (K ⁻¹' deck) from Measure.restrict_congr_set trim_w]; change (Measure.map K _)=_; rw [ ← K.restrict_map, he.map_eq ] ⟩
lemma shineZ {F:QP→ℂ}(h:Continuous F)(he: City.Gate F): (∫ p, (aisle p:ℂ) * F p ∂planeF)=∫ p,F p ∂μzone:= by
   rw [show (∫ p,( aisle p:ℂ)* F p ∂planeF)=_ from crystal (F:=F) hemi he (Continuous.integrable_of_hasCompactSupport ( door_sm.continuous.smul h ) (door_p.smul_right)), ← deck_c.integral_comp']; exact City.moves north h he
-- bug h.mul
end YM.MS.Fiddle
