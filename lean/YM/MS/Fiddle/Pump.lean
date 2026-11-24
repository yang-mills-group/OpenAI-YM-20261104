import YM.MS.Fiddle.Reap
/-!
# Wide-zone rapid budget after folding
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Fiddle
open Function Set Filter Finset Metric Real MeasureTheory Momentum Tone Landau Osc Osc.Snap Lattice
open scoped Topology ContDiff
variable {I E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {a b:ℝ} {S:Scale I}{F G:I→ QP→ ℂ}{K:I→ℝ}
lemma in_wide (u:ℝ)(h:|u|≤wide):∃ k:ℤ, |u+tier*k|≤π ∧ |u|≤3*|u+tier*k|:= by
    by_cases hp:|u|≤π; · exact ⟨0,by simpa using hp,by simp; linarith [abs_nonneg u]⟩ -- simp
    rcases le_total 0 u with hx|hx
    · rw [abs_of_nonneg hx] at *; refine ⟨-1,?_,?_⟩ <;> simp only [ Int.cast_neg, Int.cast_one, mul_neg,mul_one,tier, abs_of_nonpos (show _ by unfold wide at h; linarith:(u+- (2*π))≤0)] <;> unfold wide at h <;> linarith [Real.pi_pos]
    rw [abs_of_nonpos hx] at *; refine ⟨1,?_,?_⟩ <;> simp only [Int.cast_one,mul_one,tier,abs_of_nonneg (show 0≤u+2*π by unfold wide at h; linarith [Real.pi_pos])] <;> unfold wide at h <;> linarith
lemma wideZ (v:QP)(h:‖v‖≤ wide): ∃ k:Cover, v+rep k∈firstZone Axis ∧ ‖v‖≤3*‖v+rep k‖:= by
    choose k hk hx using fun i=> in_wide (v i) ((pi_norm_le_iff_of_nonneg risingW.le).mp h i);
    have hs :∀ i:Axis, v i+tier*k i=(v+rep k) i:=fun i=>rfl; refine ⟨k,(inside_i _).mpr (fun i=>hk i), (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i=>(hx i).trans ?_⟩; rw [hs]; exact mul_le_mul_of_nonneg_left (norm_le_pi_norm (v+rep k) i) (by norm_num :0 ≤ (3:ℝ))
abbrev located (_:I): Set QP:= firstZone Axis
abbrev Wid (_:I): Set QP:= Metric.closedBall 0 wide
omit [NormedSpace ℝ E] in
lemma weightUp (S:Scale I)(i:I)(p q:E)(h:‖p‖≤ 3*‖q‖) (b:ℕ)(ha:0≤ a): a / S.weight i q^b ≤ (3^b)*(a / S.weight i p^b):= by
    have he:S.weight i p≤ 3*S.weight i q:= by unfold Scale.weight; have ht:= S.pos i; nlinarith
    rw [ ← mul_div_assoc, mul_comm (3^b:ℝ), div_le_div_iff₀ (pow_pos (S.weight_pos ..) _) (pow_pos (S.weight_pos ..) _), mul_assoc,← mul_pow]; gcongr; exact ( S.weight_pos i p ).le
abbrev Zone (S:Scale I)(F:I→QP→ℂ)(b:I→ℝ): Prop:= Line S located F b
def Veiled (F:QP→ℂ) : Prop:=∀ i:Cover,∃ v:ℂ,‖v‖=1∧ (fun q=> F (q+rep i))=v • F
lemma cityLine {G: Gauge} {L:Plane.Flux (Branch G Axis) QP ℂ}(h:City.Near L)(i j:Branch G Axis): Veiled (L i j):= by
   intro x; refine ⟨_,?_,funext (fun k=> h x i j k)⟩; rw [norm_mul]; change ‖Tone.bill _ _‖ * ‖Tone.bill _ _‖=1; rw [Tone.bill_norm,Tone.bill_norm,mul_one] -- BH location
lemma noPole (h:Zone S F K)(i:I): 0≤ K i:= by simpa using (h 0).nonneg i 0 (show (0:QP)∈ firstZone Axis from Metric.mem_closedBall_self Real.pi_pos.le)
lemma ride (hf:Zone S F K)(hF:∀ i,Veiled (F i)): Line S Wid F K:= by
    intro b; refine ⟨(hf b).smooth,fun j=>?_⟩; obtain ⟨C,hC,w,hw⟩:= (hf b).quoted j; refine ⟨ C*3^b,mul_pos hC (by positivity),w,fun i p hp=>?_⟩; dsimp only; obtain ⟨k,hk,hX⟩:=wideZ p (by simpa [Scale.strict] using hp); let L:=p+rep k; obtain ⟨v,hv,h⟩:= hF i k; have he:0≤ S.length i^j:= pow_nonneg ( S.pos i|>.le ) j; have h': iteratedFDeriv ℝ j (F i) L = v • iteratedFDeriv ℝ j (F i) p:= by unfold L; rw [← iteratedFDeriv_comp_add_right,h]; exact iteratedFDeriv_const_smul_apply ( (hf b).smooth i|>.contDiffAt.of_le (by exact_mod_cast le_top))
    rw [ ← one_mul ‖iteratedFDeriv _ _ _ _‖, ← hv, ← norm_smul, ← h']; apply ( hw i _ hk ).trans; change C* S.basic i^w*( K i / S.weight i L^b * S.length i^j ) ≤ _; simp only [ Scale.strict ]; conv_rhs=> rw [mul_right_comm C, mul_assoc ( C*_ ), ← mul_assoc ( 3^b:ℝ)]; 
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (weightUp S i p L hX b (noPole hf i)) he) (by have h:=S.basic_pos i; positivity)
lemma β_cost (H:∀ i,1 ≤ S.length i)(D:I→Set QP): Costs ( S.strict D ) S (fun (_:I)p=> aisle p) (fun _ _=>1) := by
    refine ⟨ fun _=> door_sm, fun j=>?_⟩; obtain ⟨C,hC,h⟩:= total_bd j; refine ⟨_,hC,0,fun i p hp=> (h p).trans ?_⟩; simp only [ Scale.strict, pow_zero, mul_one,one_mul ]; exact le_mul_of_one_le_right hC.le (one_le_pow₀ (H i))
where
 total_bd (j:ℕ): ∃ C:ℝ,0<C ∧ ∀ i, ‖iteratedFDeriv ℝ j aisle i‖≤C:= by
    let F:= iteratedFDeriv ℝ j aisle; have hk:HasCompactSupport F:= door_p.iteratedFDeriv j; have hi : Continuous ( norm ∘ F ):= continuous_norm.comp (door_sm.continuous_iteratedFDeriv (by exact_mod_cast le_top)); obtain ⟨v,h⟩:= (hk.image hi).bddAbove; refine ⟨max v 1,lt_max_of_lt_right zero_lt_one, fun i=>?_⟩; by_cases hx:i∈ tsupport F; · exact le_max_of_le_left (h (Set.mem_image_of_mem _ hx))
    rw [show iteratedFDeriv ℝ j aisle i=0 from image_eq_zero_of_notMem_tsupport hx,norm_zero]; simp
lemma β_proven (hp: Line S Wid F K)(H:∀ i,1≤ S.length i)(he:∀ i, 0≤ K i) : Line S (fun _=>Set.univ) (fun i p=>(aisle p:ℂ)*F i p) K:= by
   intro b; obtain hx : Costs ( S.strict Wid ) S (fun i p=>(aisle p:ℂ)*F i p) (fun i p=> K i/S.weight i p^b):= by simpa only [one_mul] using ((β_cost H _).ofReal.mul (hp b))
   refine ⟨hx.smooth, fun j=>?_⟩; obtain ⟨C,hC,w,hw⟩:= hx.quoted j; refine ⟨C,hC,w, fun i p h=>?_⟩; by_cases ht:p∈ Wid i; · exact hw i p ht
   dsimp only; rw [show iteratedFDeriv ℝ j _ _=0 from ?_,norm_zero]; swap
   · have hV: (fun p=> (aisle p:ℂ)*F i p)=ᶠ[𝓝 p] (0:QP→ℂ) := by
         filter_upwards [(isClosed_closedBall (x:=(0:QP))).isOpen_compl.mem_nhds (show p∈(Wid i)ᶜ from ht) ] with v hv; rw [show aisle v=0 from Classical.byContradiction fun h=> hv (Metric.mem_closedBall.mpr (by simpa using door_n h))]; simp
     rw [(hV.iteratedFDeriv ℝ j).eq_of_nhds]; simp
   simp only [Scale.strict]; have hs:= S.weight_pos i p; have hc:= S.basic_pos i; have hp:= S.pos i; have hh:= he i; positivity
lemma folding (h:Zone S F K)(hu:∀ i, Veiled (F i))(ht:∀ i,1≤S.length i): Line S (fun _=>Set.univ) (fun i p=>(aisle p:ℂ)*F i p) K:= β_proven (ride h hu) ht (noPole h)
end YM.MS.Fiddle
