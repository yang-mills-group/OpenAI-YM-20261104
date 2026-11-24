import YM.MSbar.Heath.Charts
/-!
# Detailed-balance ticket. Compare probability of pulling under real shift, not
summed-tail mixing assumption. Unnormalized ratios tested BEFORE arithmetic.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath
open Lattice Wilson RG Function Filter MeasureTheory Push.Local Push Push.AbsoluteSums WilsonStartup
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{c f:Side}{S:StepData c f}{U W:Config G f}{V:Config G c}{R:Rep G f}{σ C T a v x g r δ w:ℝ}
open Finset
open YM.MSbar.Bulk SectorNext.Vacuum
local notation "N" => Config G f
variable {D B A A' X Y Z:Set (Config G f)}{τ:Config G f → Config G f}{J hE: Config G f→ℝ}
set_option quotPrecheck false
local notation "JJ"=>prior G f
def boundPress (S:StepData c f)(R:Rep G f)(V:Config G c)(U:Config G f):= R.eval U*S.density R.beta U V
-- Transport on actual density. Domain T.B. nonnegative.Charge) Define partial for P reweight.
def spec (A:Set N) : N→ℝ:=A.indicator (fun _=>1)
local notation "□"=> boundPress S R V
variable (h: Admitted V R S σ C δ T w)
include h
lemma measure_out : (∫ U, □ U∂ JJ)= S.push R.beta R.eval V:=by unfold boundPress StepData.push; simp only [smul_eq_mul]; exact integral_congr_ae (Eventually.of_forall (fun i=> mul_comm ..))
lemma bound_ink : Envelope (boundPress S R V):=by
    obtain ⟨η,ht⟩:=h.kernel.bound
    refine Envelope.mul (R.envelope h.lawful) ⟨?_,η, fun i=> (Real.norm_of_nonneg (h.kernel.positive i V)).trans_le (ht i V)⟩
    change Measurable ((fun i:N × Config G c => S.density R.beta i.1 i.2) ∘ (fun i:N=>(i,V))); exact h.kernel.meas.comp (show Measurable (fun i:N => (i,V)) from measurable_id.prodMk measurable_const)
lemma bound_positive (U) : 0 ≤ boundPress S R V U:=mul_nonneg (h.positive _) (h.kernel.positive ..)
lemma readsX (f':Config G f→ℝ) : Bulk.expect S R V f' = (∫ U,□ U*f' U∂ JJ)/(S.push R.beta R.eval V):=by unfold Bulk.expect; apply congr_arg (· / S.push R.beta R.eval V); unfold StepData.push boundPress; simp only [smul_eq_mul]; exact integral_congr_ae (Eventually.of_forall (fun i=>by simp only [Pi.mul_apply]; ring))
lemma chance_pos (hA:MeasurableSet A):0 ≤ chance S R V A:=by
    have he:= nn V h (show Envelope (spec A) from Envelope.piece hA (Envelope.const (1:ℝ)) (Envelope.const _)) (Envelope.const (0:ℝ)) (fun i=> Set.indicator_nonneg (fun _ _=>zero_le_one) _); rw [e_const V h 0] at he; exact he -- private ind shadow
lemma chance_g (hA:MeasurableSet A):chance S R V A ≤1 := (c_mono V h hA MeasurableSet.univ (Set.subset_univ A)).trans (show chance S R V Set.univ ≤1 from le_of_eq (by unfold chance; rw [Set.indicator_univ]; exact e_const _ h _))
-- A flow only on sets.D. Integrate with nonnegative envelopes.Need indicator frame equality.
structure Moving (V:Config G c)(R:Rep G f)(S:StepData c f)(F:Set (Config G f)→Prop)(D:Set (Config G f))(τ:Config G f → Config G f)(J:Config G f → ℝ):Prop where
    domain:MeasurableSet D
    measurable: Measurable τ
    jac: Envelope J
    exchange (A Y:Set (Config G f)) : MeasurableSet A→ MeasurableSet Y → F A→F Y → A⊆D → Set.MapsTo τ A Y→ (∫ U,A.indicator (fun U=> J U*boundPress S R V (τ U)) U∂prior G _) ≤ ∫ U,Y.indicator (boundPress S R V) U∂prior G _
variable {F:Set (Config G f)→Prop}
-- Body for normalization & ∂_x.Effect.
variable (K: Moving V R S F D τ J)
include K
lemma power_shift (hA:MeasurableSet A)(hB:MeasurableSet B)(hF:F A)(hG:F B)(ht:A⊆D)(hf:Set.MapsTo τ A B){g:N→ℝ}(hg:Envelope g)(hv:∀ x,x ∉ A → g x = 0)(hx: ∀ x∈ A, boundPress S R V x*g x ≤ v*(J x*boundPress S R V (τ x))) (hp:0≤v): Bulk.expect S R V g ≤ v*chance S R V B:=by
    rw [show chance S R V B= Bulk.expect S R V (spec B) from rfl, readsX h, readsX h, ← mul_div_assoc]; apply div_le_div_of_nonneg_right _ h.mass.le
    let s U:= □ U*g U; let t U:= J U*□ (τ U); let m:= A.indicator t
    have he:=bound_ink h
    obtain ⟨d,hH⟩:= he.cost
    have ht' : Envelope t:= K.jac.mul ⟨he.meas.comp K.measurable,d,fun _=> hH _⟩
    have hi(i): s i ≤ v*m i:=by
        unfold s m; by_cases hi:i∈A; rw [Set.indicator_of_mem hi]; exact hx i hi; rw [Set.indicator_of_notMem hi,hv i hi,mul_zero,mul_zero]
    have hb:= integral_mono ((he.mul hg|>.integrable JJ)) (((ht'.integrable JJ).indicator hA).const_mul v) hi; rw [integral_const_mul] at hb
    refine hb.trans (mul_le_mul_of_nonneg_left ((K.exchange A B hA hB hF hG ht hf).trans_eq ?_) hp)
    apply integral_congr_ae; filter_upwards with i; by_cases hh:i∈B; rw [Set.indicator_of_mem hh, show spec B i=1 from Set.indicator_of_mem hh _,mul_one]; rw [Set.indicator_of_notMem hh,show spec B i= 0 from Set.indicator_of_notMem hh _,mul_zero]
lemma budget_shift (hA:MeasurableSet A)(hB:MeasurableSet B)(hF:F A)(hG:F B)(ht:A⊆D)(hf:Set.MapsTo τ A B)(hx: ∀ x∈ A, boundPress S R V x ≤ v*(J x*boundPress S R V (τ x))) (hp:0≤v): chance S R V A ≤ v*chance S R V B:=power_shift h K hA hB hF hG ht hf (Envelope.piece hA (Envelope.const _) (Envelope.const _)) (fun i hi=> Set.indicator_of_notMem hi _) (fun i hi=>by
     rw [Set.indicator_of_mem hi, mul_one]; exact hx i hi) hp
-- energy overcoming local.Ratio. pay without a pointwise log
variable {X:Support f}
lemma energy_shift (H:Psalm S R a r) (L:MergeProof.Menu.Arsenal R)(ha:0≤r)(hw:flags a V=∅)(hP: Tracks R X τ (spec A) S 1)
    (hA:MeasurableSet A)(hB:MeasurableSet B)(hF:F A)(hG:F B)(ht:A⊆ D)(hT:Set.MapsTo τ A B)(hp:0≤v)(hc: Continuous R.eval) (hv:∀ U:N, 0< R.eval U) (hz : ∀ U∈A, S.density R.beta U V * Real.exp (R.exponent U) ≤ v*(J U*S.density R.beta (τ U) V)*Real.exp (R.exponent (τ U))):
    chance S R V A ≤ v*chance S R V B+r*(R.p.mass X 2*Real.exp (X.card*w)):=by
    let f:N→ℝ:= fun i=> R.eval (τ i)/R.eval i * Real.exp (R.exponent i-R.exponent (τ i))
    let g i:= spec A i*(f i-1)
    have he:= R.exponentEnv h.lawful; obtain ⟨b,hb⟩:=he.cost
    have hE:Envelope f:=by
       have ht:= R.envelope h.lawful; have hi: Continuous fun i=>(R.eval i)⁻¹:= hc.inv₀ fun i=>(hv i).ne'
       obtain ⟨b,hH⟩:=(isCompact_range (show Continuous _ from hi.norm)).bddAbove; obtain ⟨d,hB⟩:=ht.cost
       unfold f; simp_rw [div_eq_mul_inv, sub_eq_add_neg]
       exact (((show Envelope (R.eval∘τ) from ⟨ht.meas.comp K.measurable,d,fun i=> hB _⟩).mul ⟨hi.measurable,b,fun i=> hH ⟨i,rfl⟩⟩).mul ((he.add ((show Envelope (R.exponent∘τ) from ⟨he.meas.comp K.measurable,_,fun i=>hb _⟩).neg)).exp))
    let q:= spec A; have hq:Envelope q:=Envelope.piece hA (Envelope.const _) (Envelope.const _)
    have hg:Envelope g:=by unfold g; simp_rw [sub_eq_add_neg]; exact hq.mul (hE.add (Envelope.const _))
    have hW: g + q = fun i=>q i*f i:= funext (fun i=> by unfold g q; simp only [Pi.add_apply]; ring)
    let cA:= chance S R V A
    have hu: Bulk.expect S R V (g+q)= Bulk.expect S R V g+cA:=e_sum V h hg hq; rw [hW] at hu
    have hb: Bulk.expect S R V (fun i=> q i*f i) ≤ _ := power_shift h K hA hB hF hG ht hT (hq.mul hE) (fun i hi=>by rw [show q i=0 from Set.indicator_of_notMem hi _,zero_mul]) (fun i hi=>by
      rw [show q i=1 from Set.indicator_of_mem hi _,one_mul]
      have hh:S.density R.beta i V*Real.exp (R.exponent i-R.exponent (τ i)) ≤ v*(J i*S.density R.beta (τ i) V):=by rw [Real.exp_sub, ← mul_div_assoc]; exact (div_le_iff₀ (Real.exp_pos _)).mpr (hz i hi)
      unfold boundPress f
      have hi: (R.eval i*S.density R.beta i V)*(R.eval (τ i)/R.eval i* Real.exp (R.exponent i-R.exponent (τ i)))= R.eval (τ i)*(S.density R.beta i V* Real.exp (R.exponent i-R.exponent (τ i))):=by field_simp [(hv i).ne']
      rw [hi]; exact (mul_le_mul_of_nonneg_left hh (hv (τ i)).le).trans_eq (by ring)) hp
    have hK:=receipt V h hP L H ha hw hv; change |Bulk.expect S R V g|≤_ at hK; simp only [one_mul] at hK
    rw [hu] at hb; change cA≤ _; linarith only [hb,(abs_le.mp hK).1]
end YM.MSbar.Heath
