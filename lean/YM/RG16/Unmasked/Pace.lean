import YM.RG16.Provider.Slower
import YM.MergeProof.North.Wicker
import YM.OPE.Height

/-!
# Uniform capture mesh for (literal) product readout

Window rate is **not** enough to buy a fixed inverse power of g. Choose the
usual `Λ` of qass (not `log Λ`), and buy exactly a powers-of-log overshoot on
actual geometry. This choice allows all positions in a fixed separated
*physical* shape, relative scale r on shell. Here one common capture k_
coarser than necessary for some smaller radii: enough for uniformity for this
calculation. We aren't asserting this pays the whole qass precision.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG16.Literal
open Function Filter Set Lattice RG OPE MergeProof MergeProof.Ribbons
open scoped Topology BigOperators
variable {G:Gauge}
set_option quotPrecheck false
section
variable (A:Family G) (hG:G.Simple)
local notation "Λ" => Lambda A.path.levels
local notation "β" => A.path.levels.clock.hatBeta
local notation "S" => A.S

lemma lambda_up (i:ℕ) : 2 < Λ i := lt_add_of_pos_right _ (Real.log_pos (A.path.levels.fits.delayed i))
lemma lambda_pos (i:ℕ) : 0 < Λ i := zero_lt_two.trans (lambda_up A i)

-- reusable for soft costs etc.
lemma normal_height : Height A.S atTop A.S.scale id 1 :=
   ⟨tendsto_id,tendsto_const_nhds.congr' (A.S.divergent.eventually_gt_atTop 0|>.mono fun _ hi=>
     (div_self hi.ne').symm)⟩
include hG
lemma lambda_mono : StrictMono Λ := by
  intro i j hij
  have he : β i < β j := add_lt_add_right (mul_lt_mul_of_pos_left (scale_mono A.S hij) (Gauge.slopeConstant_pos hG)) _
  exact add_lt_add_right (Real.log_lt_log (zero_lt_one.trans (A.path.levels.fits.delayed i)) he) _

lemma lambda_leads : Tendsto Λ atTop atTop := tendsto_atTop_add_const_left _ (2:ℝ)
    (Real.tendsto_log_atTop.comp (Next.Rank.Station.hat_rate _ hG))

lemma lambda_negligible : Tendsto (fun i => Λ i / A.S.scale i) atTop (𝓝 0):= by
   have hx:= (hut A hG).pitch
   simpa only [Lambda,add_div,add_zero] using!
     ((show Tendsto (fun i=> (2:ℝ)/A.S.scale i) atTop (𝓝 0) from
      tendsto_const_nhds.div_atTop A.S.divergent).add hx)

lemma levelT : RateIs atTop A.S.scale Λ 0 := by
    refine ⟨Eventually.of_forall (lambda_pos A),?_⟩
    apply squeeze_zero' ?_ ?_ (lambda_negligible A hG)
    · filter_upwards [A.S.divergent.eventually_gt_atTop 0] with i hi using
       div_nonneg (Real.log_nonneg (one_le_two.trans (lambda_up A i).le)) hi.le
    filter_upwards [A.S.divergent.eventually_gt_atTop 0] with i hi using div_le_div_of_nonneg_right (Real.log_le_self (lambda_pos A i|>.le)) hi.le

-- Choose capture to put EVEN furthest allowed r point in one b+1 cell, with room.
def Upper (L K:ℝ)(i:ℕ): ℝ := L*((Λ i)^(K+1))

lemma upper_slow (L K:ℝ) (hp:0<L) : RateIs atTop A.S.scale (Upper A L K) 0 :=
   ((RateIs.const A.S.divergent hp).mul ((levelT A hG).rpow (K+1))).swap (by ring)

variable (L K:ℝ) (hp:0<L) (hK: 0<K)
include hp in
lemma cluster_shrinks : Tendsto (fun i=> Upper A L K i * A.S.a i) atTop (𝓝 0) :=
   ((upper_slow A hG L K hp).mul (normal_height A).mesh).tends (by norm_num) A.S.divergent

/- choose first stage whose successor second mesh fits; keep Height measured on actual k. -/
omit hG
include hp in
lemma upper_pos (i:ℕ) : 0< Upper A L K i := mul_pos hp (Real.rpow_pos_of_pos (lambda_pos A i) _)
include hp in
lemma shift (i:ℕ) : ∃ b, A.S.a (b+2)< Upper A L K i * A.S.a i := by
    let h := A.S.shrinks.comp (tendsto_add_atTop_nat 2);
    exact (h.eventually (gt_mem_nhds (mul_pos (upper_pos A L K hp i) (A.S.a_pos i)))).exists

open scoped Classical in
noncomputable def port (i:ℕ) := Nat.find (shift A L K hp i)
set_option quotPrecheck false
local notation "b" => port A L K hp
open scoped Classical in
lemma step_bound (i:ℕ) : A.S.a (b i+2)< Upper A L K i * A.S.a i := Nat.find_spec (shift A L K hp i)

include hG
lemma port_grows : Tendsto b atTop atTop := by
    refine tendsto_atTop.mpr fun j => ?_
    filter_upwards [(cluster_shrinks A hG L K hp).eventually (gt_mem_nhds (A.S.a_pos (j+2)))] with i hi
    have hv : A.S.a (b i+2) < A.S.a (j+2) := lt_trans (step_bound A L K hp i) hi
    exact (Nat.le_of_add_le_add_right (A.S.strictAnti.le_iff_ge.mp hv.le)) -- orientation?

open scoped Classical in
lemma inner_bound : ∀ᶠ i in atTop, Upper A L K i * A.S.a i ≤ A.S.a (b i+1) := by
    filter_upwards [(port_grows A hG L K hp).eventually_gt_atTop 0] with i hi
    let v := b i-1
    have he : ¬A.S.a (v+2)< Upper A L K i*A.S.a i := Nat.find_min (shift A L K hp i) (by unfold v; change b i - 1 < b i; omega)
    rw [← (show v+2=b i+1 by unfold v; omega)]; exact le_of_not_gt he

include hK in
lemma port_small : ∀ᶠ i in atTop, b i+1 < i := by
    have hu : Tendsto (Upper A L K) atTop atTop:= Tendsto.const_mul_atTop hp ((tendsto_rpow_atTop (show 0<K+1 by linarith)).comp (lambda_leads A hG))
    filter_upwards [inner_bound A hG L K hp,hu.eventually_gt_atTop 1] with i hi hp
    exact (A.S.strictAnti.lt_iff_gt).mp ((lt_of_lt_of_le (lt_mul_of_one_lt_left (A.S.a_pos i) hp) hi))

-- Quantitative neighbour ratios (literal uses up to two stages). `hpace` is purchased already in this construction.
variable (hpace : ∀ i,((A.S.block i).val:ℝ) ≤ Real.log (Lambda A.path.levels i))
include hpace hK
lemma outer_bound : ∀ᶠ i in atTop, A.S.a (b i) / A.S.a i ≤
      Upper A L K i * (Λ i)^ (2:ℕ) := by
    filter_upwards [port_small A hG L K hp hK] with i h
    let m:= b i; let B j:=(A.S.block j).val
    have hs j (he:j ≤ i) : (B j:ℝ) ≤ Λ i:= (hpace j).trans
      ((Real.log_le_self (lambda_pos A j|>.le)).trans ((lambda_mono A hG).monotone he))
    let u:= Upper A L K i*A.S.a i; have hb(j:ℕ): (A.S.a (j+1))*(B j:ℝ) = A.S.a j:= by
       rw [A.S.a_step]; exact div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (A.S.block j).property.ne')
    have hu:0 ≤ u:= (mul_pos (upper_pos A L K hp i) (A.S.a_pos i)).le
    have hv' : A.S.a (m+1) ≤ u*Λ i := (hb (m+1)).symm.trans_le (mul_le_mul (step_bound A L K hp i).le (hs _ h.le) (by positivity) hu)
    rw [div_le_iff₀ (A.S.a_pos _)]
    calc
       _ ≤ u*Λ i*Λ i := (hb m).symm.trans_le (mul_le_mul hv' (hs _ (m.le_succ.trans h.le)) (by positivity) (mul_nonneg hu (lambda_pos A i).le))
       _ = _ := by unfold u; ring

lemma port_height : Height A.S atTop A.S.scale b 1 := by
    have hs: Height A.S atTop A.S.scale id 1:= normal_height A
    have he:=((upper_slow A hG L K hp).mul ((levelT A hG).power 2)).mul hs.mesh
    have hu: RateIs atTop A.S.scale (fun i=> A.S.a (b i)) (-1) := by
        refine hs.mesh.of_sandwich ((he.swap (by ring)).pays A.S.divergent) ?_ ?_ A.S.divergent
        · filter_upwards [port_small A hG L K hp hK] with i hi; exact A.S.strictAnti.antitone (le_trans (Nat.le_succ _) hi.le)
        filter_upwards [outer_bound A hG L K hp hK hpace] with i hi using (div_le_iff₀ (A.S.a_pos i)).1 hi
    refine ⟨port_grows A hG L K hp,?_⟩; simpa only [Schedule.scale,Real.log_inv,neg_div,neg_neg] using! hu.rate.neg
end
end YM.RG16.Literal
