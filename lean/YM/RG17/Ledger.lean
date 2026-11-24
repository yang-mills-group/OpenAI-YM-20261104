import YM.SharpGram.Precision.Coordinate
import YM.RG17.Layout
import YM.PertExtension.Running

/-!
`polylog` of hatted schedule; `g` comes from simultaneous limits of beta
on this actual Family. Costs on two scales. Only after inverse has only
polylog cost will we multiply a coupling error through it.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Filter Set OPE Extraction PertExtension
open SharpGram.Allow
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}{F:Spec.Final C f S}

-- keep make/coupling data the same throughout readouts
structure Ledger (L:Layout F) where
    simple : G.Simple
    actual : C.Makes
    B : ℕ→ℝ
    asymptotic : Running.isLimit C f B
    reach : Reach C L.level

variable {L:Layout F} (Z:Ledger L)
namespace Ledger
set_option quotPrecheck false
local notation "m"=>L.level
local notation "hat"=> C.path.levels.clock.hatBeta
local notation "P"=>fun i:ℝ=>hat (m i)
local notation "ρ"=>OPE.run

abbrev g (Z:Ledger L) (r:ℝ):ℝ:=coupling (Z.B (L.level r))
abbrev Λ (_:Ledger L) (r:ℝ):ℝ:=Lambda C (m r)

lemma paidBand (r:ℝ):Z.B (m r) ∈ Band C (m r) := Running.band f C Z.actual Z.simple Z.asymptotic _
lemma positive (r:ℝ):0<Z.g r:= coupling_pos (Z.paidBand r)
lemma small : ∀ᶠ r in home,Z.g r ≤1:= (Z.reach.growing.eventually (later C Z.simple)).mono (fun r hr=>hr _ (Z.paidBand r))
lemma above (r:ℝ):1≤Z.Λ r := by unfold Λ Lambda; linarith only [Real.log_nonneg (C.path.levels.fits.delayed (m r)).le]
lemma fuse_at (r:ℝ) : Tendsto (fun i : ℕ×ℕ=> Pert.Asymptotics.regulatorRun C i.1 i.2 (L.level r)) f.fuse (𝓝 (Z.g r)) :=
    ((Z.asymptotic _).sqrt).inv₀ (Real.sqrt_pos.mpr (beta_pos (Z.paidBand r))).ne'

lemma betaTail : Tendsto (fun r=> Z.B (m r) / ρ r) home (𝓝 G.slopeConstant) := by
    have h := ((Running.discrete f C Z.actual Z.asymptotic).comp Z.reach.growing).mul Z.reach.nearby
    rw [mul_one,← Running.slope] at h
    apply h.congr'; filter_upwards [(C.S.divergent.comp Z.reach.growing).eventually (eventually_gt_atTop 0)] with i hi
    change Z.B _/C.S.scale (m i)*(_/(_))= _
    change 0<C.S.scale (m i) at hi; field_simp
lemma contour : Tendsto (fun r=> Z.g r^2 * ρ r) home (𝓝 G.slopeConstant⁻¹) := by
   refine (Z.betaTail.inv₀ (Gauge.slopeConstant_pos Z.simple).ne').congr ?_
   intro i; rw [g,coupling,inv_pow,Real.sq_sqrt (beta_pos (Z.paidBand i)).le]; rw [inv_div,div_eq_mul_inv,mul_comm]
lemma coarse_g : RateIs home ρ Z.g 0:= by
    have h:=Gauge.slopeConstant_pos Z.simple
    let b (i:ℝ):= Z.B (m i)
    have hb:RateIs home ρ b 0:=by
       have ht:RateIs home ρ ρ 0:= ⟨ageLarge.eventually_gt_atTop 0, Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp ageLarge⟩
       have hc:RateIs home ρ (fun i=> b i/ρ i) 0:= ⟨Z.betaTail.eventually (lt_mem_nhds h),(Z.betaTail.log h.ne').div_atTop ageLarge⟩
       have hw:= hc.mul ht; rw [add_zero] at hw
       exact hw.congr ((ageLarge.eventually_gt_atTop 0).mono (fun i hi=> div_mul_cancel₀ _ hi.ne'))
    change RateIs home ρ (fun i=> (Real.sqrt (b i))⁻¹) 0
    simpa only [zero_mul,mul_zero,neg_zero,g,coupling,Real.sqrt_eq_rpow] using (hb.rpow (1/2:ℝ)).inv

/-- using polynomial Λ (the frame for costs, not its beta as coupling!) -/
lemma dominant (j:ℕ) : Tendsto (fun r=> Z.g r * Z.Λ r^j) home (𝓝 0) := by
     let D (i:ℝ):=hat (m i)
     have hD: Tendsto D home atTop:= (Next.Rank.Station.hat_rate C.path.levels Z.simple).comp Z.reach.growing
     have hx(r):0≤Z.g r * Z.Λ r^j :=mul_nonneg (Z.positive r).le (pow_nonneg (zero_le_one.trans (Z.above r)) j)
     let K (i:ℝ):= Real.log (D i)
     have he: Tendsto (fun r=> K r^j/Real.sqrt (D r)) home (𝓝 0):=by
         have h:= (isLittleO_log_rpow_rpow_atTop (j:ℝ) (s:= (1/2:ℝ)) (by norm_num)).tendsto_div_nhds_zero
         simpa only [Real.rpow_natCast,Real.sqrt_eq_rpow,Function.comp_def,K] using h.comp hD -- K definitional?
     refine squeeze_zero' (Eventually.of_forall hx) (g:=fun i=> (2*3^j)*(K i^j/Real.sqrt (D i))) ?_ (by simpa only [mul_zero] using he.const_mul (2*3^j))
     filter_upwards [(Real.tendsto_log_atTop.comp hD).eventually_ge_atTop 1] with i hi
     have hn:D i*Z.g i^2 ≤ 2:= caps (Z.paidBand i)
     have hp: 1 ≤ K i:= hi
     have hb:0<D i:=zero_lt_one.trans (C.path.levels.fits.delayed (m i))
     have hg: Z.g i*Real.sqrt (D i) ≤ 2 := by
         have h:(Z.g i*Real.sqrt (D i))^2≤2:=by rw [mul_pow,Real.sq_sqrt hb.le, mul_comm]; exact hn
         nlinarith only [h]
     have hj: Z.Λ i ≤ 3 * K i:= by change 2+K i≤_; linarith
     apply (mul_le_mul ((le_div_iff₀ (Real.sqrt_pos.mpr hb)).mpr hg) (pow_le_pow_left₀ (zero_le_one.trans (Z.above i)) hj j) (pow_nonneg (zero_le_one.trans (Z.above i)) j) (by positivity)).trans_eq
     rw [mul_pow]; ring
lemma vanishes : Tendsto Z.g home (𝓝 0) := by simpa only [pow_zero,mul_one] using Z.dominant 0
lemma cheap : RateLE home ρ Z.Λ 0 := by
    have h:RateIs home ρ (fun i=>(Z.g i)⁻¹) 0:=by simpa only [neg_zero] using Z.coarse_g.inv
    apply RateLE.of_norm_le (h.pays ageLarge)
    filter_upwards [(Z.dominant 1).eventually (gt_mem_nhds zero_lt_one)] with i hi
    rw [Real.norm_of_nonneg (zero_le_one.trans (Z.above i)),← one_div]; apply (le_div_iff₀ (Z.positive i)).mpr; rw [mul_comm,← pow_one (Z.Λ i)]; exact hi.le
end Ledger
end YM.RG17
