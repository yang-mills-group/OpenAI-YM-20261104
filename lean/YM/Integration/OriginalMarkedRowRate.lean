import YM.Integration.OriginalMarkedRowPrice
import YM.Integration.WilsonAxialRates
import YM.Integration.ActualCoarseStagePrice
import YM.IterationFour.Running
import YM.Next.SCHEDULE.Support

/-! One further genuinely purchased Taylor order pays the entire
four-dimensional support-hit sum, including the plaquettes inspected
by the ordinary health mask, on the original calendar. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.OriginalMarkedRowRate
open Filter Function Set Finset Lattice Wilson RG RG.Supply
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open Push.GridApprox.Attach GapsLocal.Renew
open OriginalMarkedRunAction OriginalMarkedRowCovariance OriginalMarkedRowPrice
open scoped Classical BigOperators Topology
variable {G : Gauge} {n : Side}

private theorem contact {P S : Support n} (h : ¬Disjoint (inspected P) S) :
    ¬Disjoint (inspected S) P := by
  obtain ⟨v,hv,hs⟩ := Finset.not_disjoint_iff.mp h
  rcases Finset.mem_union.mp hv with hp|hp
  · exact Finset.not_disjoint_iff.mpr ⟨v,Finset.mem_union_left _ hs,hp⟩
  obtain ⟨face,_,hi⟩ := Finset.mem_biUnion.mp hp
  by_cases empty : Disjoint P (touched face)
  · simp [empty] at hi
  have ht : v∈touched face := by simpa only [if_neg empty] using hi
  obtain ⟨u,hu,hface⟩ := Finset.not_disjoint_iff.mp empty
  have hit : ¬Disjoint S (touched face) := Finset.not_disjoint_iff.mpr ⟨v,hs,ht⟩
  apply Finset.not_disjoint_iff.mpr
  exact ⟨u,Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨face,Finset.mem_univ _,
    by simpa only [if_neg hit] using hface⟩),hu⟩

theorem mask_contact (P S : Support n) :
    (¬Disjoint (inspected P) S) ↔ ¬Disjoint P (inspected S) := by
  constructor
  · exact fun h d => contact h d.symm
  · exact fun h => contact (fun d => h d.symm)

theorem mask_size (S : Support n) : (inspected S).card ≤ S.card*17^4 :=
  (Finset.card_le_card (Next.Scheduling.flag_layer S)).trans (Lattice.Corona.halo_size S 8)

variable (R : Run G) {N p m d : ℕ} (hm : m<N)
local notation "Ω" => Config G (R.family.side m p)
local notation "I" => remainder R (p:=p) hm d
local notation "B" => R.alloy.B.a.budget m
local notation "g" => Pert.Asymptotics.regulatorRun R.family N p (m+1)

theorem field_local (A : Comparison R (p:=p) hm d) (i : ℕ) :
    LocalOn (inspected ((I).reg i).support) (local_weight R (p:=p) hm d i) := by
  let X := ((I).reg i).support
  have loc : UsesFinal (B).threshold X (row R (p:=p) hm d i) := by
    intro U V h flags
    have same : Healthy (B).threshold X U ↔ Healthy (B).threshold X V := by
      simp only [Healthy,Finset.disjoint_iff_inter_eq_empty,flags]
    by_cases healthy : Healthy (B).threshold X U
    · exact (masked_eq _ _ _ _ healthy).trans (((A.posterior.cut.regular.smooth i).sites U V h).trans
        (masked_eq _ _ _ _ (same.mp healthy)).symm)
    · exact (masked_ne _ _ _ _ healthy).trans (masked_ne _ _ _ _ (mt same.mpr healthy)).symm
  intro U V h
  exact congrArg (fun t : ℝ => (Real.exp (-t):ℂ)) ((UsesFinal.allReads _ _ _ loc) U V h)

include hm in
private theorem fine_cap (hG : G.Simple) :
    g ≤ 2*(Real.sqrt (R.alloy.B.a.clock.hatBeta m))⁻¹ := by
  let L := R.alloy.B.a
  have upper : g ≤ 2*(Real.sqrt (L.clock.hatBeta (m+1)))⁻¹ := (IterationFour.Currency.hat_g R.makes N p (m+1) hm).2
  exact upper.trans (mul_le_mul_of_nonneg_left
    (inv_anti₀ (Real.sqrt_pos.mpr (zero_lt_one.trans (L.fits.delayed m)))
      (Real.sqrt_le_sqrt (ActualCoarseStagePrice.hatBeta_mono L hG (Nat.le_succ m)))) (by norm_num))

theorem shell_clock (hG : G.Simple) (v : ℝ) (hv : 0<v) :
    ∀ᶠ m : ℕ in atTop, ∀ N p, m<N →
      hitConstant (((R.alloy.B.a.budget m).B+1)*shell_width R) *
        Pert.Asymptotics.regulatorRun R.family N p (m+1) ≤ v := by
  let L := R.alloy.B.a
  let r := shell_width R
  let C := ∑' i,polyExp i
  have hC : 0≤ C := tsum_nonneg fun i => (polyExp_pos i).le
  let k := 12*r+5
  have limit := (WilsonAxialRates.controlled L hG k 1 4 0 (s:=1/2) (by norm_num)).const_mul (2*C)
  rw [mul_zero] at limit
  filter_upwards [limit.eventually (ge_mem_nhds hv)] with m point N p hm
  let b := (L.budget m).B
  let β := L.clock.hatBeta m
  let Y := 1+(WilsonAxialReach.reach L k 1 m:ℝ)
  have size : (((leg ((b+1)*r)*2+1:ℕ):ℝ)) ≤ Y := by
    dsimp [Y,WilsonAxialReach.reach,k,leg]
    push_cast
    nlinarith only [show 0≤(b:ℝ) by positivity]
  have K : hitConstant ((b+1)*r) ≤ Y^4*C :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) size 4) hC
  have bg : 0 ≤ Pert.Asymptotics.regulatorRun R.family N p (m+1) :=
    (IterationFour.Currency.g_pos R.makes N p (m+1) hm).le
  calc hitConstant ((b+1)*r)*Pert.Asymptotics.regulatorRun R.family N p (m+1) ≤
        (Y^4*C)*(2*(Real.sqrt β)⁻¹) := mul_le_mul K (fine_cap R hm hG) bg (mul_nonneg (by positivity) hC)
       _ = (2*C)*(Y^4*(OPE.Therm.sigmaU L m)^0/β^(1/2:ℝ)) := by rw [pow_zero,mul_one,Real.sqrt_eq_rpow]; ring
       _ ≤ _ := point

private theorem fine_small (hG : G.Simple) :
    ∀ᶠ m : ℕ in atTop, ∀ N p, m<N →
      Real.sqrt 2 * Pert.Asymptotics.regulatorRun R.family N p (m+1) ≤ 1 := by
  have t := IterationFour.Currency.g_small hG R.makes (Real.sqrt 2)⁻¹ (inv_pos.mpr (Real.sqrt_pos.mpr (by norm_num)))
  obtain ⟨k,hk⟩ := eventually_atTop.mp t
  filter_upwards [eventually_ge_atTop k] with m h N p hm
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  exact (mul_le_mul_of_nonneg_left (hk (m+1) (h.trans (Nat.le_succ m)) N p hm).le hs.le).trans_eq (mul_inv_cancel₀ hs.ne')

/-- Uniformly in every actual upper cutoff, period, carrier and signed
test, the higher-order purchase pays an arbitrarily small multiple of
the requested power for all physically touching omitted interactions. -/
theorem purchased (hG : G.Simple)
    (marks : Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fee : Mallow.RG12.Earned (checkout G) R.kit.shape R.alloy.delay)
    (q : ℕ) (v : ℝ) (hv : 0<v) :
    ∀ᶠ m : ℕ in atTop, ∀ N p (hm : m<N) (S : Support (R.family.side m p))
      (f : Config G (R.family.side m p)→ℂ) (M : ℝ), Measurable f → 0≤M → (∀ U, ‖f U‖≤M) →
      let rem := remainder R (p:=p) hm (q+1)
      SumBudget (fun i => if ¬Disjoint (inspected (rem.reg i).support) S then
        ‖local_ratio R (p:=p) hm (q+1) i f‖ else 0)
        (v*S.card*M*(Pert.Asymptotics.regulatorRun R.family N p (m+1))^(q+1)) := by
  let c := (17:ℝ)^4*(2*Real.exp 2)*(Real.sqrt 2)^(q+2)
  have hc : 0<c := by dsimp [c]; positivity
  filter_upwards [calendar R hG marks fee (q+1),shell_clock R hG (v/c) (div_pos hv hc),
    fine_small R hG] with m bought shell tiny N p hm S f M meas hM cap
  let t := Pert.Asymptotics.regulatorRun R.family N p (m+1)
  let K := hitConstant (((R.alloy.B.a.budget m).B+1)*shell_width R)
  let e := (Real.sqrt 2*t)^(q+2)
  have A := bought N p hm
  have paid := carrier R hm A (inspected S) f meas M hM cap
  simp_rw [← mask_contact] at paid
  have t₀ : 0≤t := (IterationFour.Currency.g_pos R.makes N p (m+1) hm).le
  have e₀ : 0≤e := pow_nonneg (mul_nonneg (Real.sqrt_nonneg _) t₀) _
  have e₁ : e≤1 := pow_le_one₀ (mul_nonneg (Real.sqrt_nonneg _) t₀) (tiny N p hm)
  have hk : 0≤K := mul_nonneg (by positivity) (tsum_nonneg fun i => (polyExp_pos i).le)
  have ce : c*(K*t)≤v := by rw [mul_comm]; exact (le_div_iff₀ hc).mp (shell N p hm)
  have size : ((inspected S).card:ℝ) ≤ (S.card:ℝ)*17^4 := by exact_mod_cast mask_size S
  have exp_le : Real.exp (2*e)≤Real.exp 2 := Real.exp_le_exp.mpr (by linarith)
  refine ⟨paid.1,paid.2.1,paid.2.2.trans ?_⟩
  calc ((inspected S).card:ℝ)*(2*Real.exp (2*e)*M*e*K) ≤
        (S.card*17^4)*(2*Real.exp 2*M*e*K) := by gcongr
       _ = (c*(K*t))*S.card*M*t^(q+1) := by
         dsimp [e,c]
         rw [mul_pow,show t^(q+2)=t^(q+1)*t from pow_succ _ _]
         ring
       _ ≤ _ := by gcongr

end YM.Integration.OriginalMarkedRowRate
