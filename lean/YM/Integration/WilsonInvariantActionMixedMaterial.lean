import YM.Integration.WilsonRegisteredRegularQuota
import YM.Integration.WilsonLocalCompactMeasuredMoments
import YM.Push.LOCAL_SPLITTING.Direct

/-! The two actual sources in a mixed incoming row of the separated action
response. The earlier regular cohort can be any subset of its filed rows. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionMixedMaterial
open Function Finset Set MeasureTheory Lattice RG Wilson Source Labels Push.Local MergeProof
open WilsonInheritedRegisteredField WilsonLocalCompactProbability
open scoped Classical BigOperators
variable {G:Gauge} {C:Family G} (h:C.Makes) {k N per:ℕ}

def primary (live:k≤N) (v:C.label 4) (x:Site (C.side k per)) (U:Config G (C.side k per)):ℂ:=
  let A:=C.path.rep N per k;let Z:=packet h live v x;let S:=C.localSection 4;let L:=C.labels.level 4
  alto C.path k 4*masked A.p.threshold (S.footprint x) (S.places (L.scaled A.p.threshold⁻¹ (L.core Z.x)) x) U

def earlier (live:k≤N) (v:C.label 4) (x:Site (C.side k per)) (I:Set ℕ) (U:Config G (C.side k per)):ℂ:=
  let A:=C.path.rep N per k;let Z:=packet h live v x
  alto C.path k 4*(∑' i,if i∈I then Z.maskedTerm A i U else 0)

def budget (v:C.label 4) (k N per:ℕ):ℝ:=
  (C.path.levels.params k).columns*((C.S.a k^4)⁻¹*Next.UVStress.quota C 4 k N per v)

def controlled {n:Side} (f:Config G n→ℂ) (c:ℝ):Prop:=
  Envelope f ∧ GaugeInvariant f ∧ ∀U,‖f U‖≤c

private theorem scaled {f:Config G (C.side k per)→ℂ} {v:C.label 4} (live:k≤N)
    (x:Site (C.side k per)) (hm:Measurable f) (hg:GaugeInvariant f)
    (hb:∀U,‖f U‖≤(C.path.levels.params k).columns*
      (C.labels.level 4).coeffSize ((C.labels.level 4).core (packet h live v x).x)):
    controlled (fun U=>alto C.path k 4*f U) (budget v k N per):=by
  let L:=C.labels.level 4;let Z:=packet h live v x;let K:=(C.path.levels.params k).columns
  have normal:L.coeffSize Z.x=Next.UVStress.quota C 4 k N per v:=
    congrArg L.coeffSize (WilsonTranslatedFactory.coordinate h live x ((C.factory 4 N per).terminal.symm v))
  have b (U):‖alto C.path k 4*f U‖≤budget v k N per:=by
    rw [norm_mul,alto_norm]
    calc
      _≤(C.S.a k^4)⁻¹*(K*L.coeffSize (L.core Z.x)):=mul_le_mul_of_nonneg_left (hb U) (by positivity)
      _≤(C.S.a k^4)⁻¹*(K*L.coeffSize Z.x):=by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left (Work.G08.size_core L Z.x) (zero_le_one.trans (C.path.levels.params k).columns_ge)
      _=budget v k N per:=by rw [normal];unfold budget;ring
  exact ⟨⟨measurable_const.mul hm,_,b⟩,fun g U=>congrArg (alto C.path k 4*·) (hg g U),b⟩

theorem filed (live:k≤N) (ref:C.ref 4≤k) (v:C.label 4) (x:Site (C.side k per)) (I:Set ℕ):
    controlled (primary h live v x) (budget v k N per) ∧ controlled (earlier h live v x I) (budget v k N per):=by
  let A:=C.path.rep N per k;let Z:=packet h live v x;let S:=C.localSection 4;let L:=C.labels.level 4
  let K:=(C.path.levels.params k).columns;let y:=L.scaled A.p.threshold⁻¹ (L.core Z.x)
  let u:=fun U=>masked A.p.threshold (S.footprint x) (S.places y x) U
  have quoted:=Push.GridApprox.specific_price C h x ref live y
  have certified:=WilsonTranslatedFactory.based h ref live x ((C.factory 4 N per).terminal.symm v)
  have format:Z.Format x C.params A:=certified.1
  refine ⟨scaled h live x (f:=u) (masked_measurable _ _ _ (S.continuous_places y x).measurable)
    (Push.Local.Kernel.mask_gauge _ _ quoted.1.symmetry) ?_,?_⟩
  · intro U
    by_cases clean:Healthy A.p.threshold (S.footprint x) U
    · have bill:=quoted.2.2 U clean [] (Nat.zero_le _) (by simp)
      change ‖S.places y x U‖≤K*L.coeffSize (L.scaled A.p.threshold y) at bill
      change ‖masked _ _ _ U‖≤_
      rw [masked_eq _ _ _ _ clean]
      rwa [show L.scaled A.p.threshold y=L.core Z.x from L.scaled_inv A.p.threshold_pos.ne' _] at bill
    · change ‖masked _ _ _ U‖≤_
      rw [masked_ne _ _ _ _ clean,norm_zero]
      exact mul_nonneg (zero_le_one.trans (C.path.levels.params k).columns_ge) (sum_nonneg fun _ _=>norm_nonneg _)
  let f:=fun i U=>if i∈I then Z.maskedTerm A i U else 0
  have measurable (i):Measurable (f i):=by
    by_cases hit:i∈I
    · simpa only [f,if_pos hit,Coefficient.maskedTerm] using (masked_measurable _ _ _ (format.smooth i).borel)
    · simp only [f,if_neg hit];exact measurable_const
  have invariant (i):GaugeInvariant (f i):=by
    by_cases hit:i∈I
    · simpa only [f,if_pos hit,Coefficient.maskedTerm] using Push.Local.Kernel.mask_gauge A.p.threshold (Z.support i) (format.smooth i).symmetry
    · exact fun g U=>by simp only [f,if_neg hit]
  apply scaled h live x (f:=fun U=>∑' i,f i U) (Measurable.tsum measurable) (fun g U=>tsum_congr fun i=>invariant i g U)
  intro U
  obtain ⟨a,c,_,hc,allFee,_,⟨e,E,S⟩,_⟩:=certified.2
  have point (i):‖f i U‖≤A.p.mass (Z.support i) (e i):=by
    have fee:A.p.supBounds x (Z.support i) (Z.regular i) (e i):=S i
    have lo:e i≤A.p.mass (Z.support i) (e i):=le_mul_of_one_le_left fee.1 (Real.one_le_exp (mul_nonneg A.p.exponent_pos.le (Nat.cast_nonneg _)))
    by_cases hit:i∈I
    · rw [show f i U=Z.maskedTerm A i U from if_pos hit]
      by_cases healthy:Healthy A.p.threshold (Z.support i) U
      · change ‖masked _ _ _ U‖≤_
        rw [masked_eq _ _ _ _ healthy]
        exact (fee.2 U healthy [] (Nat.zero_le _) (by simp)).trans lo
      · change ‖masked _ _ _ U‖≤_
        rw [masked_ne _ _ _ _ healthy,norm_zero]
        exact fee.1.trans lo
    · rw [show f i U=0 from if_neg hit,norm_zero];exact fee.1.trans lo
  have bill:SumBudget (fun i=>‖f i U‖) a:=sumBudget_mono E (fun i=>norm_nonneg _) point le_rfl
  exact ((norm_tsum_le_tsum_norm bill.2.1).trans bill.2.2).trans ((le_add_of_nonneg_right hc).trans allFee)

def signal {n:Side} {f:Config G n→ℂ} {b:ℝ} (c:controlled f b) (η:ℂ→L[ℝ]ℝ): Signal (G:=G) (n:=n):=
  enrolled (f:=fun U=>η (f U)) ⟨η.continuous.measurable.comp c.1.meas,‖η‖*b,fun U=>
    (η.le_opNorm _).trans (mul_le_mul_of_nonneg_left (c.2.2 U) (norm_nonneg _))⟩
    (fun g U=>congrArg η (c.2.1 g U))

theorem value {n:Side} {f:Config G n→ℂ} {b:ℝ} (c:controlled f b) (η:ℂ→L[ℝ]ℝ)
    (U:Config G n):|(signal c η).1 U|≤‖η‖*b:=by
  calc
    _=‖η (f U)‖:=by simp only [signal,enrolled,Real.norm_eq_abs]
    _≤‖η‖*‖f U‖:=η.le_opNorm _
    _≤‖η‖*b:=mul_le_mul_of_nonneg_left (c.2.2 U) (norm_nonneg _)

end YM.Integration.WilsonInvariantActionMixedMaterial
