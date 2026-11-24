import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionShortNetworkBill
import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionSignedCollarAlgebra

/-! Use the actual-minus-independent price on the crowded event. This avoids
assuming a uniform RMS for the retained hard row. After this subtraction the
only old hard term on the dated physical posterior has a truly large actor
meeting the nominated ball; exterior tests may be unbounded and correlated. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Set Finset Filter MeasureTheory Lattice RG Wilson Marker Multi Extra.Trajectories Push.AbsoluteSums.Animals
open scoped Classical BigOperators ENNReal
variable {G:Gauge}{n:Side}{V:Type}[Fintype V][DecidableEq V]{C:Census V}

private theorem event_stock {T:Type*}[MeasurableSpace T](μ:Measure T)[IsFiniteMeasure μ]
    (E:Set T)(em:MeasurableSet E)(A Y:T→ℂ)(am:Measurable A)(y2:MemLp Y 2 μ)
    (τ M:ℝ)(mp:0≤M)(stock:∀t,‖(τ:ℂ)*A t‖≤M):
    let Z:=fun t=>E.indicator (fun u=>(τ:ℂ)*A u) t * Y t
    Integrable Z μ ∧ ‖∫t,Z t ∂μ‖≤Real.sqrt (∫t,‖Y t‖^2 ∂μ)*(M*Real.sqrt (μ.real E)):=by
  intro Z
  have mz:AEStronglyMeasurable Z μ:=
    ((measurable_const.mul am).indicator em).aestronglyMeasurable.mul y2.1
  have upper (t:T):‖Z t‖^2≤M^2*‖Y t‖^2:=by
    by_cases hit:t∈E
    · simpa only [Z,Set.indicator_of_mem hit,norm_mul,mul_pow] using
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (stock t) 2) (sq_nonneg ‖Y t‖)
    simp only [Z,Set.indicator_of_notMem hit,zero_mul,norm_zero,ne_eq,OfNat.ofNat_ne_zero,
      not_false_eq_true,zero_pow]
    positivity
  have sqy:Integrable (fun t=>‖Y t‖^2) μ:=(memLp_two_iff_integrable_sq_norm y2.1).1 y2
  have maj:=sqy.const_mul (M^2)
  have sqz:Integrable (fun t=>‖Z t‖^2) μ:=maj.mono' (mz.norm.pow 2)
    (.of_forall fun t=>by rw [Real.norm_of_nonneg (sq_nonneg _)];exact upper t)
  have z2:MemLp Z 2 μ:=(memLp_two_iff_integrable_sq_norm mz).2 sqz
  have bound:(∫t,‖Z t‖^2 ∂μ)≤M^2*(∫t,‖Y t‖^2 ∂μ):=
    (integral_mono sqz maj upper).trans_eq (integral_const_mul ..)
  have rms:=Real.sqrt_le_sqrt bound
  rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq mp] at rms
  obtain ⟨zi,small⟩:=support_rms μ E em Z z2 (fun t ht=>by simp only [Z,Set.indicator_of_notMem ht,zero_mul])
  refine ⟨zi,small.trans ?_⟩
  exact (mul_le_mul_of_nonneg_left rms (Real.sqrt_nonneg _)).trans_eq (by ring)

abbrev loggedRaw (B:Activities G n)(p:BudgetPoint)(K:Config G n→ℕ→Poly C)
    (s:C.Mode)(U:Config G n):ℂ:=
  (connected (((B.gas p U:ℂ)⁻¹) • ∑'S,RoseRoster.roster B p U (K U) S)).part s

/-- The only residual hard hearing is large-actor-supported. The initial
comparison and gross stock apply to the same actual-minus-filed table A and
wallet. No bound for the full old connected ground cofactor is assumed. -/
theorem observed_long_entry {T:Type*}[MeasurableSpace T](law:Measure T)[IsFiniteMeasure law]
    (μ:Measure (Config G n))[IsFiniteMeasure μ](π:T→Config G n)(πm:Measurable π)
    (original:Measure.map π law=μ)
    (B:Activities G n)(p:BudgetPoint)(K:Config G n→ℕ→Poly C)
    (o:V→Site n)(carry:∀U (i:ℕ)(r:C.Mode),(K U i).part r≠0 → ∀v∈r.val,o v∈(B.forced i).support)
    (licensed:∀U i,K U i≠0 → (B.forced i).eligible p.threshold U)
    (K₀:∀U i,(K U i).part C.quiet=(B.K i U:ℂ))(live:∀t,B.gas p (π t)≠0)
    (w:V→ℝ)(wp:∀v,0<w v)(stock:∀U,Summable fun i=>Poly.price w (K U i))
    (s:C.Mode)(a b:V)(usedA:a∈s.val)(usedB:b∈s.val)(m D:ℕ)
    (separated:2*m*width p D<separation (o a) (o b))(rate:ℝ)
    (rare:∀Z:Support n, μ.real {U|Z⊆flags p.threshold U}≤rate^Z.card)
    (A:T→ℂ)(am:Measurable A)(τ M ε:ℝ)(tp:0≤τ)(mp:0≤M)(ep:0≤ε)
    (global:∀t,‖(τ:ℂ)*A t‖≤M)
    (regular:∀Z:T→ℂ,MemLp Z 2 law →
      Integrable (fun t=>Z t*(A t-loggedRaw B p K s (π t))) law ∧
      τ*‖∫t,Z t*(A t-loggedRaw B p K s (π t)) ∂law‖≤Real.sqrt (∫t,‖Z t‖^2 ∂law)*ε)
    (Y:T→ℂ)(y2:MemLp Y 2 law):
    let F:=neighbors (2*m*width p D) (o a)
    let E:=π ⁻¹' crowd p.threshold F m
    let H:=fun t=>if LongAt B p (K (π t)) (o a) (2*m) D then loggedRaw B p K s (π t) else 0
    let value:=fun t=>(τ:ℂ)*Y t*(A t-Eᶜ.indicator H t)
    Integrable value law ∧ ‖∫t,value t ∂law‖≤
      Real.sqrt (∫t,‖Y t‖^2 ∂law)*(ε+M*Real.sqrt ((F.card.choose m:ℕ)*rate^m)):=by
  intro F E H value
  have seen:=crowd_measurable (G:=G) p.threshold F m
  have em:MeasurableSet E:=seen.preimage πm
  have hits:Eᶜ.indicator H=Eᶜ.indicator (fun t=>loggedRaw B p K s (π t)):=by
    funext t
    by_cases out:t∈Eᶜ
    · simp only [Set.indicator_of_mem out,H]
      split
      · rfl
      next clear =>
        symm
        by_contra nz
        have count:=(original_limited_window B p (π t) (K (π t)) o (carry _) (licensed _) (K₀ _) (live t)
          w wp (stock _) s nz a b usedA usedB (2*m) D separated).resolve_left clear
        have room:m≤(flags p.threshold (π t)∩F).card:=by dsimp only [F];omega
        obtain ⟨Z,taken,sz⟩:=Finset.exists_subset_card_eq room
        exact out (Set.mem_iUnion.mpr ⟨Z,Set.mem_iUnion.mpr
          ⟨mem_powersetCard.mpr ⟨taken.trans inter_subset_right,sz⟩,taken.trans inter_subset_left⟩⟩)
    simp only [Set.indicator_of_notMem out]
  have marginal:law.real E=μ.real (crowd p.threshold F m):=by
    rw [←original]
    exact (congrArg ENNReal.toReal (Measure.map_apply πm seen)).symm
  obtain ⟨ii,fee⟩:=event_stock law E em A Y am y2 τ M mp global
  obtain ⟨fi,bill⟩:=RoseDatedReceived.paid_signed_complement law E em A
    (fun t=>loggedRaw B p K s (π t)) Y y2 tp ep regular ⟨ii,fee⟩
  dsimp only [value]
  rw [hits]
  rw [marginal] at bill
  exact ⟨fi,bill.trans (mul_le_mul_of_nonneg_left
    (add_le_add_right (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (crowd_bound μ _ _ rare F m)) mp) ε)
    (Real.sqrt_nonneg _))⟩

end YM.Integration.FVA1Physical.Exchange.RoseCut
