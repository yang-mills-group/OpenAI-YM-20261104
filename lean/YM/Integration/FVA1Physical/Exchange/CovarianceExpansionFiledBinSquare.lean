import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionTailBins

/-! The square price of the observed bin means comes from the actual fine
field on the very same regulator. This form permits a path-dependent
spectator inside the measured field and makes no statistical independence
claim for the dated deposit. -/
set_option autoImplicit false
set_option maxHeartbeats 1300000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Set Finset MeasureTheory
open scoped Classical BigOperators
variable {Ω:Type*}[MeasurableSpace Ω](μ:Measure Ω)[IsFiniteMeasure μ]
variable {ι:Type*}[Fintype ι](z:Ω→ι)

private theorem cell_square (B:Set Ω)(meas:MeasurableSet B)(u:Ω→ℂ)(square:MemLp u 2 μ):
    μ.real B*‖(∫x in B,u x ∂μ)/(μ.real B:ℂ)‖^2 ≤ ∫x in B,‖u x‖^2 ∂μ:=by
  let p:=μ.real B
  by_cases zero:p=0
  · change p*_≤_
    rw [zero,zero_mul]
    exact integral_nonneg fun x=>sq_nonneg _
  have pos:0<p:=lt_of_le_of_ne measureReal_nonneg (Ne.symm zero)
  have one:=square.indicator meas
  obtain ⟨_,read⟩:=support_rms μ B meas (B.indicator u) one (fun x hx=>Set.indicator_of_notMem hx u)
  have sqE:(fun x=>‖B.indicator u x‖^2)=B.indicator (fun x=>‖u x‖^2):=by
    funext x;by_cases hit:x∈B <;> simp [hit]
  rw [integral_indicator meas,sqE,integral_indicator meas] at read
  let m:=∫x in B,u x ∂μ
  let K:=∫x in B,‖u x‖^2 ∂μ
  have Kp:0≤K:=integral_nonneg fun x=>sq_nonneg _
  change ‖m‖≤Real.sqrt p*Real.sqrt K at read
  have bill:=pow_le_pow_left₀ (norm_nonneg _) read 2
  rw [mul_pow,Real.sq_sqrt pos.le,Real.sq_sqrt Kp] at bill
  change p*‖m/(p:ℂ)‖^2≤K
  rw [norm_div,Complex.norm_real,Real.norm_of_nonneg pos.le,div_pow,←mul_div_assoc]
  apply (div_le_iff₀ (pow_pos pos 2)).mpr
  nlinarith only [mul_le_mul_of_nonneg_right bill pos.le]

theorem original_bin_square (meas:∀i,MeasurableSet {x|z x=i})(u:Ω→ℂ)(square:MemLp u 2 μ):
    (∑i:ι,μ.real {x|z x=i}*‖(∫x in {x|z x=i},u x ∂μ)/(μ.real {x|z x=i}:ℂ)‖^2)≤
    ∫x,‖u x‖^2 ∂μ:=by
  let f:=fun i:ι=>({x|z x=i}:Set Ω).indicator (fun x=>‖u x‖^2)
  have whole (x:Ω):(∑i:ι,f i x)=‖u x‖^2:=by
    rw [Finset.sum_eq_single (z x)]
    · exact Set.indicator_of_mem (show x∈{y|z y=z x} from rfl) _
    · intro i _ other
      exact Set.indicator_of_notMem (show x∉{y|z y=i} from fun h=>other (Eq.symm h)) (fun y=>‖u y‖^2)
    · simp
  have all:Integrable (fun x=>‖u x‖^2) μ:=(memLp_two_iff_integrable_sq_norm square.1).1 square
  have tot:(∑i:ι,∫x in {x|z x=i},‖u x‖^2 ∂μ)=∫x,‖u x‖^2 ∂μ:=by
    calc _=∑i:ι,∫x,f i x ∂μ:=Finset.sum_congr rfl (fun i _=>(integral_indicator (meas i)).symm)
         _=∫x,∑i:ι,f i x ∂μ:=(integral_finsetSum _ (fun i _=>all.indicator (meas i))).symm
         _=_:=integral_congr_ae (.of_forall whole)
  exact (Finset.sum_le_sum (fun i _=>cell_square μ _ (meas i) u square)).trans_eq tot

theorem measured_bin_transport (meas:∀i,MeasurableSet {x|z x=i})(u:Ω→ℂ)(square:MemLp u 2 μ)
    (r:ι→ℝ)(b:ι→ℂ)(M ε δ:ℝ)(mp:0<M)
    (scalar:(∑i:ι,|μ.real {x|z x=i}-r i|)≤ε)
    (marked:(∑i:ι,‖(∫x in {x|z x=i},u x ∂μ)-b i‖)≤δ):
    (∑i:ι,μ.real {x|z x=i}*‖(∫x in {x|z x=i},u x ∂μ)/(μ.real {x|z x=i}:ℂ)-
        clippedBin (μ.real {x|z x=i}) (r i) M (b i)‖)≤(2*δ+2*M*ε)+(3/M)*∫x,‖u x‖^2 ∂μ:=
  normalized_bin_square_transport (fun i=>μ.real {x|z x=i}) r
    (fun i=>∫x in {x|z x=i},u x ∂μ) b (fun _=>measureReal_nonneg) M ε δ _ mp
    scalar marked (original_bin_square μ z meas u square)

end YM.Integration.FVA1Physical.Exchange.RoseCut
