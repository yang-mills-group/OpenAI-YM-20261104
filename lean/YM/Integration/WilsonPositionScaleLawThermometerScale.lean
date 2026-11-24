import YM.Integration.WilsonPositionScaleLawThermometerPay

/-! Physical bounded-ratio running from ordinary near-home prices. The group
coefficient is real at the true measured coupling at every finite truncation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawThermometerScale
open Function Filter Set Finset PowerSeries Asymptotics Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Rose PhysicalNext.Repeat.Legato
open MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionScaleLawWindow (RangeSpec Ratio sweep)
open WilsonPositionScaleLawKinetic (kinetic)
open WilsonPositionScaleLawThermometerPay (Fits target)
open WilsonPositionScaleLawIndependent (ψ)
open scoped Topology BigOperators Classical Polynomial
variable [W:RangeSpec]{G:Gauge}(Z:WilsonPrescription G){hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
    {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)

include H in
theorem real (q:ℕ)(z:ℝ×Ratio):starRingEnd ℂ (target Z M ν F J q z)=target Z M ν F J q z:=by
  let s:=WilsonPositionScaleLawCompactIndependent.time z.2
  have h(k:ℕ):starRingEnd ℂ (coeff k (ψ Z M ν s))=coeff k (ψ Z M ν s):=by
    have f:=congrArg (coeff k) ((H.details.normative ν).first.led s).real
    simpa only [PowerSeries.coeff_map] using f
  rw [target,WilsonPositionScaleLawThermometerSmeared.paper,map_sum]
  apply Finset.sum_congr rfl;intro k _
  rw [map_mul,map_pow,h];simp [s]

def Earned(q:ℕ):Prop:=∀δ:ℝ,0<δ→∀ᶠz:ℝ×Ratio in sweep,Fits Z M ν F J q z (δ*|kinetic Z F J z.1|^q)

variable (lead:Leading F J){Y:(Bel R.family.book).Hierarchy}(paid:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)
include H lead paid in
theorem qinterg (q:ℕ)(raw:WilsonPositionScaleLawCompactBranch.Raw J 6)(fees:Earned Z M ν F J q):
    (fun z:ℝ×Ratio=>kinetic Z F J (z.2.val*z.1)-(target Z M ν F J q z).re)=o[sweep] (fun z=>kinetic Z F J z.1^q):=by
  have tiny:Tendsto (fun z:ℝ×Ratio=>kinetic Z F J z.1) sweep (𝓝 0):=
    (WilsonPositionPrescribedZero.measured F J Z.store lead paid hG Z.criterion).comp tendsto_fst
  obtain ⟨L,T,hL,hT,cost⟩:=WilsonPositionScaleLawThermometerPay.original Z M H ν F J lead paid q raw
  apply isLittleO_iff.mpr;intro ε hε
  have pos:0<L+T+1:=by linarith
  let δ:=min 1 (ε/(L+T+1))
  have hd:0<δ:=lt_min zero_lt_one (div_pos hε pos)
  filter_upwards [cost,fees δ hd,Metric.tendsto_nhds.mp tiny δ hd] with z bound income gz
  let g:=kinetic Z F J z.1
  have hg:|g|≤δ:=by simpa only [dist_zero_right,Real.norm_eq_abs] using gz.le
  have hu:δ≤1:=min_le_left ..
  have fee1:δ*|g|^q≤1:=(mul_le_mul hu (pow_le_one₀ (abs_nonneg _) (hg.trans hu)) (by positivity) zero_le_one).trans_eq (one_mul _)
  have money:=bound (δ*|g|^q) (mul_nonneg hd.le (by positivity)) fee1 income
  have scale:L*δ+T*|g|≤ε:=calc
    _≤(L+T+1)*δ:=by nlinarith [mul_le_mul_of_nonneg_left hg hT]
    _≤(L+T+1)*(ε/(L+T+1)):=mul_le_mul_of_nonneg_left (min_le_right ..) pos.le
    _=ε:=mul_div_cancel₀ _ pos.ne'
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_pow]
  calc _≤L*(δ*|g|^q)+T*|g|^(q+1):=money
       _=(L*δ+T*|g|)*|g|^q:=by ring
       _≤ε*|g|^q:=mul_le_mul_of_nonneg_right scale (by positivity)

end YM.Integration.WilsonPositionScaleLawThermometerScale
end
