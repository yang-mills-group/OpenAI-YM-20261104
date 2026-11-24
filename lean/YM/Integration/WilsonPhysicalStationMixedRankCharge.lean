import YM.Integration.WilsonPhysicalStationMeasuredCash
/-! Complete two-sided thermal factor on the measured K-column against an arbitrary linear measurement. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedRankCharge
open Function Filter RG Wilson MergeProof Labels Source Lattice
open Next.Rank Next.Rank.East Next.Rank.Price MergeProof.East
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress
open PhysicalNext.Repeat.Legato Trace.Physical.GermGraph
open WilsonPhysicalStationThermalCoordinates (filed)
open WilsonPhysicalStationThermalPair (raw)
open scoped BigOperators Classical Topology

theorem scale {E x P U T z fee:ℝ}(q Q:ℕ)(ep:0≤E)(xp:0≤x)(fp:0≤fee)
    (pp:0≤P)(up:0≤U)(tp:0≤T)(width:P≤2*T)(height:T≤2*P)(adjacent:U≤6*P)
    (gate:1/2≤1-z)(paid:(1-z)*x*P^Q≤E*U^q*fee):
    x*T^Q≤(2*2^Q*12^q*E*fee)*T^q:=by
  have a:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right gate xp) (pow_nonneg pp Q)
  have b:x*P^Q≤2*(E*U^q*fee):=by linarith only [a,paid]
  have c:U≤12*T:=by linarith only [adjacent,width]
  have d:=pow_le_pow_left₀ up c q
  have e:=pow_le_pow_left₀ tp height Q
  rw [mul_pow] at d e
  calc
    _ ≤ x*(2^Q*P^Q):=mul_le_mul_of_nonneg_left e xp
    _ = 2^Q*(x*P^Q):=by ring
    _ ≤ 2^Q*(2*(E*(12^q*T^q)*fee)):=mul_le_mul_of_nonneg_left
      (b.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left d ep) fp) (by norm_num))) (by positivity)
    _ = _:=by ring

variable {G:Gauge}(R:Run G){f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}
    {D:ℕ}(A:Vane R.family D)(d:Fin (D+1)){N p:ℕ}(ca:A.checked f H D)(top:A.k<N)
local notation "F₀" => R.family.labels.level d
local notation "T₀" => R.family.path.levels.clock.monitor A.k
local notation "P₀" => (shrink R.family A.k N p)⁻¹

theorem filed_read (hear:R.family.label d→ₗ[ℂ]ℂ)(y:R.family.label d):
    hear y=∑ a,filed R A d N p y a*hear (raw R A d (p:=p) ca top (Pi.single a 1)):=by
  calc
    _=hear (∑a,filed R A d N p y a • raw R A d (p:=p) ca top (Pi.single a 1)):=
      congrArg hear (WilsonPhysicalStationThermalCoordinates.expands R A d (p:=p) ca top y)
    _=_:=by simp only [map_sum,map_smul,smul_eq_mul]

theorem original (hear:R.family.label d→ₗ[ℂ]ℂ)(y:R.family.label d)(Γ:(F₀).Index→ℂ)
    (Q:ℕ)(J:ℝ)(jp:0≤J)(hot:4≤T₀)
    (low:∀i,((F₀).grades i).2≤Q→
      ‖hear (raw R A d (p:=p) ca top (Pi.single i 1))-Γ i‖*(T₀)^Q≤J*(T₀)^((F₀).grades i).2)
    (high:∀i,Q<((F₀).grades i).2→‖hear (raw R A d (p:=p) ca top (Pi.single i 1))-Γ i‖≤J):
    ‖hear y-∑i,filed R A d N p y i*Γ i‖*(P₀)^Q≤
      (J*4^Q)*(1:ℝ)*∑i,‖filed R A d N p y i‖*(P₀)^((F₀).grades i).2:=by
  obtain ⟨pp,lo,hi⟩:=WilsonPhysicalStationDetectorCurrency.original R p top.le
  have room:1≤P₀:=by linarith only [hot,hi]
  have grant:0≤J*4^Q:=by positivity
  have envelope:= WilsonPhysicalStationWickFees.price (fun i=>( (F₀).grades i).2)
    (filed R A d N p y) (fun i=>hear (raw R A d (p:=p) ca top (Pi.single i 1))-Γ i)
    Q (P₀) 1 (J*4^Q) room (by norm_num) grant (by simpa only [mul_one] using room)
    (fun i rank=>WilsonPhysicalStationDetectorCurrency.low (T:=(T₀)) (P:=(P₀)) rank (by linarith only [hot]) pp.le jp
      (zero_le_one' ℝ) (norm_nonneg _) lo hi (by simpa only [mul_one] using low i rank))
    (fun i rank=>(high i rank).trans (le_mul_of_one_le_right jp (one_le_pow₀ (by norm_num))))
  calc
    _=‖∑i,filed R A d N p y i*(hear (raw R A d (p:=p) ca top (Pi.single i 1))-Γ i)‖*(P₀)^Q:=by
      rw [filed_read R A d (p:=p) ca top hear y]
      simp only [mul_sub,Finset.sum_sub_distrib]
    _≤_:=envelope.trans_eq (by ring)

end YM.Integration.WilsonPhysicalStationMixedRankCharge
end
