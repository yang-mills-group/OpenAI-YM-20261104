import YM.Integration.WilsonPhysicalStationMixedRankCharge
import YM.Integration.WilsonPhysicalStationBasisWindow
/-! Restore a signed mixed row on the selected lower subtraction on either real pair of dates. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedChartCharge
open Function Filter Finset Lattice RG Wilson Source Labels
open Next.Rank Next.Rank.East Next.Rank.Price MergeProof.East
open Cells Extraction Table Climb Trace Trace.Pilot Next.UVStress
open PhysicalNext.Repeat.Legato Trace.Physical.GermGraph
open WilsonPhysicalStationRawReading (err)
open WilsonPhysicalStationRestoredEntry (signal)
open WilsonPhysicalStationMeasuredCash (aperture)
open WilsonPhysicalStationRegisteredDiagonal (ratio)
open WilsonPhysicalStationWeightedAxis (purse)
open WilsonPhysicalStationThermalPair (raw)
open WilsonPhysicalStationThermalStart (entered)
open WilsonPhysicalStationThermalCoordinates (filed)
open WilsonPhysicalStationBasisRoof (rent)
open scoped Classical BigOperators Topology

variable {G:Gauge}(R:Run G){f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}
    {D D' h e N p:ℕ}(A:Vane R.family D)(B:Vane R.family D')
    (da:h<D+1)(db:h<D'+1)(ca:A.checked f H D)(cb:B.checked f H D')
local notation "d₀"=>(⟨h,da⟩:Fin (D+1))
local notation "d₁"=>(⟨h,db⟩:Fin (D'+1))
local notation "F₀"=>R.family.labels.level h
local notation "A₀"=>R.family.path.levels
local notation "M₀"=>Station.mag (A₀) A.b A.k
local notation "M₁"=>Station.mag (A₀) B.b B.k
local notation "T₀"=>(A₀).clock.monitor A.k
local notation "P₀"=>(shrink R.family A.k N p)⁻¹
local notation "P₁"=>(shrink R.family B.k N p)⁻¹

def wage (q Q:ℕ)(J Γ:ℝ)(m h:ℕ):ℝ:=
  2*2^Q*12^q*(J*4^Q*(2^q+(Fintype.card (R.family.labels.level h).Index:ℝ)*rent R m h)+rent R m h*Γ)

theorem original (dates:B.k=A.k ∨ B.k=A.k+1)(top:B.k<N)(warm:WilsonPhysicalStationBasisClock.Live R A.k)
    (window:aperture R A.k B.k h (M₀) (M₁)≤1)(a:(F₀).Index)(w:R.family.label h)
    (stamped:if B.k=A.k then WilsonPhysicalStationCoincidentLower.Receipt R A B h e da db (p:=p) ca cb top a w
      else WilsonPhysicalStationSelectedLower.Receipt R A B h e da db (p:=p) ca cb top a w)
    (hear:R.family.label h→ₗ[ℂ]ℂ)(Γ:(F₀).Index→ℂ)(Q:ℕ)(J:ℝ)(jp:0≤J)
    (low:∀i,((F₀).grades i).2≤Q→
      ‖hear (raw R A (d₀) (p:=p) ca (show A.k<N by omega) (Pi.single i 1))-Γ i‖*(T₀)^Q≤J*(T₀)^((F₀).grades i).2)
    (high:∀i,Q<((F₀).grades i).2→
      ‖hear (raw R A (d₀) (p:=p) ca (show A.k<N by omega) (Pi.single i 1))-Γ i‖≤J)
    (foreign:∀i,((F₀).grades i).2≠Q→Γ i=0):
    let q:=((F₀).grades a).2
    let Z:=entered R B (d₁) (p:=p) cb top (Pi.single a 1)-(R.family.factory h N p).terminal w
    let χ:ℂ:=signal R N p A.k B.k h q (M₀) (M₁)
    ‖hear Z-χ*Γ a‖*(T₀)^Q≤wage R q Q J (∑i,‖Γ i‖) A.k h*(T₀)^q:=by
  intro q Z χ
  let E:=aperture R A.k B.k h (M₀) (M₁)
  let μ:=purse R N p A.k B.k h q (M₀) (M₁)
  let τ:=fun i=>( (F₀).grades i).2
  let ledger:=filed R A (d₀) N p Z
  let ρ:=rent R A.k h
  have live:A.k<N:=by omega
  have Epos:0≤E:=pow_nonneg (div_nonneg (mul_nonneg (R.family.S.a_pos _).le (Station.mag_pos ..).le)
    (mul_nonneg (R.family.S.a_pos _).le (Station.mag_pos ..).le)) _
  have up:=inv_pos.mpr (shrink_pos R.family R.makes top.le p)
  have pp:0≤μ:=mul_nonneg Epos (pow_nonneg up.le _)
  have rnon:0≤ρ:=add_nonneg (abs_nonneg _) (abs_nonneg _)
  have eq:μ=E*(P₁)^q:=rfl
  obtain ⟨pos,width,height⟩:=WilsonPhysicalStationDetectorCurrency.original R p live.le
  have col:∀i,(1-err R B.k)*‖ledger i-χ*(Pi.single a (1:ℂ):(F₀).Index→ℂ) i‖*(P₀)^(τ i)≤ρ*μ:=by
    intro i
    rcases dates with same|next
    · rw [if_pos same] at stamped
      have ref:=WilsonPhysicalStationBasisImpact.self R (N:=N) (p:=p) (h:=h) (q:=q) same live.le (M₀) (M₁)
      change (1-err R B.k)*‖ledger i-(signal R N p A.k B.k h q (M₀) (M₁):ℂ)*(Pi.single a (1:ℂ):(F₀).Index→ℂ) i‖*(P₀)^(τ i)≤ρ*μ
      rw [ref]
      exact (stamped.coefficients i).trans (mul_le_mul_of_nonneg_right (warm.coincident h) pp)
    · rw [if_neg (show B.k≠A.k by omega)] at stamped
      exact (stamped.coefficients i).trans (mul_le_mul_of_nonneg_right (show _ ≤ _ by rw [next];exact warm.adjacent h) pp)
  have main:(1-err R B.k)*‖χ‖*(P₀)^q≤(2:ℝ)^q*μ:=by
    rcases dates with same|next
    · dsimp only [χ]
      rw [WilsonPhysicalStationBasisImpact.self R (p:=p) same live.le (M₀) (M₁)]
      exact (WilsonPhysicalStationCoincidentAxis.principal R A B h (p:=p) same top q).trans
        (mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num)) pp)
    · have tp:0≤ratio R A.k:=div_nonneg ((A₀).budget _).threshold_pos.le ((A₀).budget _).threshold_pos.le
      exact (WilsonPhysicalStationWeightedAxis.principal R A B h da (p:=p) next top q).trans
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ tp warm.thermal q) pp)
  have physics:=WilsonPhysicalStationMixedRankCharge.original R A (d₀) (p:=p) ca live hear Z Γ Q J jp warm.large low high
  have paid:=WilsonPhysicalStationResidualWallet.original τ a ledger Γ χ (hear Z) Q
    (WilsonPhysicalStationFiledGate.refund R B) pos.le (zero_le_one' ℝ)
    (mul_nonneg jp (by positivity : 0≤(4:ℝ)^Q)) main col physics foreign
  have gate:((A₀).params B.k).columns*err R B.k≤1/2:=by
    rcases dates with same|next
    · rw [same]; exact warm.old
    · rw [next]; exact warm.fine
  have half:1/2≤1-err R B.k:=by
    have z:0≤err R B.k:=(Real.exp_pos _).le
    have one:=((A₀).params B.k).columns_ge
    linarith only [gate,le_mul_of_one_le_left z one]
  have advance:P₁≤6*P₀:=by
    rcases dates with same|next
    · rw [same]; linarith only [pos]
    · rw [next,←one_div,←div_eq_mul_inv]
      exact (div_le_div_iff₀ (shrink_pos R.family R.makes (show A.k+1≤N by omega) p)
        (shrink_pos R.family R.makes live.le p)).2 (by simpa using warm.slope N p live)
  let inn:=J*4^Q*((2:ℝ)^q+(Fintype.card (F₀).Index:ℝ)*ρ)+ρ*∑i,‖Γ i‖
  have ip:0 ≤ inn:=by dsimp [inn]; positivity
  have fee:(1-err R B.k)*‖hear Z-χ*Γ a‖*(P₀)^Q≤E*(P₁)^q*inn:=by
    simpa only [←eq,mul_one,inn] using paid
  have hot:0≤T₀:=by linarith only [warm.large]
  have scaled:=WilsonPhysicalStationMixedRankCharge.scale q Q Epos (norm_nonneg _) ip pos.le up.le hot width height advance half fee
  apply scaled.trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hot _)
  change 2*2^Q*12^q*E*inn≤2*2^Q*12^q*inn
  exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (by positivity) window) ip

end YM.Integration.WilsonPhysicalStationMixedChartCharge
end
