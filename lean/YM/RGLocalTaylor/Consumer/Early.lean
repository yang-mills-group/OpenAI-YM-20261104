import YM.RGLocalTaylor.Consumer.Leaflet
/-!
# Uniform local Taylor remainder, early vacuum clause

`7 (M+1) ≥ 8 p` is the oversampling threshold: M the Mayer Taylor
order; p the final g exponent. No power loss, post beta-support costs paid in
full to get this printed estimate. Strengthen thresholds only via `Earned`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor.Consumer
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration RG.Shoot Push.SectorMeasure Supply Input Testing Push.PriceCompiler Org
open ConnectedActivityE6.Blaze Blaze.March Captain Silica PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Height Refrain Song
open PhysicalNext.Repeat.Greenbelt Match Roof Roost Geo Time Opera PhysicalNext.Repeat.Legato
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open RG01 RG01.Survive Daisy.Charity.RG12
variable {G : Gauge} {X : Metals G} {D:Rolls X.p}{A:Alloy X D}{R:Roost.Factor A}
    {m N n : ℕ} {u : RG.Rep G (A.B.a.S.side (m+1) n)} (H:Guide A.B R.shape N m n u)
    (O:Return.Wood A.B m n)

set_option quotPrecheck false
variable (hH: Opera.Price A.B R.shape N m n u H) (hm:m<N) (hl : RG.Shoot.Lives A.B.bake N (m+1) n u) (hb: u.beta∈ RG.Shoot.band A.B.a (m+1))

namespace Issued01
variable {H M O} {s t : ℝ}
lemma weaken (h : Issued01 H O M s) (ht:s ≤ t): Issued01 H O M t :=
  {h with priced := ⟨VerifiedReset.Time.E_rises h.priced.1 ht,h.priced.2⟩}
end Issued01

variable (R)
theorem calendar (hG:G.Simple) (ht:Mallow.RG12.Earned (Mayer.decal G) R.shape A.delay) (M p j : ℕ) (hp:8*p ≤ 7*(M+1)) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (N m n:ℕ), m<N → M ≤ A.B.a.clock.J (m+1) → ∀ u:RG.Rep G (A.B.a.S.side (m+1) n), RG.Shoot.Lives A.B.bake N (m+1) n u → u.beta ∈ RG.Shoot.band A.B.a (m+1) →
      ∃ H:Guide A.B R.shape N m n u, Opera.Price A.B R.shape N m n u H ∧
        A.B.a.clock.hatBeta (m+1)^j * ((A.B.a.clock.forcedAllowance m) / Real.sqrt (A.B.a.clock.forcedAllowance m)) ≤ c * (Real.sqrt u.beta)⁻¹^p ∧
        ∀ (O : Return.Wood A.B m n) (H: Guide A.B R.shape N m n u), Opera.Price A.B R.shape N m n u H → Issued01 H O M (c*(Real.sqrt u.beta)⁻¹^p):= by
  obtain ⟨c,hc,H⟩:= Vacuum.markCurrency R hG (M+1)
  obtain ⟨d,hd,K⟩:= Vacuum.Flat.currency A.B.a hG p j
  let t:=Real.sqrt 2; have hf:0<t:=by unfold t; positivity
  let p':= t^(M+1)+c; have hc':0≤ p':=by unfold p'; positivity
  let C:= p'*t^(M+1-p)+t^p
  have hC:0≤C:= by unfold C; positivity
  refine ⟨C+d,add_nonneg hC hd,fun N m n hi hn u he hv=>?_⟩
  obtain ⟨A',hA⟩:= Opera.feature A.B R.shape hi R.pledging.conducts.full R.pledging.conducts.income he hv
  let w:= A.B.a.clock.forcedAllowance m; have hw : 0<w:=Real.exp_pos _
  let g:= (Real.sqrt u.beta)⁻¹; have hK := A.B.a.fits.delayed (m+1)
  have hu:0<u.beta:= lt_of_lt_of_le (half_pos (zero_lt_one.trans hK)) hv.1; have hg:0<g:=by unfold g; positivity
  refine ⟨A',hA,?_ ,fun O Z hZ=>?_⟩
  · rw [show w/Real.sqrt w=Real.sqrt w from (div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr hw))).2 (Real.mul_self_sqrt hw.le).symm] -- zeta direction
    exact (K m _ hu (Or.inl hv.2)).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC) (pow_nonneg hg.le _))
  have hD:= delivered Z O hZ hi he hv M (gate Z ht hn hi) (H m N hi u.beta hv)
  let f:=A.B.a.clock.hatBeta (m+1); let L:= D.L (A.B.a.clock.J (m+1))
  have hδ:(((f^Mayer.height)^ (M+1))⁻¹) ≤ t^p*g^p:= Mayer.pay_extra hK.le hu hv.2 hp
  have hx : f=Pressure.betaF G (A.B.a.clock.hatBeta m) L:= PriceCompiler.beta_eq A.B.valid m
  apply hD.weaken
  apply le_trans (b:= C*g^p) _ (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hd) (pow_nonneg hg.le _))
  change p'*g^(M+1)+(Mayer.arcRadius .. ^_)⁻¹ ≤ _
  unfold C; rw [add_mul (p'*t^(M+1-p))]
  unfold Mayer.arcRadius; rw [← hx]; exact add_le_add ((mul_le_mul_of_nonneg_left (Mayer.advance hK hv.1 (by omega : p≤M+1)) hc').trans_eq (mul_assoc ..).symm) hδ
end YM.RGLocalTaylor.Consumer
