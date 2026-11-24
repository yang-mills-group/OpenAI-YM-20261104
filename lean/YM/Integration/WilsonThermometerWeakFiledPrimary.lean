import YM.Integration.WilsonThermometerWeakColumnWallet

/-! On the original displaced Wilson intake the finitely posted weak coordinate
is uniformly close to its measured germ before either regulator. The same group
word carries the real healthy-aperture comparison after the physical valuation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakFiledPrimary
open Function Filter Set Lattice Wilson RG Source Labels RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Trace.Physical Push.Local GermGraph Next.Rank.Spindle Next.Rank Configuration Normal Rise
open Perch Glimmer LiftMark Beamer Station Atlas Tariffs MvPolynomial Ribbon Asymptotics
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G)
local notation "Rf" => R.family
local notation "Lev" => R.family.path.levels
local notation "B" => WilsonThermometerOffsetLedger.cash R

private theorem clock (A:Levels G) (a:ℝ):
    ∀ᶠ m:ℕ in atTop,a*A.clock.hatBeta m≤Real.exp (A.S.scale m):=by
  have hv : (fun s : ℝ => a*(A.clock.bar+G.slopeConstant*s)) =o[atTop] Real.exp := by
    have hh (n : ℕ) : (fun x : ℝ => x^n) =o[atTop] Real.exp := by simpa using isLittleO_pow_exp_pos_mul_atTop n (zero_lt_one' ℝ)
    have hx : _ := ((hh 0).const_mul_left A.clock.bar).add ((hh 1).const_mul_left G.slopeConstant)
    simpa using! (hx.const_mul_left a)
  have he := (hv.comp_tendsto A.S.divergent).def zero_lt_one
  filter_upwards [he] with m hm
  refine le_trans (le_abs_self _) ?_
  simpa only [Calendar.hatBeta,Function.comp_def,one_mul,Real.norm_eq_abs,abs_of_nonneg (Real.exp_pos _).le] using! hm

private theorem older (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b)
    (d:ℕ) {ε:ℝ} (hε:0<ε):
    ∀ᶠ k:ℕ in atTop,GermGraph.price (C:=Rf) d*Real.exp (-((Rf).S.scale k))*B d k≤ε :=by
  let c:=abs (GermGraph.price (C:=Rf) d)
  filter_upwards [WilsonThermometerOffsetLedger.original R simple shop d,clock (Lev) (4*c/ε)] with k h cap
  let b:=clim (Lev) k
  have b1:1≤b:=((Lev).fits.delayed k).le
  have hb:0<b:=zero_lt_one.trans_le b1
  have g:1+Real.log (2+Real.log b)≤4*b:=by
    have l:=Real.log_le_self hb.le
    have h:=Real.log_le_self (show 0≤2+Real.log b from add_nonneg (by norm_num) (Real.log_nonneg b1))
    linarith only [l,h,b1]
  have a:B d k≤4*b:=h.2.2.trans g
  have prod:=mul_le_mul_of_nonneg_left a (abs_nonneg (GermGraph.price (C:=Rf) d))
  have k':c*(4*b)≤ε*Real.exp ((Rf).S.scale k):=by
    calc
     _ = ((4*c/ε)*b)*ε:=by field_simp
     _ ≤ _ := (mul_le_mul_of_nonneg_right cap hε.le).trans_eq (mul_comm ..)
  rw [Real.exp_neg, mul_right_comm,←div_eq_mul_inv,div_le_iff₀ (Real.exp_pos _)]
  exact (mul_le_mul_of_nonneg_right (le_abs_self _) (zero_le_one.trans h.2.1)).trans (prod.trans k')

theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) (S:Rules G)
    (d D:ℕ) (hd:d≤D) {ε:ℝ} (hε:0<ε) :
    ∀ᶠ k:ℕ in atTop,∀ N p (_:k≤N),
    let P:=(Rf).path.rep N p k
    let b:=sizeQ Rf k
    let m:=scouts Rf k
    let F:=(Rf).labels.level d
    let g:=GaugeScale Rf k N p
    ∃ (K:Provision Rf d k N p m b) (wide:4*b≤wood (Lev) k),D+1≤P.p.order →
    ∀ (X:Coefficient F ((Rf).side k p)) (y:Palette Rf d),
    let cash:=B d k*size y
    X.Format 0 (Rf).params P → X.remBound 0 P (kappa (Rf).path k) cash →
    Germ.projection F (Rf).params P.p.threshold 0 X=y (primaryLetter d) →
    ∃ q:poly (Up Rf k p b),
    let W:=Spindle.sender K.length P.p.threshold g q
    q.totalDegree≤D ∧ Spirit W ∧
    (∀ U:Config G ((Rf).side k p),Healthy (tau (Lev) k) (Spindle.patch b 0) U →
      ‖X.exponentialEntry 0 ((Rf).localSection d) P U-signet 0 g W U‖≤
        bill (1/8-(D:ℝ)) (clim (Lev) k)*size y) ∧
    (∀ E:AtlasData G (Rf).S p,Hail Rf k p D E →
       ∃ z:F.Coeff,expose F z=WilsonThermometerWeakGroupCoordinate.contracted R d wide E W ∧
        F.coeffSize (@Sub.sub F.Coeff _ (F.scaled (P.p.threshold/g) z) (y (primaryLetter d))) ≤ ε*size y) := by
  let F₀:=(Rf).labels.level d
  obtain ⟨c,cpos,read⟩:=zone_cost F₀
  have gate:= (hat_rate (Lev) simple).eventually (transports (show (-3:ℝ)/8<0 by norm_num) (c/(ε/2)))
  filter_upwards [WilsonThermometerWeakGroupFiling.original R simple d D hd S,
    WilsonThermometerWeakColumnWallet.original R simple shop d (show (0:ℝ)<1/8 by norm_num),
    WilsonThermometerWeakTaylor.head (d:=d) R simple (-1),
    older R simple shop d (show 0<ε/2 by positivity),gate] with k filed fee head old small N p hk P b m F g
  obtain ⟨K,wide,model⟩:=filed N hk p
  refine ⟨K,wide,?_⟩
  intro degree X y cash format rem germ
  obtain ⟨q,degr,spin,healthy,wick⟩:=model degree X format rem
  let s:=clim (Lev) k
  let cap:=2*((Lev).params k).columns*F.coeffSize X.x
  let u:F.Coeff:= y (primaryLetter d)
  have bill0:=fee N p hk X y format rem germ
  refine ⟨q,degr,spin,?_,?_⟩
  · intro U hu
    refine (healthy U hu).trans ((mul_le_mul_of_nonneg_right bill0 (Real.exp_pos _).le).trans_eq ?_)
    change (Perch.bill (1/8) s*size y)*Perch.bill (-(D:ℝ)) s=Perch.bill (1/8-(D:ℝ)) s*size y
    rw [mul_right_comm,overlap];rfl
  · intro E hail
    obtain ⟨z,contracted,scaled⟩:=WilsonThermometerWeakGroupCoordinate.original R hk K.length wide E hail q spin
    refine ⟨z,contracted,?_⟩
    let z':=F.scaled (P.p.threshold/g) z
    have step:F.coeffSize (z'-X.x)≤c*((cap+cash)*bill (-(1/2)) s):=by
      apply le_trans (read (z'-X.x));apply mul_le_mul_of_nonneg_left _ cpos
      rw [map_sub,scaled];exact wick E hail
    have near:c*bill (-(3:ℝ)/8) s≤ε/2:=by
      rw [show Perch.bill 0 s = 1 by simp [Perch.bill]] at small
      have hs:=mul_le_mul_of_nonneg_right small (le_of_lt (show 0<ε/2 by positivity))
      dsimp only [s] at *
      calc
       _ = (c/(ε/2)*bill (-(3:ℝ)/8) (clim (Lev) k))*(ε/2):=by field_simp
       _ ≤ _:=by simpa only [one_mul] using hs
    have high:F.coeffSize (z'-X.x)≤(ε/2)*size y:=by
      apply step.trans
      calc
        _ ≤ c*((bill (1/8) s*size y)*bill (-(1/2)) s):=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right bill0 (Real.exp_pos _).le) cpos
        _ = (c*bill (-(3:ℝ)/8) s)*size y:=by rw [mul_right_comm (bill _ s),overlap];rw [show (1/8:ℝ)+ -(1/2)= -(3:ℝ)/8 by norm_num];ring
        _ ≤ _:=mul_le_mul_of_nonneg_right near (size_ge y)
    have hh:=head N p hk X u ⟨format,rem⟩ germ
    have low:F.coeffSize (u-X.x)≤(ε/2)*size y:=by
      apply hh.trans
      calc
        _ = (GermGraph.price (C:=Rf) d*Real.exp (-((Rf).S.scale k))*B d k)*size y :=by rw [neg_one_mul];ring
        _ ≤ _ :=mul_le_mul_of_nonneg_right old (size_ge y)
    have neg:F.coeffSize (-(u-X.x))=F.coeffSize (u-X.x):=by change ∑ i,‖-(u-X.x) i‖=∑ i,‖(u-X.x) i‖;simp only [norm_neg]
    change F.coeffSize (z'-u)≤_
    rw [show z'-u=(z'-X.x)+(-(u-X.x)) by abel]
    apply (Size.add ..).trans;rw [neg];linarith only [high,low]

end YM.Integration.WilsonThermometerWeakFiledPrimary
end
