import YM.Integration.WilsonThermometerWeakBasisCalibration
import YM.Integration.WilsonThermometerWeakMeasuredHead

/-! The measured angular price and corrected Weyl coordinates of one joint finite basis. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakMeasuredBasis
open Function Filter Set Lattice Wilson RG Source Labels RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Trace.Physical Push.Local GermGraph Next.Rank.Spindle Next.Rank Configuration Normal Rise
open Perch Glimmer LiftMark Beamer Station Atlas Tariffs MvPolynomial Ribbon Asymptotics
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open WilsonThermometerOwnOffsetTale
open scoped Classical Topology BigOperators
open WilsonThermometerWeakBasisCalibration
open private calibrate from YM.Integration.WilsonThermometerWeakBasisCalibration
variable {G:Gauge}
variable (R:Run G)
local notation "Rf" => R.family
local notation "Lev" => R.family.path.levels
local notation "B" => WilsonThermometerOffsetLedger.cash R

theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) (S:Rules G)
    (d D:ℕ) (hd:d≤D):
    ∀ᶠ k:ℕ in atTop,∀ N p (_:k≤N),
    let P:=(Rf).path.rep N p k
    let b:=sizeQ Rf k
    let m:=scouts Rf k
    let F:=(Rf).labels.level d
    let g:=GaugeScale Rf k N p
    ∃ (K:Provision Rf d k N p m b) (wide:4*b≤wood (Lev) k),D+1≤P.p.order →
    ∀ (z:Site ((Rf).side N p)) (V:Sight Rf d p) (r:Emblems Rf d),
    Enrolled R.makes R.doors B k N p d (digits R N p z) V r →
    ∃ (X:F.Index → Coefficient F ((Rf).side k p)) (q:F.Index→poly (Up Rf k p b)),
    let W:=fun i=>Spindle.sender K.length P.p.threshold g (q i)
    (∀ i,(X i).Format 0 (Rf).params P ∧ (X i).remBound 0 P (kappa (Rf).path k) (B d k) ∧
       V k (input R d i) (line (primaryLetter d))=invoice (X i) 0 ((Rf).localSection d) P) ∧
    (∀ i,coin (W i)≤2*bill (5/8) (clim (Lev) k) ∧ (W i).totalDegree≤D ∧ Spirit (W i) ∧
      ∀ U:Config G ((Rf).side k p),Healthy (tau (Lev) k) (Spindle.patch b 0) U →
      ‖(X i).exponentialEntry 0 ((Rf).localSection d) P U-signet 0 g (W i) U‖≤
        bill (1/8-(D:ℝ)) (clim (Lev) k)) ∧
    ∀ E:AtlasData G (Rf).S p,Hail Rf k p D E →
      ∃ T:F.Coeff≃ₗ[ℂ]F.Coeff,(∀ v,F.coeffSize (T.symm v)≤2*F.coeffSize v) ∧
      ∀ i,∃ v:F.Coeff,T (Size.axis F i)=F.scaled (P.p.threshold/g) v ∧
        expose F v=WilsonThermometerWeakGroupCoordinate.contracted R d wide E (W i):=by
  filter_upwards [WilsonThermometerWeakMeasuredHead.original R simple shop S d D hd (show (0:ℝ)<1/2 by norm_num)] with k fund N p hk P b m F g
  obtain ⟨K,wide,model⟩:=fund N p hk
  refine ⟨K,wide,?_⟩
  intro deg z V r accepted
  choose X form rem germ same posted using fun i:F.Index=>WilsonThermometerWeakReflectedRows.master R z hk (input R d i) accepted
  have mass (i:F.Index):size (input R d i)=1:=by rw [input,size_chunk];apply Size.size_axis
  choose q rent degQ spin fit bank using fun i=>model deg (X i) (input R d i) (form i) (rem i) (germ i)
  refine ⟨X,q,fun i=>⟨form i,by simpa only [mass,mul_one] using rem i,same i⟩,
    fun i=>⟨by simpa only [mass,mul_one] using rent i,(LiftMark.factor_degree ..).trans ((Rise.ascent ..).trans (degQ i)),spin i,fun U h=>by simpa only [mass,mul_one] using fit i U h⟩,?_⟩
  intro E hail
  choose v equal bound using fun i=>bank i E hail
  let b i:=F.scaled (P.p.threshold/g) (v i)
  have near (i:F.Index):F.coeffSize (b i-Size.axis F i)≤1/2:=by
    have h:=bound i;rw [mass,mul_one] at h
    change F.coeffSize (@Sub.sub F.Coeff _ (F.scaled (P.p.threshold/g) (v i)) (Size.axis F i))≤_
    simpa only [input,chunk_self] using h
  obtain ⟨T,cal,price⟩:=calibrate F b near
  exact ⟨T,price,fun i=>⟨v i,cal i,equal i⟩⟩

end YM.Integration.WilsonThermometerWeakMeasuredBasis
end
