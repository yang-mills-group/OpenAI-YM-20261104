import YM.Integration.WilsonThermometerWeakFiledPrimary
import YM.Integration.WilsonThermometerWeakReflectedRows

/-! Calibrate the original displaced weak basis before prescribing any detector
dilation. The compensated, self-contracted basis has a uniformly priced exact
inverse and retains its all-field physical invoices at this same cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakBasisCalibration
open Function Filter Set Lattice Wilson RG Source Labels RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Trace.Physical Push.Local GermGraph Next.Rank.Spindle Next.Rank Configuration Normal Rise
open Perch Glimmer LiftMark Beamer Station Atlas Tariffs MvPolynomial Ribbon Asymptotics
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open WilsonThermometerOwnOffsetTale
open scoped Classical Topology BigOperators
variable {G:Gauge} {d:ℕ} (F:Frame G d)

private def readBasis (H:F.Index→F.Coeff):F.Coeff→ₗ[ℂ]F.Coeff where
  toFun u:=∑ i,u i•H i
  map_add' x y:=by simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' z x:=by simp only [Pi.smul_apply,Finset.smul_sum,smul_smul,RingHom.id_apply,smul_eq_mul]

private theorem calibrate (H:F.Index→F.Coeff)
    (h:∀ i,F.coeffSize (H i-Size.axis F i)≤1/2):
    ∃ T:F.Coeff≃ₗ[ℂ]F.Coeff,(∀ i,T (Size.axis F i)=H i) ∧
      (∀ u,F.coeffSize (T.symm u)≤2*F.coeffSize u):=by
  let M:=readBasis F H
  have err (v:F.Coeff):F.coeffSize (M v-v)≤(1/2)*F.coeffSize v:=by
    have eq:M v-v=∑ i,v i•(H i-Size.axis F i):=by
      simp only [smul_sub,Finset.sum_sub_distrib,Size.sum_axes];rfl
    rw [eq]
    apply (Size.finite F _ _).trans
    simp only [Size.smul]
    calc
      _ ≤ ∑ i,‖v i‖*(1/2):=Finset.sum_le_sum fun i _=>mul_le_mul_of_nonneg_left (h i) (norm_nonneg _)
      _ = _:=by rw [← Finset.sum_mul,mul_comm];rfl
  have budget (v:F.Coeff):F.coeffSize v≤2*F.coeffSize (M v):=by
    have eq:v=(-(M v-v))+M v:=by abel
    have neg:F.coeffSize (-(M v-v))=F.coeffSize (M v-v):=by change ∑ i,‖-(M v-v) i‖=∑ i,‖(M v-v) i‖;simp only [norm_neg]
    have sum:= (Size.add F (-(M v-v)) (M v))
    rw [←eq,neg] at sum
    linarith only [sum,err v]
  have inj:Injective M:=by
    intro v w eq
    have bd:=budget (v-w)
    rw [map_sub,eq,sub_self,show F.coeffSize 0=0 by simp [Frame.coeffSize],mul_zero] at bd
    exact sub_eq_zero.mp (norm_le_zero_iff.mp ((Size.norm_le F _).trans bd))
  let T:=LinearEquiv.ofBijective M ⟨inj,LinearMap.injective_iff_surjective.mp inj⟩
  refine ⟨T,?_,fun u=>(budget (T.symm u)).trans_eq ?_⟩
  · intro i;change ∑ j,Size.axis F i j•H j=H i
    rw [Finset.sum_eq_single i]; · simp [Size.axis]
    · intro j _ nav;simp only [Size.axis,Pi.single_eq_of_ne nav,zero_smul]
    · simp
  · exact congrArg (fun v=>2*F.coeffSize v) (T.apply_symm_apply u)

variable (R:Run G)
local notation "Rf" => R.family
local notation "Lev" => R.family.path.levels
local notation "B" => WilsonThermometerOffsetLedger.cash R

def input (d:ℕ) (i:((Rf).labels.level d).Index):Palette Rf d:=
  chunk (primaryLetter d) (Size.axis ((Rf).labels.level d) i)

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
    (∀ i,(q i).totalDegree≤D ∧ Spirit (W i) ∧
      ∀ U:Config G ((Rf).side k p),Healthy (tau (Lev) k) (Spindle.patch b 0) U →
      ‖(X i).exponentialEntry 0 ((Rf).localSection d) P U-signet 0 g (W i) U‖≤
        bill (1/8-(D:ℝ)) (clim (Lev) k)) ∧
    ∀ E:AtlasData G (Rf).S p,Hail Rf k p D E →
      ∃ T:F.Coeff≃ₗ[ℂ]F.Coeff,(∀ v,F.coeffSize (T.symm v)≤2*F.coeffSize v) ∧
      ∀ i,∃ v:F.Coeff,T (Size.axis F i)=F.scaled (P.p.threshold/g) v ∧
        expose F v=WilsonThermometerWeakGroupCoordinate.contracted R d wide E (W i):=by
  filter_upwards [WilsonThermometerWeakFiledPrimary.original R simple shop S d D hd (show (0:ℝ)<1/2 by norm_num)] with k fund N p hk P b m F g
  obtain ⟨K,wide,model⟩:=fund N p hk
  refine ⟨K,wide,?_⟩
  intro deg z V r accepted
  choose X form rem germ same posted using fun i:F.Index=>WilsonThermometerWeakReflectedRows.master R z hk (input R d i) accepted
  have mass (i:F.Index):size (input R d i)=1:=by rw [input,size_chunk];apply Size.size_axis
  choose q degQ spin fit bank using fun i=>model deg (X i) (input R d i) (form i) (rem i) (germ i)
  refine ⟨X,q,fun i=>⟨form i,by simpa only [mass,mul_one] using rem i,same i⟩,
    fun i=>⟨degQ i,spin i,fun U h=>by simpa only [mass,mul_one] using fit i U h⟩,?_⟩
  intro E hail
  choose v equal bound using fun i=>bank i E hail
  let b i:=F.scaled (P.p.threshold/g) (v i)
  have near (i:F.Index):F.coeffSize (b i-Size.axis F i)≤1/2:=by
    have h:=bound i;rw [mass,mul_one] at h
    change F.coeffSize (@Sub.sub F.Coeff _ (F.scaled (P.p.threshold/g) (v i)) (Size.axis F i))≤_
    simpa only [input,chunk_self] using h
  obtain ⟨T,cal,price⟩:=calibrate F b near
  exact ⟨T,price,fun i=>⟨v i,cal i,equal i⟩⟩

end YM.Integration.WilsonThermometerWeakBasisCalibration
end
