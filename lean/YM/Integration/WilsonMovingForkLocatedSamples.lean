import YM.Integration.WilsonMovingForkPairGeometry
import YM.Integration.WilsonMovingForkPhysicalSamples

/-! Finite signed sampling of the actual smooth moving product and every
reflected basis row on the public fork's true fields.  All sites are expressed
on the single near reporter, with the distant field still at its real home. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkLocatedSamples
open Function Filter Set MeasureTheory Lattice Wilson RG Source Extraction Table Spec RG17 Climb
open Trace.Pilot PhysMS PhysicalNext.Repeat.Legato Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register
open FVA2.O MS MS.Land MS.Theater
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot WilsonMacroscopicRichTwoDatePivot
open WilsonMacroscopicRichSignedAmplitude WilsonMacroscopicRichPositionRows WilsonMacroscopicRichMovingPlane
open WilsonPublicForkTestProduct WilsonMacroscopicRichTestGeometry
open WilsonMovingForkPositionIntegrals WilsonMovingForkProbeMaster WilsonMovingForkProbeDates
open WilsonMovingForkLocalReceipt (physical)
open WilsonPublicForkPublicRows (probe)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    (J:ℝ→PhysMS.tower S)(Z:WilsonPrescription G){n h:ℕ}(d:Fin n→ℕ)(v:∀i,Free R.family (d i))
    (B:Profiles R h)(w:B.probes.index→Atom (R:=R) h)
    (issued:∀j,B.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.book.grid h (w j))

def nearSite (r t:ℝ)(p:Points n×Points 2):Points (n+1):=placed 1 (t/r) p.1 (relative p.2)
def farSite (r t:ℝ)(z:Points 2):Points 2:=(t/r) • z

def measured {δ:ℝ}(r t:{x:ℝ //0<x ∧ x<δ}){m:ℕ}(look:Fin m→Seat G n h B.probes.index)
    (x:Points m):ℂ:=
  S.classMoment S (fun i=>(bound d (look i)).val) (r.val • x)
    (fun i=>homogeneous F J Z (dates r t (look i)).val (bound d (look i)).val
      (dose d v (probe B w) (look i)))

theorem original (j:B.probes.index)(K:Set (Points n))(compact:IsCompact K)(separated:K⊆conf n):
    let φ:=profile (B.probes.shell j) (w j) (issued j) (test B j)
    ∃L:ℝ,0<L ∧ ∃η:ℝ,0<η ∧ ∃σ:ℝ,0<σ ∧ ∀{δ:ℝ}(r t:{x:ℝ // 0<x ∧ x<δ}),r.val≤t.val →
      r.val/t.val≤σ → ∀ψ:Test n,tsupport ψ⊆K → ∀ε:ℝ,0<ε →
      let X:=WilsonPublicOutputSmooth.exterior F J Z B w issued t.property.1 j
      let pub:=homogeneous F J Z r.val
      let Y:=RG17.appeared F (d:=d) (fun i=>pub (d i) (v i)) X r.val ψ
      let M:=fun k=>X.charge F h (pub h (WilsonMSDictionaryVector.basis R.family h k))
      let atSite:=@measured G R f S F J Z n h d v B w δ r t
      ∃ι:Type,∃_:Fintype ι,∃x:ι→space ψ φ,∃μ:ι→ℂ,∃κ:Type,∃_:Fintype κ,∃z:κ→tsupport φ,∃ν:κ→ℂ,
      (∑i,‖μ i‖)≤Read.Value ψ*Read.Value φ+ε ∧ (∑b,‖ν b‖)≤Read.Value φ+ε ∧
      (∀a,let p:=nearSite r.val t.val (x a).val
          (∀i,‖r.val • p i‖≤L*t.val) ∧ (∀i k,i≠k → η≤dist (p i) (p k))) ∧
      (∀b,let p:=farSite r.val t.val (z b).val
          (∀i,‖r.val • p i‖≤L*t.val) ∧ (∀i k,i≠k → η≤dist (p i) (p k))) ∧
      let full:=∑a,μ a * atSite (m:=n+1) (WilsonMovingForkProbeMaster.whole j) (nearSite r.val t.val (x a).val)
      let gram:=fun k=>∑b,ν b * atSite (m:=2) (pair k j) (farSite r.val t.val (z b).val)
      ‖Y-full‖≤ε ∧ (∀k,‖M k-gram k‖≤ε) ∧ ∀c:Dframe.Toon G h→ℂ,
        ‖(Y-∑k,c k*M k)-(full-∑k,c k*gram k)‖≤ε+∑k,‖c k‖*ε:=by
  intro φ
  obtain ⟨L,lp,η,ep,σ,sp,near⟩:=WilsonMovingForkSampleGeometry.original K compact separated φ
  obtain ⟨P,pp,ζ,zp,far⟩:=WilsonMovingForkPairGeometry.original φ
  refine ⟨max L P,lp.trans_le (le_max_left _ _),min η ζ,lt_min ep zp,σ,sp,?_⟩
  intro δ r t rt ratio ψ support ε small X pub Y M atSite
  have safe:∀x∈tsupport ψ,∀z∈tsupport φ,placed r.val t.val x (relative z)∈conf (n+1):=by
    intro x hx z hz i k e
    by_contra ne
    have gap:η≤dist ((nearSite r.val t.val (x,z)) i) ((nearSite r.val t.val (x,z)) k):=
      (near r.val t.val r.property.1 rt ratio x (support hx) z hz).2.1 i k ne
    rw [←(WilsonMovingForkSampleGeometry.scaled r.property.1 x z).1] at e
    have cancel:r.val • ((nearSite r.val t.val (x,z)) i)=r.val • ((nearSite r.val t.val (x,z)) k):=e
    have same:= (smul_right_injective _ r.property.1.ne') cancel
    rw [same,dist_self] at gap
    exact ep.not_ge gap
  obtain ⟨ι,_,x,μ,κ,_,z,ν,ymass,mmass,wholeFee,pairFee,groupFee⟩:=
    WilsonMovingForkPhysicalSamples.original F J Z d v B w issued r t ψ j small safe
  refine ⟨ι,inferInstance,x,μ,κ,inferInstance,z,ν,ymass,mmass,?_,?_,?_⟩
  · intro a p
    have room:=near r.val t.val r.property.1 rt ratio (x a).val.1 (support (x a).property.1)
      (x a).val.2 (x a).property.2
    exact ⟨fun i=>(room.1 i).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) t.property.1.le),
      fun i k ne=>(min_le_left _ _).trans (room.2.1 i k ne)⟩
  · intro b p
    have room:=far r.val t.val r.property.1 rt (z b) (z b).property
    exact ⟨fun i=>(room.1 i).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) t.property.1.le),
      fun i k ne=>(min_le_right _ _).trans (room.2 i k ne)⟩
  · intro full gram
    have wholeAt(a:ι):atSite (m:=n+1) (WilsonMovingForkProbeMaster.whole j) (nearSite r.val t.val (x a).val)=
        S.useAt S (placed r.val t.val (x a).val.1 (relative (x a).val.2))
          (physical F J Z (bound d) (dose d v (probe B w)) (dates r t) (WilsonMovingForkProbeMaster.whole j)):=by
      dsimp only [atSite,measured,nearSite];rw [(WilsonMovingForkSampleGeometry.scaled r.property.1 _ _).1];rfl
    have pairAt(k:Dframe.Toon G h)(b:κ):atSite (m:=2) (pair k j) (farSite r.val t.val (z b).val)=
        S.useAt S (t.val • (z b).val)
          (physical F J Z (bound d) (dose d v (probe B w)) (dates r t) (pair k j)):=by
      dsimp only [atSite,measured,farSite]
      have cancel:r.val*(t.val/r.val)=t.val:=by field_simp [r.property.1.ne']
      rw [smul_smul,cancel];rfl
    simpa only [full,gram,wholeAt,pairAt] using
      (show _ ∧ _ ∧ _ from ⟨wholeFee,pairFee,groupFee⟩)
end YM.Integration.WilsonMovingForkLocatedSamples
end
