import YM.Integration.WilsonMovingForkSampleBank
import YM.Integration.WilsonMovingForkSignedGrid

/-! A signed smooth moving product and its complete basis comparison on one
original reporting lattice. The two tests keep their own integration weights. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkProfileGrid
open Function Filter Set MeasureTheory Metric Lattice Wilson RG Source Extraction Table Spec RG17 Climb
open GapsContact GapsContact.Ascent Contacts.Mat WilsonSeparatedGridDesign WilsonSeparatedBranchStencil WilsonSeparatedGridTree
open Trace.Pilot PhysMS PhysicalNext.Repeat.Legato Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register
open FVA2.O MS MS.Land MS.Theater
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot WilsonMacroscopicRichTwoDatePivot
open WilsonMacroscopicRichSignedAmplitude WilsonMacroscopicRichPositionRows WilsonMacroscopicRichMovingPlane
open WilsonPublicForkTestProduct WilsonMacroscopicRichTestGeometry
open WilsonMovingForkPositionIntegrals WilsonMovingForkProbeMaster WilsonMovingForkProbeDates
open WilsonMovingForkSampleBank WilsonMovingForkLocatedSamples
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonMovingForkOpticalBook (reporter)
open WilsonPublicForkPublicRows (probe)
open scoped Classical Topology BigOperators
attribute [local instance] Trial.count
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}{l:Ultrafilter (ℕ×ℕ)}
    (J:ℝ→PhysMS.tower S)(Z:WilsonPrescription G){n h:ℕ}(d:Fin n→ℕ)(v:∀i,Free R.family (d i))
    (B:Profiles R h)(w:B.probes.index→Atom (R:=R) h)
    (issued:∀j,B.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.book.grid h (w j))
local notation "a" => R.family.S.a
local notation "Kind" => Option (Dframe.Toon G h)

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (lead:Leading F J)(owed:∀d,∀ᶠr in trail,Frame.obedient F H (J r) d)
    (T A:ℕ){δ:ℝ}(books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z (cap h d) T s.val)
    (j:B.probes.index)(K:Set (Points n))(compact:IsCompact K)(separated:K⊆conf n):
    let φ:=profile (B.probes.shell j) (w j) (issued j) (test B j)
    let source:=dose d v (probe B w)
    ∃M:ℝ,0<M ∧ ∃η:ℝ,0<η ∧ ∃σ:ℝ,0<σ ∧ ∀(E:Type)[Fintype E](P:ℕ),
      ∃order:Kind→ℕ,∃price:Kind→ℝ,(∀k,0≤price k) ∧ ∀ᶠr in trail,∀rp:0<r,∀inBook:r<δ,
      ∀t:{s:ℝ // 0<s ∧ s<δ},r≤t.val → t.val≤outer z A r → r/t.val≤σ →
      let ρ:=dates (P:=B.probes.index) (G:=G) (h:=h) (n:=n) ⟨r,rp,inBook⟩ t
      let f₀:=reporter F books ρ
      let dp:=div_pos (R.family.S.a_pos f₀) rp
      let arm:=fun s=>homogeneous F J Z (ρ s).val (bound d s).val (source s)
      let obs(k:Kind)(x:Points (arity n k)):=S.classMoment S (fun i=>(bound d (ports j k i)).val) x
        (fun i=>arm (ports j k i))
      let X:=WilsonPublicOutputSmooth.exterior F J Z B w issued t.property.1 j
      let pub:=homogeneous F J Z r
      ∀ψ:Test n,tsupport ψ⊆K → ∀ε:ℝ,0<ε → ∀ref:E→E4,
      let Y:=RG17.appeared F (d:=d) (fun i=>pub (d i) (v i)) X r ψ
      let mat:=fun k=>X.charge F h (pub h (WilsonMSDictionaryVector.basis R.family h k))
      ∃ι:Type,∃_:Fintype ι,∃x:ι→space ψ φ,∃μ:ι→ℂ,∃κ:Type,∃_:Fintype κ,∃zz:κ→tsupport φ,∃ν:κ→ℂ,
      (∑i,‖μ i‖)≤Read.Value ψ*Read.Value φ+ε ∧ (∑b,‖ν b‖)≤Read.Value φ+ε ∧
      let pos:=fun u:Index ι κ G h=>site (fun i=>nearSite r t.val (x i).val) (fun b=>farSite r t.val (zz b).val) u
      let chart u:=sold (order (kind u)) ref dp (pos u)
      ∃o:∀u,(chart u).sample→Fin (arity n (kind u))→ Cover,
      (∀u b,tag (a f₀) (o u b)=r • (chart u).site b ∧ tag (a f₀) (o u b)∈generic _ ∧
        (∀i,‖R.family.S.gridPoint f₀ (o u b i)‖≤(M+1)*outer z A r) ∧
        Pairwise fun i k=>(η/2)*r≤‖R.family.S.gridPoint f₀ (o u b i)-R.family.S.gridPoint f₀ (o u b k)‖) ∧
      ∀c:Dframe.Toon G h→ℂ,let coin u (b:(chart u).sample):=mix μ ν c u*((chart u).weight b:ℂ)
        (∑u,∑b:(chart u).sample,‖coin u b‖)≤∑u,‖mix μ ν c u‖*(total (arity n (kind u)) (order (kind u)) E)^levels (arity n (kind u)) ∧
        ‖(Y-∑k,c k*mat k)-∑u,∑b:(chart u).sample,coin u b*obs (kind u) (tag (a f₀) (o u b))‖≤
          (ε+∑k,‖c k‖*ε)+∑u,‖mix μ ν c u‖*(price (kind u)*(∏i,‖source (ports j (kind u) i)‖)*(wilson z r)^P):=by
  intro φ source
  obtain ⟨M,mp,η,ep,σ,sp,located⟩:=WilsonMovingForkLocatedSamples.original F J Z d v B w issued j K compact separated
  refine ⟨M,mp,η,ep,σ,sp,?_⟩
  intro E _ P
  obtain ⟨m,fees,nonnegative,grid⟩:=WilsonMovingForkSignedGrid.original F J Z simple bliss slow lead owed
    (cap h d) T A (bound d) (M:=M) ep books (arity n) (ports j) E P
  refine ⟨m,fees,nonnegative,?_⟩
  filter_upwards [grid] with r screen
  intro rp small t rt reach gap ρ f₀ dp arm obs X pub ψ support ε positive ref Y mat
  let nearDate:{s:ℝ //0<s ∧ s<δ}:=⟨r,rp,small⟩
  obtain ⟨ι,_,x,μ,κ,_,zz,ν,massX,massZ,coveredX,coveredZ,_,_,physical⟩:=
    located nearDate t rt gap ψ support ε positive
  refine ⟨ι,inferInstance,x,μ,κ,inferInstance,zz,ν,massX,massZ,?_⟩
  intro pos chart
  have outerBound(u:Index ι κ G h)(i:Fin (arity n (kind u))):‖r • pos u i‖≤M*outer z A r:=by
    apply le_trans _ (mul_le_mul_of_nonneg_left reach mp.le)
    cases u with
    | inl k=>exact (coveredX k).1 i
    | inr k=>exact (coveredZ k.2).1 i
  have clear(u:Index ι κ G h)(i k:Fin (arity n (kind u)))(ne:i≠k):η≤dist (pos u i) (pos u k):=by
    cases u with
    | inl p=>exact (coveredX p).2 i k ne
    | inr p=>exact (coveredZ p.2).2 i k ne
  have datesPaid:=@WilsonMovingForkProbeDates.file_dates G n h B.probes.index δ nearDate t
  obtain ⟨roots,hits,returned⟩:=screen rp ρ (fun i=>⟨(datesPaid.2.2 rt i).1,((datesPaid.2.2 rt i).2).trans reach⟩)
    datesPaid.2.1 source ref kind pos outerBound clear
  refine ⟨roots,hits,?_⟩
  intro c coin
  have paid:=returned (mix μ ν c)
  refine ⟨paid.1,?_⟩
  have first:‖(Y-∑k,c k*mat k)-∑u,mix μ ν c u*obs (kind u) (r • pos u)‖≤ε+∑k,‖c k‖*ε:=by
    rw [WilsonMovingForkSampleBank.contrast]
    exact physical c
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add first paid.2)

end YM.Integration.WilsonMovingForkProfileGrid
end
