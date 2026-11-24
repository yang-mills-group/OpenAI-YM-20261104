import YM.Integration.WilsonMovingForkOwnRadiusPanel
import YM.Integration.WilsonMovingForkDilatedCuts
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 840000
noncomputable section
namespace YM.Integration.WilsonMovingForkOwnRadiusHearing
open Function Filter Set MeasureTheory Metric Lattice Wilson RG Source Extraction Table Spec RG17 Climb
open GapsContact GapsContact.Ascent Contacts.Mat WilsonSeparatedGridDesign WilsonSeparatedBranchStencil WilsonSeparatedGridTree
open Trace.Pilot PhysMS PhysicalNext.Repeat.Legato Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register
open FVA2.O MS MS.Land MS.Theater
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot WilsonMacroscopicRichTwoDatePivot
open WilsonMacroscopicRichSignedAmplitude WilsonMacroscopicRichPositionRows WilsonMacroscopicRichMovingPlane
open WilsonPublicForkTestProduct WilsonMacroscopicRichTestGeometry
open WilsonMovingForkPositionIntegrals WilsonMovingForkProbeMaster WilsonMovingForkProbeDates
open WilsonMovingForkSampleBank WilsonMovingForkLocatedSamples
open Pert.Asymptotics
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

theorem original (formation:(l:Filter _)≤f.fuse)(simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (lead:Leading F J)(owed:∀d,∀ᶠr in trail,Frame.obedient F H (J r) d)
    (T A reserve depth:ℕ){δ:ℝ}(books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z (cap h d) T s.val)
    (j:B.probes.index)(K:Set (Points n))(compact:IsCompact K)(separated:K⊆conf n):
    let φ:=profile (B.probes.shell j) (w j) (issued j) (test B j)
    let source:=dose d v (probe B w)
    ∃M:ℝ,0<M ∧ ∃η:ℝ,0<η ∧ ∃σ:ℝ,0<σ ∧ ∃width:ℕ,∀(E:Type)[Fintype E](P:ℕ),
      ∃order:Kind→ℕ,∃price:Kind→ℝ,(∀k,0≤price k) ∧ ∀ᶠr in trail,∀rp:0<r,∀inBook:r<δ,
      ∀t:{s:ℝ // 0<s ∧ s<δ},r≤t.val → t.val=outer z A r → r/t.val≤σ →
      let ρ:=dates (P:=B.probes.index) (G:=G) (h:=h) (n:=n) ⟨r,rp,inBook⟩ t
      let f₀:=reporter F books ρ
      let cutoff:=WilsonInvariantActionPosition.berth R reserve f₀
      let captured:=WilsonMovingForkOwnRadiusSites.capture R.family.S (M+1) r t.val
      captured≤f₀ ∧ a captured/a f₀≤R.family.path.levels.clock.hatBeta f₀^((2*T+11+2*A)+2*A+2) ∧
      (∀u N per,u≤captured → captured≤N →
        R.family.S.scale captured-R.family.S.scale u ≤
          4*(2*(depth:ℝ)+1)*Real.log (regulatorRun R.family N per captured)⁻¹ →
        a u/a cutoff≤R.family.path.levels.clock.hatBeta u^width ∧
          R.family.S.scale cutoff-R.family.S.scale u≤(width:ℝ)*(1+Real.log (R.family.path.levels.clock.hatBeta (u+1)))) ∧
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
        (∀i,‖R.family.S.gridPoint f₀ (o u b i)‖≤(M+1)*t.val) ∧
        WilsonMovingForkOwnRadiusSites.Recorded R f₀ captured (o u b) ∧
        Pairwise fun i k=>(η/2)*r≤‖R.family.S.gridPoint f₀ (o u b i)-R.family.S.gridPoint f₀ (o u b k)‖) ∧

      ∀c:Dframe.Toon G h→ℂ,let coin u (b:(chart u).sample):=mix μ ν c u*((chart u).weight b:ℂ)
        (∑u,∑b:(chart u).sample,‖coin u b‖)≤∑u,‖mix μ ν c u‖*(total (arity n (kind u)) (order (kind u)) E)^levels (arity n (kind u)) ∧
        ‖(Y-∑k,c k*mat k)-∑u,∑b:(chart u).sample,coin u b*obs (kind u) (tag (a f₀) (o u b))‖≤
          (ε+∑k,‖c k‖*ε)+∑u,‖mix μ ν c u‖*(price (kind u)*(∏i,‖source (ports j (kind u) i)‖)*(wilson z r)^P) ∧
        ∀mode:Seat G n h B.probes.index→Bool,
        let native:=fun s=>((books (ρ s)).rows (bound d s)).arm (mode s) (arm s)
        let node:=Σu:Index ι κ G h,(chart u).sample
        let fK:f₀≤cutoff:=(WilsonInvariantActionPosition.arrival R reserve f₀).1.le
        ∀(stopped grouped:node→(ℕ×ℕ)→ℂ)(cash:node→(ℕ×ℕ)→ℝ)(cross endFee:(ℕ×ℕ)→ℝ)(room:ℝ),
        (∀ᶠz₀:ℕ×ℕ in f.fuse,∀live:cutoff<z₀.1,∀s:node,
          ‖R.family.omega z₀.1 z₀.2 (WilsonOriginalTwoFlatGridCapture.word R
            (fun i=>(bound d (ports j (kind s.1) i)).val) f₀ z₀.1 z₀.2 (fK.trans live.le)
            (o s.1 s.2) (fun i=>(native (ports j (kind s.1) i)).source z₀))-stopped s z₀‖≤cash s z₀) →
        (∀ᶠz₀:ℕ×ℕ in f.fuse,‖∑s:node,coin s.1 s.2*(stopped s z₀-grouped s z₀)‖≤cross z₀) →
        (∀ᶠz₀:ℕ×ℕ in f.fuse,‖∑s:node,coin s.1 s.2*grouped s z₀‖≤endFee z₀) →
        (∀ᶠz₀:ℕ×ℕ in f.fuse,(∑s:node,‖coin s.1 s.2‖*cash s z₀)+cross z₀+endFee z₀≤room) →
        ‖Y-∑k,c k*mat k‖≤
          ((ε+∑k,‖c k‖*ε)+∑u,‖mix μ ν c u‖*(price (kind u)*(∏i,‖source (ports j (kind u) i)‖)*(wilson z r)^P))+room:=by
  intro φ source
  obtain ⟨M,mp,η,ep,σ,sp,width,origin⟩:=
    WilsonMovingForkOwnRadiusPanel.original F J Z d v B w issued simple bliss slow lead owed T A reserve depth books j K compact separated
  refine ⟨M,mp,η,ep,σ,sp,width,?_⟩
  intro E _ P
  obtain ⟨order,fee,nonneg,hearing⟩:=origin E P
  refine ⟨order,fee,nonneg,?_⟩
  filter_upwards [hearing] with r pay
  intro rp inBook t rt home gap ρ f₀ cutoff captured
  obtain ⟨older,nativeWidth,dates,seen⟩:=pay rp inBook t rt home gap
  refine ⟨older,nativeWidth,dates,?_⟩
  intro dp arm obs X pub ψ support ε positive ref Y mat
  obtain ⟨ι,_,x,μ,κ,_,zz,ν,nx,nz,start⟩:=seen ψ support ε positive ref
  refine ⟨ι,inferInstance,x,μ,κ,inferInstance,zz,ν,nx,nz,?_⟩
  intro pos chart
  obtain ⟨o,recorded,feeAt⟩:=start
  refine ⟨o,recorded,?_⟩
  intro c coin
  obtain ⟨totalPaid,stencil⟩:=feeAt c
  refine ⟨totalPaid,stencil,?_⟩
  intro mode native node fK stopped grouped cash cross endFee room finite matched measured bill
  have landed:=WilsonMovingForkDilatedCuts.original F
    (fun s:node=>arity n (kind s.1)) (fun s i=>(bound d (ports j (kind s.1) i)).val)
    (fun s i=>arm (ports j (kind s.1) i)) (fun s i=>native (ports j (kind s.1) i))
    (fun s=>o s.1 s.2) (fun s=>coin s.1 s.2) formation fK (fun s=>(recorded s.1 s.2).2.1)
    stopped grouped cash cross endFee room finite matched measured bill
  change ‖∑s:node,coin s.1 s.2*obs (kind s.1) (tag (a f₀) (o s.1 s.2))‖≤room at landed
  rw [Fintype.sum_sigma] at landed
  exact (show ‖Y-∑k,c k*mat k‖≤_ from (by
    simpa only [sub_zero] using norm_sub_le_norm_sub_add_norm_sub (Y-∑k,c k*mat k)
      (∑u,∑b:(chart u).sample,coin u b*obs (kind u) (tag (a f₀) (o u b))) 0)).trans (add_le_add stencil landed)

end YM.Integration.WilsonMovingForkOwnRadiusHearing
end
