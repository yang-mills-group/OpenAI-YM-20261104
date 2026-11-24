import YM.Integration.WilsonPhysicalShiftedFacePhase
import YM.Integration.WilsonPhysicalLicensedMaster
import YM.Integration.WilsonMeasuredPublicEntranceProfileMesh

/-! Transfer all the actual occupied cells of a fixed joint test under one
optical bed, for heterogeneous public homes and their single preselected roster. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalShiftedLicensedHead
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open WilsonReflectedPublicOrientedFaces
open Climb Maxwell Maxwell.Free MS.Land Next.Rank.Station MergeProof.East Next.UVStress Trace.Terrace
open GapsContact GapsContact.Seams GapsContact.Stamps Trace GapsContact.Ascent
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare
open RG16 RG16.Literal OPE Overlay Bid Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open WilsonOriginalTwoFlatPublicFare (charge)
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMovingForkOpticalBook (reporter)
open WilsonMeasuredPublicEntranceCellWords (physical)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
  (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}

variable {lo wid teach}(L:Package R.family wid lo teach)
local notation "C₀" => R.family
local notation "a_" => R.family.S.a
local notation "β" => (C₀).path.levels.clock.hatBeta

open WilsonAddressedPhysicalCells WilsonPhysicalLicensedFaces
open PertExtension PertExtension.LatticePT
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonPositionProgramReporterBand (Band)
open Pert.Asymptotics PhysMS
def receipt {D T n k:ℕ}(d:Fin n→Fin (D+1)){δ:ℝ}
    (books:(s:{y:ℝ //0<y ∧ y<δ})→Book F (l:=l) H z D T s.val)
    (ρ:Fin n→{y:ℝ //0<y ∧ y<δ})(q u f:ℕ)(s:(Stock.census (Fin n)).Mode)
    (width sep r scope:ℝ):Prop:=
  ∀φ:Test k,∀scale:ℝ,∀pick:Fin n→Fin k,∀origin:Fin n→ Cover,
    (∀x:Points k,φ x≠0→
      let center:=fun i=>(C₀).S.gridPoint f (origin i)+scale • x (pick i)
      (∀i,‖center i‖≤width*scope) ∧ Pairwise fun i j=>sep*r≤‖center i-center j‖) →
    ∀N per:ℕ,∀deep:f<N,∀uf:u≤f,∀weak:Fin n→Bool,∀v:∀i,S.Field (d i).val,
    ∀turn:Sites ((C₀).side f per) k→Fin n→Motion,
    ∀cell:Sites ((C₀).side f per) k,mass φ (a_ f) scale ((C₀).side f per) cell≠0 →
    let Y(i:Fin n):=(((books (ρ i)).rows (d i)).arm (weak i) (v i)).source (N,per)
    let raw:=physical R (fun i=>(d i).val) (N:=N) Y (turn cell)
      (fun i=>wrap ((C₀).side f per) (origin i)+cell (pick i)) s
    ‖(C₀).omega N per raw-actualTransport (C₀) (N:=N) raw (uf.trans deep.le) 1‖ ≤
      (∏i:↥s.val,Motion.orbitCost ((C₀).labels.level (d i).val)*
        charge F ((books (ρ i)).rows (d i)) f (weak i) (v i))*((β f)^q)⁻¹

include L in
theorem original {I:Type}[Fintype I][Nonempty I]{n k:ℕ}
    (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (forecast:WilsonReportLampForecast.Ready (C₀).path.levels)
    (D T h b:ℕ)(hb:h≤b)(d:I→Fin (D+1))(select:Fin n→I){δ:ℝ}
    (books:(s:{s:ℝ //0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    {width sep:ℝ}(wp:0<width)(sp:0<sep):
    ∃window:ℕ,∀u J depth stage goal q:ℕ,(C₀).ref 0≤u → Stop C₀ 0 J u →∀P:XSpace.Run,∀B:Band R P stage,
      ∃v:WilsonIndependentCapturedPages.Stop R P B u depth,∀floor:ℕ,∀ᶠr in trail,
      ∀ρ:I→{s:ℝ //0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→(∃i,(ρ i).val=r)→
      let f:=reporter F books ρ
      ∃t:ℕ,let c:=B.reporter+t
      floor≤c ∧ c+2≤f ∧ a_ c/a_ f≤(β f)^window ∧ u≤v.date t ∧ v.date t≤c ∧
      WilsonMovingForkMountedStage.Paid R P B v goal t ∧
      (∀N per:ℕ,c≤N→let g:=regulatorRun (C₀) N per c
        0<g ∧ g≤1 ∧ a_ c/a_ (v.date t)≤(g^depth)^2 ∧
        (C₀).S.scale c-(C₀).S.scale (v.date t)≤4*(2*depth+1)*Real.log g⁻¹) ∧
      ∀s:(Stock.census (Fin n)).Mode,s.val.Nonempty →
        receipt (k:=k) F (fun i=>d (select i)) books (fun i=>ρ (select i)) q u f s width sep r (outer z b r):=by
  classical
  obtain ⟨window,house⟩:=WilsonMovingForkPaidHousing.original F simple bliss slow forecast D T h b k hb d books (width+1) (by linarith)
  refine ⟨window,?_⟩
  intro u J depth stage goal q home ear P B
  obtain ⟨v,author⟩:=house u depth stage goal home P B
  obtain ⟨gate,paid⟩:=WilsonPhysicalLicensedSelection.selected F L simple slow ear d select books window q
  refine ⟨v,?_⟩
  intro floor
  have link:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  have wider:∀ᶠr in trail,r≤outer z b r:=by
    filter_upwards [link.positive,(link.conforms simple).eventually (ge_mem_nhds zero_lt_one),self_mem_nhdsWithin (a:=(0:ℝ))]
      with r gp small rp
    change 0<r at rp
    have gt:1≤(wilson z r)⁻¹:=(one_le_inv₀ gp).mpr small
    exact (mul_one r).symm.le.trans (mul_le_mul_of_nonneg_left (one_le_pow₀ gt) rp.le)
  filter_upwards [author (max (max floor (u+2)) gate),
    WilsonSeparatedPrefixMasterResolution.original (I:=I) F simple slow D T books (half_pos sp),
    WilsonMeasuredPublicEntranceProfileMesh.original (I:=I) F simple D T k books
      (t:=min 1 (sep/4)) (lt_min zero_lt_one (by positivity)),wider,self_mem_nhdsWithin (a:=(0:ℝ))]
    with r ledger clear refined broader rp
  change 0<r at rp
  intro ρ band near f
  obtain ⟨t,leGate,cf,range,wall,uv,vc,sold,fees⟩:=ledger ρ band near
  have base:max floor (u+2)≤B.reporter+t:=(le_max_left ..).trans leGate
  have cash:=paid ρ _ ((le_max_right ..).trans leGate) ((le_max_right ..).trans base) cf range
  have hmesh:4*(k:ℝ)*a_ f≤ min 1 (sep/4)*r:=refined ρ near
  have within:4*(k:ℝ)*a_ f≤outer z b r:=hmesh.trans ((mul_le_mul_of_nonneg_right (min_le_left ..) rp.le).trans (by simpa only [one_mul] using broader))
  have distance:4*(k:ℝ)*a_ f≤(sep/4)*r:=hmesh.trans (mul_le_mul_of_nonneg_right (min_le_right ..) rp.le)
  have enclosed:8*((width+1)*outer z b r)≤a_ (B.reporter+t+1):=by
    apply le_trans _ wall
    have a0:0≤4*(k:ℝ)*a_ f:=by exact mul_nonneg (by positivity) ((C₀).S.a_pos f).le
    linarith only [a0]
  refine ⟨t,(le_max_left ..).trans base,cf,range,uv,vc,sold,fees,?_⟩
  intro s occupied φ scale pick origin supp N per deep uf weak point turn cell hit
  exact WilsonPhysicalShiftedFacePhase.original F (fun i=>d (select i)) books (fun i=>ρ (select i)) s
    (cash s occupied) φ scale pick origin supp within distance enclosed (clear ρ near).le deep uf weak point turn cell hit

end YM.Integration.WilsonPhysicalShiftedLicensedHead
end
