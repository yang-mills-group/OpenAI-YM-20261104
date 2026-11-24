import YM.Integration.WilsonOriginalGeneralRosterHomePage
import YM.Integration.WilsonOriginalPublicNodalQuadraticCutoffSelf

/-! The uncentered adjoint self of each named physical field is measured at
its own radius on the common union grid. Its bound precedes the small-radius
limit and applies to any finite signed nodal test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalGeneralRosterHomeSelf
open Function Filter Finset Set Lattice Wilson RG Source Labels Cells OPE Extraction Spec
open Table Table.Pairing Extraction.Banks RG17 PhysicalNext.Repeat.Legato Climb GapsContact Next.Rank
open XSpace XSpace.Normalize XSpace.Rose MS MS.Menus MS.Land MS.Theater Local.Physical
open FVA2 FVA2.Register Trace.Pilot PhysMS Frame XSpace.Structure1 Maxwell Maxwell.Wick
open WilsonOriginalBlissMixedGram (columns grades)
open WilsonMeasuredPublicEntranceOrderedPins (physical)
open WilsonPositionHomogeneousFrame (homogeneous)
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMovingForkOpticalBook (reporter)
open WilsonThermometerUnitFilingFourPoolClock (outer longer)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
  (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
  {I:Type}[Fintype I]{D T:ℕ}{δ:ℝ}

theorem original (J:ℝ→tower S)(Z:WilsonPrescription G)(simple:G.Simple)(bliss:Bliss F l z H)
    (lead:Leading F J)(earned:∀d,∀ᶠr in trail,Frame.obedient F H (J r) d)(below:(l:Filter (ℕ×ℕ))≤order.fuse)
    (books:(s:{s:ℝ//0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)(d:I→Fin (D+1))
    (x:∀i,RG17.Free R.family (d i).val)(ax:I→Axis)(E:I→Set (Points 2))(compact:∀i,IsCompact (E i))
    (sep:∀i,E i⊆conf 2)(h:ℕ):
    ∃B:I→ℝ,(∀i,0≤B i) ∧ ∀ᶠr in trail,∀ρ:I→{s:ℝ//0<s ∧ s<δ},
    (∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→
    let f:=reporter F books ρ
    ∀(i:I)(branch:Bool),let arm:=((books (ρ i)).rows (d i)).arm branch (homogeneous F J Z (ρ i).val (d i).val (x i))
    ∀(τ:Type)[Fintype τ](o:τ→Fin 2 → Cover)(pos:τ→Points 2)(μ:τ→ℂ),(∀s,pos s∈E i)→
      (∀s,Order.grid R.family f (o s)=(ρ i).val • pos s)→∀ε:ℝ,0<ε→∀ᶠw:ℕ×ℕ in (l:Filter (ℕ×ℕ)),
        ‖∑s,μ s*physical (grades (d i).val (d i).val) f (o s) w.1 w.2
          (columns R (ax i) (d i).val (d i).val (arm.source w) (arm.source w))‖≤(∑s,‖μ s‖)*B i+ε:=by
  choose B nonneg paid using fun i=>WilsonOriginalPublicNodalQuadraticCutoffSelf.original R F J Z (d i).val
    (ax i) (x i) simple lead earned below (compact i) (sep i)
  obtain ⟨limit,lp,uniform⟩:=mem_nhdsGT_iff_exists_Ioc_subset.mp (Filter.eventually_all.mpr paid)
  refine ⟨B,nonneg,?_⟩
  filter_upwards [(longer F simple bliss h).eventually ((eventually_le_nhds lp).filter_mono nhdsWithin_le_nhds)] with r small
  intro ρ span f i branch arm τ count o pos μ hit placed tol ep
  have live:=uniform (Set.mem_Ioc.mpr ⟨(ρ i).property.1,((span i).2).trans small⟩) i
  exact live arm f o pos μ hit placed (fun s=>by rw [placed s];exact Work.A05.smul_conf (ρ i).property.1 (sep i (hit s))) tol ep

end YM.Integration.WilsonOriginalGeneralRosterHomeSelf
end
