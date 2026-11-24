import YM.Integration.WilsonOriginalPublicEarnedGramWilson

/-! Full signed table convergence on the elected original Wilson cutoffs, measured at the genuine native optical sites. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicEarnedGramWilsonTable
open Filter Set Function Lattice Wilson RG Source Extraction RG17 Table Spec Climb
open FVA2 FVA2.Register
open Trace.Pilot PhysMS Frame XSpace XSpace.Normalize XSpace.Structure1 Maxwell Maxwell.Wick
open MS MS.Menus MS.Land MS.Theater Local.Physical PhysicalNext.Repeat.Legato
open WilsonOriginalPublicRelativeGramFreePanel (named pointsAt incidence)
open WilsonOriginalPublicRelativeGramLeading (fields)
open WilsonPositionProgramPublicWickGram (reading nodes)
open WilsonPositionProgramPublicContrast (assay)
open WilsonPositionHomogeneousFrame (homogeneous)
open WilsonMacroscopicRichTwoDatePivot (active)
open WilsonOriginalBlissMixedGram (grades)
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}
    (F:Spec.Final R.family f S)(J:ℝ→tower S)(Z:WilsonPrescription G)
    {Y:(Bel R.family.book).Hierarchy} (B:Deck G)(h:ℕ)(a:Axis)
local notation "I" => Glyph B h
local notation "D" => grades h h
local notation "B₀" => Bel R.family.book
local notation "E" => named R B h
local notation "dual" => (Bel R.family.book).adj (Maxwell.Free.spin_free R.family.labels) h a
local notation "goal" i:max j:max => fields R a (fun _:I=>h) (fun k=>E k) i j

open WilsonOriginalPublicRelativeGramOuterPhysical (truePair)
open WilsonOriginalPublicRelativeGramAddresses (ports shape)
open WilsonOriginalPublicRelativeGramReflectedLimit (entered ordered)
open WilsonOriginalPublicRelativeGramPins (readings matrix)
variable (ℓ:Ultrafilter (ℕ×ℕ))(avoid:Finset E4)


local notation "real" => ordered trail (fun _:ℝ=>(ℓ:Filter (ℕ×ℕ)))

open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalPublicRelativeGramPins (cutoff)
variable {arch:Trace.Terrace.Arch R.family}

open GapsContact.Seams Trace.Terrace
open WilsonOriginalPublicRelativeGramPins (cutoff matrix readings)

theorem original (simple:G.Simple)(bliss:Bliss F ℓ arch Y)(lead:Leading F J)
    (earned:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d):
    ∃Γ:WilsonViewerReportingGrid.Grid (ℓ:=ℓ) F h (wilson arch),∀δ:ℝ,0<δ →
    ∀ᶠr in trail,∀{height T:ℕ}(cap:h≤height)(book:Book F (l:=ℓ) Y arch height T r)(side:I→Bool),
    ∀ᶠb in (ℓ:Filter (ℕ×ℕ)),‖(fun i j=>cutoff R a (fun _:I=>h) (Γ.date r)
      (fun _:Unit=>ports R avoid (pointsAt a) (Γ.date r) r) (fun _:Unit=>(1:ℂ))
      (fun _ w j=>((book.rows ⟨h,Nat.lt_succ_of_le cap⟩).arm (side j)
        (homogeneous F J Z r h (E j))).source w) false b i j)-reading a (nodes a) (id:I→I)‖<δ := by
  let link:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  obtain ⟨Γ⟩:=WilsonViewerReportingGrid.original F simple bliss _ link h
  refine ⟨Γ,?_⟩
  intro δ dp
  let profile (r:ℝ):=shape avoid (pointsAt a) (R.family.S.a (Γ.date r)/r)
  let lo (r:ℝ):=truePair R F J Z B h a r (profile r)
  have result(i j:I):=WilsonOriginalPublicRelativeGramOuterPhysicalPins.shapeLimit R F J Z B h a ℓ avoid Γ simple link lead earned i j
  have lower:Tendsto lo trail (𝓝 (reading a (nodes a) (id:I→I))):=
    tendsto_pi_nhds.mpr fun i=>tendsto_pi_nhds.mpr fun j=>result i j
  filter_upwards [Metric.tendsto_nhds.mp lower (δ/2) (half_pos dp),self_mem_nhdsWithin (a:=(0:ℝ))] with r close rp
  intro height T cap book side
  let A(j:I):=(book.rows ⟨h,Nat.lt_succ_of_le cap⟩).arm (side j) (homogeneous F J Z r h (E j))
  let grid:=fun _:Unit=>ports R avoid (pointsAt a) (Γ.date r) r
  let high (b:ℕ×ℕ) := cutoff R a (fun _:I=>h) (Γ.date r) grid (fun _:Unit=>(1:ℂ))
    (fun _ w j=>(A j).source w) false b
  have paid(i j:I):Tendsto (fun b=>high b i j) (ℓ:Filter (ℕ×ℕ)) (𝓝 (lo r i j)):=by
    have ticket:=WilsonOriginalPublicRelativeGramPins.limit R F a (fun _:I=>h) J (fun k=>active F J Z r h (E k))
      r r (Γ.date r) grid (fun _:Unit=>(1:ℂ)) (fun _ w j=>(A j).source w) (fun _ j=>(A j).label)
      (fun _ j=>(A j).approaches) (fun b j=>by simpa [active] using (A j).represents) bliss.lies
      (fun _ _=>WilsonOriginalPublicRelativeGramAddresses.screened R avoid (pointsAt a) (Γ.date r) rp) false i j
    simpa [high,lo,grid,profile,WilsonOriginalPublicRelativeGramPins.matrix,WilsonOriginalPublicRelativeGramPins.readings,truePair,
      WilsonOriginalPublicRelativeGramAddresses.placed R avoid (pointsAt a) (Γ.date r) rp,active] using ticket
  have converge:Tendsto (fun b i j=>high b i j) (ℓ:Filter (ℕ×ℕ)) (𝓝 (lo r)):=
    tendsto_pi_nhds.mpr fun i=>tendsto_pi_nhds.mpr fun j=>paid i j
  filter_upwards [Metric.tendsto_nhds.mp converge (δ/2) (half_pos dp)] with b sold
  rw [←dist_eq_norm]
  exact (dist_triangle _ (lo r) _).trans_lt (by linarith only [close,sold])

end YM.Integration.WilsonOriginalPublicEarnedGramWilsonTable
