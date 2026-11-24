import YM.Integration.WilsonPhysicalPositiveAperture

/-! Coercivity at the caller's actual optical mesh on the elected public source. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalPositiveSameDate
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
local notation "E" => named R B h

open WilsonOriginalPublicRelativeGramOuterPhysical (truePair)
open WilsonOriginalPublicRelativeGramAddresses (ports shape)
open WilsonOriginalPublicRelativeGramReflectedLimit (entered ordered)
open WilsonOriginalPublicRelativeGramPins (readings matrix)
variable (ℓ:Ultrafilter (ℕ×ℕ))(avoid:Finset E4)



open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalPublicRelativeGramPins (cutoff)
variable {arch:Trace.Terrace.Arch R.family}

open GapsContact.Seams Trace.Terrace
open WilsonOriginalPublicRelativeGramPins (cutoff matrix readings)

open WilsonPhysicalPositiveHome (appointed)
theorem original (simple:G.Simple)(bliss:Bliss F ℓ arch Y)(lead:Leading F J)
    (earned:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d):
    ∃ε:ℝ,0<ε ∧ ∀ᶠr in trail,∀m:ℕ,R.family.S.a m/r<ε → ∀{height T:ℕ}(cap:h≤height)(book:Book F (l:=ℓ) Y arch height T r)(side:I→Bool),
    ∀ᶠb in (ℓ:Filter (ℕ×ℕ)),∀x:I→ℂ,(appointed B h a).k*‖x‖^2 ≤
      (assay x x (fun i j=>cutoff R a (fun _:I=>h) m
      (fun _:Unit=>ports R avoid (pointsAt a) m r) (fun _:Unit=>(1:ℂ))
      (fun _ w j=>((book.rows ⟨h,Nat.lt_succ_of_le cap⟩).arm (side j)
        (homogeneous F J Z r h (E j))).source w) false b i j)).re:=by
  let fee:=appointed B h a
  obtain ⟨ε,ep,ready⟩:=WilsonPhysicalPositiveAperture.original R F J Z B h a avoid simple lead earned
    (fee.δ/2) (half_pos fee.aperture)
  refine ⟨ε,ep,?_⟩
  filter_upwards [ready,self_mem_nhdsWithin (a:=(0:ℝ))] with r enrolled rp m live height T cap book side
  let Φ:=shape avoid (pointsAt a) (R.family.S.a m/r)
  let lo:=truePair R F J Z B h a r Φ
  have close:‖(fun i j=>lo i j)-reading a (nodes a) (id:I→I)‖≤fee.δ/2:=
    enrolled _ (div_pos (R.family.S.a_pos _) rp) live
  let A(j:I):=(book.rows ⟨h,Nat.lt_succ_of_le cap⟩).arm (side j) (homogeneous F J Z r h (E j))
  let grid:=fun _:Unit=>ports R avoid (pointsAt a) m r
  let high (b:ℕ×ℕ) := cutoff R a (fun _:I=>h) m grid (fun _:Unit=>(1:ℂ))
    (fun _ w j=>(A j).source w) false b
  have paid(i j:I):Tendsto (fun b=>high b i j) (ℓ:Filter (ℕ×ℕ)) (𝓝 (lo i j)):=by
    have ticket:=WilsonOriginalPublicRelativeGramPins.limit R F a (fun _:I=>h) J (fun k=>active F J Z r h (E k))
      r r m grid (fun _:Unit=>(1:ℂ)) (fun _ w j=>(A j).source w) (fun _ j=>(A j).label)
      (fun _ j=>(A j).approaches) (fun b j=>by simpa [active] using (A j).represents) bliss.lies
      (fun _ _=>WilsonOriginalPublicRelativeGramAddresses.screened R avoid (pointsAt a) m rp) false i j
    simpa [high,lo,grid,Φ,WilsonOriginalPublicRelativeGramPins.matrix,WilsonOriginalPublicRelativeGramPins.readings,truePair,
      WilsonOriginalPublicRelativeGramAddresses.placed R avoid (pointsAt a) m rp,active] using ticket
  have converge:Tendsto (fun b i j=>high b i j) (ℓ:Filter (ℕ×ℕ)) (𝓝 (lo)):=
    tendsto_pi_nhds.mpr fun i=>tendsto_pi_nhds.mpr fun j=>paid i j
  filter_upwards [Metric.tendsto_nhds.mp converge (fee.δ/2) (half_pos fee.aperture)] with b sold
  apply fee.paid
  have measured:‖(fun i j=>high b i j)-(fun i j=>lo i j)‖≤fee.δ/2:=by
    simpa only [dist_eq_norm] using sold.le
  exact (norm_sub_le_norm_sub_add_norm_sub _ (fun i j=>lo i j) _).trans
    (by linarith only [measured,close])

end YM.Integration.WilsonPhysicalPositiveSameDate
