import YM.Integration.WilsonOriginalCompensatedAnchor
import YM.Integration.WilsonMatrixTicketLanesSmearedPair

/-! The actual corrected exterior legs of the previously filed two-site
matrix are uniformly affordable linear combinations of the physical J basis.
The coefficients are on the free space, before any cutoff and period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionSpectatorPrices
open Function Filter Set Finset Table Spec Climb Trace.Pilot PhysMS
open PhysicalNext.Repeat.Legato Maxwell Maxwell.Free RG17 FVA2 FVA2.Register
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot
open scoped Classical Topology BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ→tower S) (Z : WilsonPrescription G)
    {H : (Bel R.family.book).Hierarchy} (lead : Leading F J)
    (paid : ∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d) (simple : G.Simple)

def freeInput (d : ℕ) (r : ℝ) (v : RG17.Free R.family d) : RG17.Free R.family d :=
  WilsonPositionPrescribedLift.field F J Z.store d r (change F J Z d r v)

variable {ι : Type} [Fintype ι] (basis : Module.Basis ι ℂ (RG17.Free R.family 4))

def coefficient (r : ℝ) (v : RG17.Free R.family 4) (i : ι) : ℂ :=
  basis.coord i (freeInput F J Z 4 r v)

theorem physical (r : ℝ) (v : RG17.Free R.family 4) :
    homogeneous F J Z r 4 v=∑i,coefficient F J Z basis r v i • J r 4 (basis i) := by
  change J r 4 (freeInput F J Z 4 r v)=_
  rw [←(basis.sum_repr (freeInput F J Z 4 r v)),map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  congr 1

include lead paid simple in
theorem submitted (B : Profiles R 4)
    (sites : ∀j:B.probes.index,∃w:(standard R.family.labels).Ref 4,
      B.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.labels 4 w) :
    ∃(w:B.probes.index→(standard R.family.labels).Ref 4) (K:ℝ),0<K ∧
      (∀j,B.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.labels 4 (w j)) ∧
      ∀ᶠr in trail,∀j,
        let v:=(Bel R.family.book).project 4 (w j)
        (∑i,‖coefficient F J Z basis r v i‖)≤K ∧
        homogeneous F J Z r 4 v=∑i,coefficient F J Z basis r v i • J r 4 (basis i) := by
  choose w shell using sites
  let v:=fun j:B.probes.index=>(Bel R.family.book).project 4 (w j)
  let charge:=fun j:B.probes.index=>∑i,‖basis.coord i (v j)‖
  let K:=1+∑j,charge j
  have nonneg (j) : 0 ≤ charge j:=Finset.sum_nonneg fun _ _=>norm_nonneg _
  have room (j) : charge j<K:=by
    have upto:=Finset.single_le_sum (fun j _=>nonneg j) (Finset.mem_univ j)
    dsimp [K]; linarith
  have point (j) (i) : Tendsto (fun r=>coefficient F J Z basis r (v j) i) trail (𝓝 (basis.coord i (v j))) := by
    exact (basis.coord i).continuous_of_finiteDimensional.continuousAt.tendsto.comp
      (WilsonOriginalCompensatedAnchor.field F J Z lead paid simple 4 (v j))
  have limit (j) : Tendsto (fun r=>∑i,‖coefficient F J Z basis r (v j) i‖) trail (𝓝 (charge j)) :=
    tendsto_finsetSum _ fun i _=>(point j i).norm
  refine ⟨w,K,by dsimp [K]; positivity,shell,?_⟩
  apply eventually_all.mpr
  intro j
  filter_upwards [(limit j).eventually_lt_const (room j)] with r priced
  exact ⟨priced.le,physical F J Z basis r (v j)⟩

end YM.Integration.WilsonInvariantActionSpectatorPrices
