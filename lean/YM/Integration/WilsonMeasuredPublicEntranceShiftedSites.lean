import YM.Integration.WilsonMeasuredPublicEntranceProfileSites
import YM.Integration.WilsonMeasuredPublicCompact
/-! Independent physical translations of correlated test coordinates have exact periodic sites and simultaneous lifted distance bounds on every occupied original cell. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceShiftedSites
open Function Set Filter Finset MeasureTheory Lattice Extraction RG Wilson Source
open PhysicalNext.Repeat.Legato RG16 RG16.Literal WilsonAddressedPhysicalCells
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)
local notation "C" => R.family

theorem original {n k:ℕ}(φ:Test k){f per:ℕ}(scale:ℝ)(pick:Fin n→Fin k)(origin:Fin n→Lattice.Cover)
    {width sep scope radius:ℝ}
    (support:∀x:Points k,φ x≠0→
      let center:=fun v=>(C).S.gridPoint f (origin v)+scale • x (pick v)
      (∀v,‖center v‖≤width*scope) ∧ Pairwise fun v w=>sep*radius≤‖center v-center w‖)
    (within:4*(k:ℝ)*(C).S.a f ≤ scope)(clear:4*(k:ℝ)*(C).S.a f≤(sep/4)*radius):
    ∃site:Sites ((C).side f per) k→Fin n→Lattice.Cover,
      (∀cell,snap (C) f per (site cell)=(fun v=>wrap ((C).side f per) (origin v)+cell (pick v))) ∧
      ∀cell,mass φ ((C).S.a f) scale ((C).side f per) cell≠0 →
        (∀v,‖(C).S.gridPoint f (site cell v)‖≤(width+1)*scope) ∧
        Pairwise fun v w=>(sep/2)*radius≤‖(C).S.gridPoint f (site cell v)-(C).S.gridPoint f (site cell w)‖:=by
  classical
  let Gate:=fun cell:Sites ((C).side f per) k=>mass φ ((C).S.a f) scale ((C).side f per) cell≠0
  have sale(cell:Sites ((C).side f per) k):∃site:Fin n→Lattice.Cover,
      snap (C) f per site=(fun v=>wrap ((C).side f per) (origin v)+cell (pick v)) ∧ (Gate cell →
      (∀v,‖(C).S.gridPoint f (site v)‖≤(width+1)*scope) ∧
      Pairwise fun v w=>(sep/2)*radius≤‖(C).S.gridPoint f (site v)-(C).S.gridPoint f (site w)‖):=by
    by_cases hit:Gate cell
    · obtain ⟨x,position,active⟩:=WilsonSeparatedPrefixCellProfile.active φ _ scale _ ((C).S.a_pos f) cell hit
      let scan:=address ((C).S.a f) (scale • x)
      let site:=fun v=>origin v+scan (pick v)
      let center:=fun v=>(C).S.gridPoint f (origin v)+scale • x (pick v)
      refine ⟨site,?_,fun _=>?_⟩
      · funext v
        change wrap _ (origin v+scan (pick v))=_
        rw [map_add]
        exact congrArg (fun o=>wrap ((C).side f per) (origin v)+o) (congrFun position (pick v))
      · obtain ⟨room,apart⟩:=support x active
        have meter:=Extraction.approximate ((C).S.a_pos f) (scale • x)
        rw [dist_eq_norm] at meter
        have close (v:Fin n):‖(C).S.gridPoint f (site v)-center v‖≤4*(k:ℝ)*(C).S.a f:=by
          change ‖(C).S.gridPoint f (origin v+scan (pick v))-((C).S.gridPoint f (origin v)+_)‖≤_
          rw [@Work.B16.grid_add G R.family f (origin v) (scan (pick v)),add_sub_add_left_eq_sub]
          exact (PiLp.norm_apply_le (tag ((C).S.a f) scan - scale • x) (pick v)).trans meter
        constructor
        · intro v
          have norm:=norm_sub_le_norm_sub_add_norm_sub ((C).S.gridPoint f (site v)) (center v) 0
          simp only [sub_zero] at norm
          have original:‖center v‖≤width*scope:=room v
          nlinarith only [norm,original,(close v).trans within]
        · intro v w ne
          have measured:sep*radius≤‖center v-center w‖:=apart ne
          have front:=norm_sub_le_norm_sub_add_norm_sub (center v) ((C).S.gridPoint f (site v)) (center w)
          rw [norm_sub_rev (center v) ((C).S.gridPoint f (site v))] at front
          have rest:=norm_sub_le_norm_sub_add_norm_sub ((C).S.gridPoint f (site v)) ((C).S.gridPoint f (site w)) (center w)
          nlinarith only [measured,front,rest,(close v).trans clear,(close w).trans clear]
    · refine ⟨fun v=>lift (wrap ((C).side f per) (origin v)+cell (pick v)),?_,fun h=>(hit h).elim⟩
      funext v
      exact wrap_lift _
  choose site earned using sale
  exact ⟨site,fun cell=>(earned cell).1,fun cell=>(earned cell).2⟩

end YM.Integration.WilsonMeasuredPublicEntranceShiftedSites
end
