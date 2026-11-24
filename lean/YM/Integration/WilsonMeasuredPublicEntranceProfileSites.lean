import YM.Integration.WilsonSeparatedPrefixCellProfile
import YM.Integration.WilsonAddressedMixedStationRange
import YM.Integration.WilsonReflectedPublicBulbBerth
/-! Actual cover lifts of a joint smooth test, with the physical reach and separation of every occupied periodic cell. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceProfileSites
open Function Set Filter Finset MeasureTheory Lattice Extraction RG Wilson Source
open PhysicalNext.Repeat.Legato RG16 RG16.Literal WilsonAddressedPhysicalCells
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)
local notation "C" => R.family

theorem lifted {n:ℕ}(φ:Test n){f per:ℕ}{r M η:ℝ}(rp:0<r)
    (shape:∀x:Points n,φ x≠0→(∀i,‖x i‖≤M) ∧ Pairwise fun i j=>η≤‖x i-x j‖)
    (small:4*(n:ℝ)*(C).S.a f≤r)(apart:4*(n:ℝ)*(C).S.a f≤(η/4)*r):
    ∃site:Sites ((C).side f per) n→Fin n→Lattice.Cover,
    (∀cell,snap (C) f per (site cell)=cell) ∧
    ∀cell,mass φ ((C).S.a f) r ((C).side f per) cell≠0 →
      (∀i,‖(C).S.gridPoint f (site cell i)‖≤(M+1)*r) ∧
      Pairwise fun i k=>(η/2)*r≤‖(C).S.gridPoint f (site cell i)-(C).S.gridPoint f (site cell k)‖:=by
  classical
  let Gate:=fun cell:Sites ((C).side f per) n=>mass φ ((C).S.a f) r ((C).side f per) cell≠0
  have pay(cell:Sites ((C).side f per) n):∃site:Fin n→Lattice.Cover,
      snap (C) f per site=cell ∧ (Gate cell →
      (∀i,‖(C).S.gridPoint f (site i)‖≤(M+1)*r) ∧
      Pairwise fun i k=>(η/2)*r≤‖(C).S.gridPoint f (site i)-(C).S.gridPoint f (site k)‖):=by
    by_cases hit:Gate cell
    · obtain ⟨x,atCell,active⟩:=WilsonSeparatedPrefixCellProfile.active φ _ r _ ((C).S.a_pos f) cell hit
      let site:=address ((C).S.a f) (r • x)
      refine ⟨site,atCell,fun _=>?_⟩
      obtain ⟨reach,sep⟩:=shape x active
      have grid:=Extraction.approximate ((C).S.a_pos f) (r • x)
      rw [dist_eq_norm] at grid
      have close(i:Fin n):‖(C).S.gridPoint f (site i)-r • x i‖≤4*(n:ℝ)*(C).S.a f:=
        (PiLp.norm_apply_le (tag ((C).S.a f) site-r • x) i).trans grid
      have size(i:Fin n):‖r • x i‖≤r*M:=by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos rp]
        exact mul_le_mul_of_nonneg_left (reach i) rp.le
      refine ⟨?_,?_⟩
      · intro i
        have bound:=norm_sub_le_norm_sub_add_norm_sub ((C).S.gridPoint f (site i)) (r • x i) 0
        simp only [sub_zero] at bound
        nlinarith only [bound,(close i).trans small,size i]
      · intro i j ne
        have nrm: r*η≤‖r • x i-r • x j‖:=by
          rw [←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos rp]
          exact mul_le_mul_of_nonneg_left (sep ne) rp.le
        have first:=norm_sub_le_norm_sub_add_norm_sub (r • x i) ((C).S.gridPoint f (site i)) (r • x j)
        rw [norm_sub_rev (r • x i) ((C).S.gridPoint f (site i))] at first
        have later:=norm_sub_le_norm_sub_add_norm_sub ((C).S.gridPoint f (site i)) ((C).S.gridPoint f (site j)) (r • x j)
        nlinarith only [nrm,first,later,(close i).trans apart,(close j).trans apart]
    · refine ⟨fun i=>lift (cell i),?_,fun h=>(hit h).elim⟩
      funext i
      exact wrap_lift _
  choose site receipt using pay
  exact ⟨site,fun cell=>(receipt cell).1,fun cell=>(receipt cell).2⟩

end YM.Integration.WilsonMeasuredPublicEntranceProfileSites
end
