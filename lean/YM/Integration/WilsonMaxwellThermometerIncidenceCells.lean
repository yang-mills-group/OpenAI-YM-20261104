import YM.Integration.WilsonMaxwellThermometerConnectedIncidenceRate
import YM.Integration.WilsonMaxwellThermometerShiftedPanel

/-! Pointwise O(spacing) on the genuine rounded Rose cells, for every
finite signed moving source expansion. The same three roots and their
proper marked marginals enter the complete centered value. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerIncidenceCells
open Filter Set Finset Function Metric MeasureTheory Lattice Wilson Maxwell Maxwell.Free XSpace XSpace.Cirrus
open XSpace.Normalize XSpace.Structure1 XSpace.Rose XSpace.Photo XSpace.Retirement
open WilsonMaxwellThermometerBareIncidenceRate (assembled)
open WilsonMaxwellThermometerConnectedIncidenceRate (row)
open WilsonMaxwellThermometerInteracting (face)
open WilsonPositionThermometerConnected (value)
open WilsonMaxwellThermometerShiftedPanel
open scoped Topology BigOperators Classical
variable {G:Gauge}(W:Initialize G)

theorem continuum (x:Points 3)(p:Tags G 6 3):
    row (scene x 6) p=WilsonMaxwellThermometerFaces.connected x p:=by
  change value _ = PowerSeries.constantCoeff (b3 _)
  simp [b3,value,Algebra.smul_def]
  rfl

private theorem local_germ (p:Tags G 6 3){x:Points 3}(hx:x∈conf 3):
    ContDiffAt ℝ 1 (fun y:Points 3=>row (scene y 6) p) x:=by
  have v:ContDiff ℝ 1 value:=by unfold value;fun_prop
  apply v.contDiffAt.comp x
  apply contDiffAt_pi.mpr
  intro s
  exact (Wick.moment_smooth (fun i=>(missing p s i).val) hx).of_le (by simp)

theorem raised (p:Tags G 6 3){K:Set (Points 3)}(compact:IsCompact K)(apart:K⊆conf 3):
    ∃C:ℝ,0≤C ∧ ∀ᶠ M in Front,∀x∈K,∀u:pack 3,∀c∈M.Box,
    dist (M.rel u c) x≤12*M.spacing →
      ‖row (live W 6 ⟨M,u,c⟩ 0) p-row (scene x 6) p‖≤C*M.spacing:=by
  obtain ⟨r,hr,legal⟩:=compact.exists_cthickening_subset_open (conf_open _) apart
  let T:=cthickening r K
  have ct:IsCompact T:=compact.cthickening
  have loc:LocallyLipschitzOn T (fun y:Points 3=>row (scene y 6) p):=by
    intro x hx
    obtain ⟨L,t,ht,hl⟩:=(local_germ p (legal hx)).exists_lipschitzOnWith
    exact ⟨L,t,mem_nhdsWithin_of_mem_nhds ht,hl⟩
  obtain ⟨L,lip⟩:=loc.exists_lipschitzOnWith_of_compact ct
  obtain ⟨C,Cpos,initial⟩:=WilsonMaxwellThermometerConnectedIncidenceRate.ground W p ct legal
  have limit:=frontier.endpt.const_mul (12:ℝ)
  rw [mul_zero] at limit
  refine ⟨C+12*L,by positivity,?_⟩
  filter_upwards [initial,limit.eventually (gt_mem_nhds hr)] with M fee small
  intro x hx u c hc near
  have xT:x∈T:=self_subset_cthickening K hx
  have tT:M.rel u c∈T:=mem_cthickening_of_dist_le (M.rel u c) x r K hx (near.trans small.le)
  have ld:=lip.dist_le_mul (M.rel u c) tT x xT
  rw [dist_eq_norm] at ld
  calc
    _ ≤ ‖row (live W 6 ⟨M,u,c⟩ 0) p-row (scene (M.rel u c) 6) p‖+
        ‖row (scene (M.rel u c) 6) p-row (scene x 6) p‖:=by
          simpa only [dist_eq_norm] using dist_triangle (row (live W 6 ⟨M,u,c⟩ 0) p)
            (row (scene (M.rel u c) 6) p) (row (scene x 6) p)
    _ ≤ C*M.spacing+L*(12*M.spacing):=add_le_add (fee u c hc tT)
      (ld.trans (mul_le_mul_of_nonneg_left near L.coe_nonneg))
    _ = (C+12*L)*M.spacing:=by ring

theorem original {I:Fin 3→Type}[∀j,Fintype (I j)](f:∀j,I j→Sec G 6)
    {K:Set (Points 3)}(compact:IsCompact K)(apart:K⊆conf 3):
    ∃C:ℝ,0≤C ∧ ∀ᶠ M in Front,∀x∈K,
    ∀v:∀j,I j→ℂ,
    ‖row (live W 6 (translated M (Extraction.address M.spacing x)) 0) (assembled 6 f v)-
      WilsonMaxwellThermometerFaces.connected x (assembled 6 f v)‖≤
      (C*M.spacing)*∏j,∑i,‖v j i‖:=by
  choose fee pos good using fun b:∀j,I j=>raised W (fun j=>f j (b j)) compact apart
  let C:=∑b,fee b
  refine ⟨C,sum_nonneg (fun b _=>pos b),?_⟩
  filter_upwards [eventually_all.mpr good,accepted] with M paid ctr
  intro x hx v
  let t:=translated M (Extraction.address M.spacing x)
  have near:dist (familiar t) x≤12*M.spacing:=by
    rw [location];convert Extraction.approximate M.positive x using 1;norm_num
  rw [←continuum]
  let A:=row (live W 6 t 0)-row (scene x 6)
  change ‖A (fun j=>∑i,v j i •f j i)‖≤_
  rw [MultilinearMap.map_sum_finset]
  calc
    _≤∑b:∀j,I j,‖A (fun j=>v j (b j) • f j (b j))‖:=norm_sum_le ..
    _≤∑b:∀j,I j,(C*M.spacing)*∏j,‖v j (b j)‖:=by
      apply sum_le_sum;intro b _
      rw [A.map_smul_univ,norm_smul,norm_prod,mul_comm]
      apply mul_le_mul_of_nonneg_right _ (prod_nonneg fun _ _=>norm_nonneg _)
      have cb:fee b≤C:=single_le_sum (f:=fee) (fun j _=>pos j) (mem_univ b)
      exact (paid b x hx t.layout t.center ctr near).trans (mul_le_mul_of_nonneg_right cb M.positive.le)
    _= _:=by rw [←mul_sum,Fintype.prod_sum]

end YM.Integration.WilsonMaxwellThermometerIncidenceCells
