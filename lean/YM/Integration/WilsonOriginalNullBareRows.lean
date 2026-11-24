import YM.Integration.WilsonOriginalNullBareCatalogue
import YM.Integration.WilsonTrueProjectedLocatedSeedTail
import YM.Integration.WilsonMatrixOriginalGermBasis

/-! The aligned ultraviolet source has one primary vector and two null
accounts. Collect its signed components on their own numerical Wilson
carriers before charging their total variation. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOriginalNullBareRows
open Function Filter Finset Lattice Wilson RG Tree Org
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG16 Trace.Physical.Germ Trace.Physical.GermGraph Extra.Histories
open Source Labels Extra.Histories.Relay Trace.Physical
open WilsonOriginalNullCorridor
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){d N p j:ℕ}
local notation "C₀" => R.family
local notation "Fr" => R.family.labels.level d
local notation "A" => R.family.params
local notation "S" => R.family.localSection d
local notation "n₀" => R.family.side j p
local notation "P" => R.family.path.rep N p j
local notation "κ" => safety R.family j

def Paid (W:Rep G n₀)(o:Site n₀)(field:Config G n₀→ℂ)(fare:ℝ) : Prop :=
  ∃ (x:(C₀).label d) (v z:Coefficient Fr n₀) (B D:ℝ),
    v.Format o A W ∧ v.remBound o W κ B ∧ z.Format o A P ∧ z.remBound o P κ D ∧
    projection Fr A W.p.threshold o v=0 ∧ projection Fr A (P).p.threshold o z=0 ∧
    field=((calValues (C:=C₀) d N p j x) ∘ translate o)+(v.density o S W+z.density o S P) ∧ B+D ≤ fare

private theorem oneStore {T:Type*}[Fintype T](W:Rep G n₀)(o:Site n₀)
    {a c r s t:ℝ}(law:W.Lawful a c r s t)(dw:d ≤ W.p.order)(pw:d ≤ W.p.power)
    (u:T→ℂ)(v:T→ Coefficient Fr n₀)(B:T→ℝ)
    (fmt:∀l,(v l).Format o A W)(fee:∀l,(v l).remBound o W κ (B l))
    (zero:∀l,projection Fr A W.p.threshold o (v l)=0) :
    ∃ q:Coefficient Fr n₀,q.Format o A W ∧ q.remBound o W κ (∑l,‖u l‖*B l) ∧
      projection Fr A W.p.threshold o q=0 ∧ q.density o S W=∑l,u l • (v l).density o S W := by
  classical
  have pos:0<κ:=Real.sqrt_pos.mpr (Real.exp_pos _)
  obtain ⟨h,hf,hp,hz,he⟩:=WilsonTrueProjectedLocatedMerge.collect Fr A W o S law pos dw pw
    (fun l=>stretch (u l) (v l)) (fun l=>‖u l‖*B l) univ (fun l _=>by
      refine ⟨stretch_format _ (fmt l),stretch_rem _ (fee l),?_⟩
      rw [WilsonOriginalNullColumnSplit.scale_page A W o (v l) (u l) dw pw (fmt l) (fee l),zero l,smul_zero])
  refine ⟨h,hf,hp,hz,he.trans ?_⟩
  apply sum_congr rfl
  intro l _
  funext U
  exact stretch_density S W o (u l) (v l) U

theorem weighted {T:Type*}[Fintype T](W:Rep G n₀)(o:Site n₀)
    {a c r s t:ℝ}(law:W.Lawful a c r s t)(native:W.p=(P).p)(live:j ≤ N)
    (home:Opened C₀ d j p)(field:T→ Config G n₀→ℂ)(fare:T→ℝ)(u:T→ℂ)
    (axes:∀l,Paid R (d:=d) (N:=N) W o (field l) (fare l)) :
    Paid R (d:=d) (N:=N) W o (∑l,u l • field l) (∑l,‖u l‖*fare l) := by
  classical
  choose x v z B D vf vp zf zp vn zn exactField cap using axes
  have dims:=dimensions d N p j R.makes home.post live
  obtain ⟨h,hf,hp,hn,he⟩:=oneStore R W o law (native ▸ dims.1) (native ▸ dims.2) u v B vf vp vn
  obtain ⟨q,qf,qp,qn,qe⟩:=oneStore R P o (R.makes.wilson.represents N p j live).good dims.1 dims.2 u z D zf zp zn
  refine ⟨∑l,u l • x l,h,q,_,_,hf,hp,qf,qp,hn,qn,?_,?_⟩
  · rw [he,qe]
    let cm:=WilsonMatrixOriginalGermBasis.density C₀ R.makes d N p j home.post live
    funext U
    have lin:=congrFun (map_sum cm (fun l=>u l • x l) univ) (translate o U)
    change calValues (C:=C₀) d N p j (∑l,u l • x l) (translate o U)=_ at lin
    simp only [map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at lin
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.add_apply,Function.comp_apply,lin]
    rw [←sum_add_distrib,←sum_add_distrib]
    apply sum_congr rfl
    intro l _
    rw [congrFun (exactField l) U]
    simp only [Pi.add_apply,Function.comp_apply]
    change _=u l*calValues (C:=C₀) d N p j (x l) (translate o U)+_
    ring
  · rw [←sum_add_distrib]
    apply sum_le_sum
    intro l _
    simpa only [mul_add] using mul_le_mul_of_nonneg_left (cap l) (norm_nonneg (u l))

end YM.Integration.WilsonOriginalNullBareRows
