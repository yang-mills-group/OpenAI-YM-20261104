import YM.Integration.WilsonSeparatedOriginalProfileAnchor
import YM.Integration.WilsonCloseCaptureCalendar
import YM.RG05Readout.Planes.Penumbra

/-! All of a fixed three-point parent census lies in the same actual predecessor
cell once its original block is large. The gauge field and test stay at their
submitted sites. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalProfileCentral
open Filter Finset Lattice Wilson RG Source RG05Readout MergeProof PhysicalNext.Repeat.Legato Bandage
open WilsonCloseCaptureCalendar
open scoped Classical BigOperators
variable {G:Gauge}

theorem reads {c f:Side}(A:Ratio c f)(odd:Odd A.count.val)(J:ℕ)(long:2*J+1 ≤ A.count.val)
    (x:Site f)(inside:separation x 0 ≤ J):
    A.parent x=0 ∧ A.residue x=wrap A.count (lift x):=by
  have hp:pdist x ≤ J:=by simpa only [separation,sub_zero] using inside
  have ht:lift x∈Lattice.box (A.count.val/2):=by
    rw [box_test]
    constructor <;> intro i <;> have h:=(component_le x i).trans hp <;> omega
  have placed:A.assemble (0,wrap A.count (lift x))=x:=by
    change A.root 0+wrap f (lift (wrap A.count (lift x)))=x
    rw [map_zero,zero_add,A.half_lift odd _ ht,wrap_lift]
  exact ⟨(congrArg A.parent placed).symm.trans (A.assemble_parent _),
    (congrArg A.residue placed).symm.trans (A.assemble_res _)⟩

theorem original (R:Run G)(simple:G.Simple)(portfolio:Funding R)(J:ℕ):
    ∀ᶠb:ℕ in atTop,∀per (o:Fin 3→Site (R.family.side (b+1) per)),
      o∈Pulse.area (C:=R.family) (p:=per) (b:=b+1) J → ∀i,
      let A:=R.family.S.oneStep b per
      A.parent (o i)=0 ∧ A.residue (o i)=wrap A.count (lift (o i)) ∧
      coverNumber ((R.family.path.levels.budget (b+1)).B) ({o 0,o i}:Support (R.family.side (b+1) per)) ≤
        Ribbons.peepers R.family.path.levels (b+1):=by
  obtain ⟨b₀,_,_,awake⟩:=(portfolio.dates 0 0 0 0).1.exists
  have grows:=Planes.lane_rises awake
  have permitted:∀ᶠb:ℕ in atTop,∀per (o:Fin 3→Site (R.family.side (b+1) per)),
      o∈Pulse.area (C:=R.family) (p:=per) (b:=b+1) J →
      ∀shift:Site (R.family.side (b+1) per),∀i,
        coverNumber ((R.family.path.levels.budget (b+1)).B) ({o 0+shift,o i+shift}:Support (R.family.side (b+1) per)) ≤
        Ribbons.peepers R.family.path.levels (b+1):=(tendsto_add_atTop_nat 1).eventually (WilsonSeparatedOriginalProfileAnchor.priced R.family simple J)
  filter_upwards [grows.eventually_ge_atTop (((2*J+1):ℕ):ℝ),permitted] with b long granted
  intro per o chosen i
  have size:2*J+1 ≤ (R.family.S.oneStep b per).count.val:=by
    change 2*J+1 ≤ (R.family.S.block b).val
    exact_mod_cast long
  have seats:=chosen; simp only [Pulse.area,Finset.mem_filter,mem_univ,true_and] at seats
  have exactSite:=reads (R.family.S.oneStep b per) (R.family.S.oneStep_odd b per) J size (o i) (seats i)
  exact ⟨exactSite.1,exactSite.2,by simpa only [add_zero] using granted per o chosen 0 i⟩

end YM.Integration.WilsonSeparatedOriginalProfileCentral
