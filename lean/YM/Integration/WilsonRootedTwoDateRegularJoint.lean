import YM.Integration.WilsonRootedTwoDateMenu

/-! All genuine regular later entries factor through the same complete signed earlier barcode field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedTwoDateMenu
open Filter Function Finset Lattice Wilson RG Source Labels Marker FVA1
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.JointLoad
open Heir Heir.Suite Push.PriceCompiler Supply Push.SectorMeasure Push
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open PhysicalNext.Repeat.Daisy MergeProof Org GapsLocal.Renew
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonOriginalMarkedExistence ActualOriginalQReaders Extra.Trajectories
open scoped Classical BigOperators Topology
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {f : Side} {Y : RG.Rep G f} {Γ : Census V}
  {I K : Type} [Fintype I] [Fintype K]

omit [Fintype V] in
private theorem odour_quiet (b : Menu.Hat Γ Y) (U : Config G f) :
    (Menu.odour b U).part Γ.quiet=0 := by
  simp only [Menu.odour,Poly.part_send]
  split_ifs with h
  · exact False.elim (Menu.powered b h.symm)
  · rfl

theorem regular (old : I→Menu.Hat Γ Y) (fresh : K→Menu.Hat Γ Y)
    (keys : ∀i,∃k, Menu.WKey (fresh i)=.logKey k) (U : Config G f) :
    GapsLocal.Full.given (Sum.elim old fresh) 0 U=
      Poly.pass (∑j,Menu.odour (fresh j) U)*GapsLocal.Full.given old 0 U := by
  have quiet {L : Type} [Fintype L] (q : L→Menu.Hat Γ Y) : (∑i,Menu.odour (q i) U).part Γ.quiet=0 := by
    rw [Poly.part_sum]
    exact Finset.sum_eq_zero (fun i _=>odour_quiet (q i) U)
  have hard (j : K) (c : Box f) : Menu.fragrance (fresh j) U c=0 := by
    obtain ⟨k,hk⟩ := keys j
    change (fresh j).M.turn=.logKey k at hk
    simp [Menu.fragrance,MergeProof.entry,hk,Poly.send_zero]
  have zero : Accent.Mach Γ 0=0 := by simp [Accent.Mach,Poly.send_zero]
  rw [together,Extra.Trajectories.pass_add (quiet old) (quiet fresh)]
  simp only [hard,Finset.sum_const_zero,add_zero,GapsLocal.Full.given,zero,Extra.Trajectories.pass_zero,one_mul,mul_smul_comm]
  congr 1
  ac_rfl

end YM.Integration.WilsonRootedTwoDateMenu
