import YM.Integration.WilsonLongContactUnaryAverage

/-! The original forest-and-tag readout of the registered single regular address. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.PhysicalNext.Repeat.WilsonLongContactUnaryBloom
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus Greenbelt Brim Next.Foundations AnalyticBridge.LocalGaussianLaws
open YM.Integration.WilsonLongContactTown WilsonLongContactFrozenGaussian
open scoped Topology Classical BigOperators
variable {G : Gauge} {c f L : Side} {S : StepData c f} {R : Rep G f} {T : Tube G S}
    {P : Teller G} {Q : ConnectedActivityE6.Target G P} {W x μ α : ℝ} {o : Target.Order G W}
    (H : Cash W x μ L Q o α T R) (i : ℕ) (M : Leaf R) (key : M.turn=.logKey i)


open WilsonLongContactUnaryHousing WilsonLongContactUnaryAverage

theorem agree {I : Type} {a b : Fintype I} {u v : I → ℝ} (same : ∀ i,u i=v i) :
    @likely I a u=@likely I b v := by rw [Subsingleton.elim a b,funext same]

include key in
theorem physical (χ : Chi) (V : Config G c) :
    ((town T M).hire (solitary S M) V).lotus T x χ o.K W o.a Q.table Q.halo V (solitary S M)=
      masked (Pressure.temp x) (Brim.plate H i).support (fun U=>branch (T:=T) (Q:=Q) (o:=o) (x:=x) (W:=W) M χ U) V := by
  classical
  have hp:=live H i M key
  have support : H.unionP (solitary S M)=(Brim.plate H i).support := by rw [named i M key,Brim.concern]
  have flag : (roster (solitary S M)).flags=∅ := by rw [hp.2.2];rfl
  unfold Faction.lotus branch
  by_cases clean : Healthy (Pressure.temp x) (Brim.plate H i).support V
  · rw [masked_eq _ _ _ _ clean]
    apply agree;intro r
    have paid:=(town T M).pictured (X:=prism T x χ o.K V (allot r)) (solitary S M) H rfl rfl flag
    rw [support] at paid
    exact paid.trans (masked_eq _ _ _ _ clean)
  · rw [masked_ne _ _ _ _ clean]
    trans likely (fun _ : Reserve S=>0)
    · apply agree;intro r
      have paid:=(town T M).pictured (X:=prism T x χ o.K V (allot r)) (solitary S M) H rfl rfl flag
      rw [support] at paid
      exact paid.trans (masked_ne _ _ _ _ clean)
    · exact likely_constant _

end YM.PhysicalNext.Repeat.WilsonLongContactUnaryBloom
