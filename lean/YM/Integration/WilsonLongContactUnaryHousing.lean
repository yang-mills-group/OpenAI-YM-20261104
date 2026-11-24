import YM.Integration.WilsonLongContactNearLetter

/-! The original forest-and-tag readout of the registered single regular address. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.PhysicalNext.Repeat.WilsonLongContactUnaryHousing
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

include key in
theorem named : solitary S M=Brim.head (S:=S) i := by
  rw [solitary,Finset.map_singleton]
  change {M.turn.badge S}=_
  rw [key];rfl

include key in
theorem live : Ac.Spark H.supportP (solitary S M) ∧ troupe T R Q.halo (radiusB x) (solitary S M) ∧
    roster (solitary S M)=bareStores S := by
  rw [named i M key]
  refine ⟨⟨Finset.singleton_nonempty _,?_⟩,Brim.pistil i Q.halo _⟩
  intro a ha b hb
  obtain rfl:=Finset.mem_singleton.mp ha
  obtain rfl:=Finset.mem_singleton.mp hb
  exact .refl

include key in
theorem received (F : Forest S.ratio) (χ : Chi) (base V : Config G c)
    (healthy : Healthy (Pressure.temp x) (Brim.plate H i).support base) :
    (town T M).grove (prism T x χ o.K V F) (solitary S M) W o.a Q.table Q.halo =
      likely (fun tag:S.Choices=>(town T M).cinema (vary (Brim.foyer H i F χ base tag) V) (solitary S M)
        W o.a Q.table Q.halo (podium S G (Brim.plate H i).support (radiusB x))) := by
  classical
  have hp:=live H i M key
  have support : H.unionP (solitary S M)=(Brim.plate H i).support := by
    rw [named i M key,Brim.concern]
  have flag : (roster (solitary S M)).flags=∅ := by rw [hp.2.2];rfl
  have safe : Healthy (Pressure.temp x) (H.unionP (solitary S M)) base := support ▸ healthy
  unfold Township.grove
  rw [if_pos ⟨hp.1,hp.2.1⟩]
  apply congrArg likely
  funext tag
  have bought:=(town T M).casin (prism T x χ o.K base F) (solitary S M) H rfl flag safe tag V V
    (fun _ _ _=>rfl) (W:=W) (a:=o.a) (Ñ:=Q.table)
  rw [named i M key] at bought support ⊢
  have space : ground R T Q.halo (radiusB x) (Brim.head (S:=S) i)=(Brim.plate H i).support := support
  rw [show (prism T x χ o.K V F).B=radiusB x from rfl,space]
  have fixed : vary (Greenbelt.prism T x χ o.K base F) V=Greenbelt.prism T x χ o.K V F := rfl
  rw [fixed] at bought
  simpa only [Brim.foyer,support] using bought.symm

end YM.PhysicalNext.Repeat.WilsonLongContactUnaryHousing
