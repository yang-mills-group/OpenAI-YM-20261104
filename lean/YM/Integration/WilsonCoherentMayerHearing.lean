import YM.Integration.WilsonCoherentMayerClear

/-! The two original finite tag averages of a marked coefficient on a
surviving elastic component, with the entire Mayer integrand still present
at its original orbit and Gaussian sample. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerHearing
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure RGLocalTaylor
open Coat Matter Pond Blaze.March PhysicalNext.Repeat Greenbelt PhysicalNext.Repeat.Legato
open Dict06.Series RGLocalTaylor.Insert
open scoped Topology BigOperators Classical
variable {G:Gauge} {c f L:Side} {S:StepData c f} {T:Tube G S}
variable {P:Teller G} {Q:ConnectedActivityE6.Target G P} {W s μ C:ℝ} {o:Target.Order G W}
  {R:Rep G f} (H:Cash W s μ L Q o C T R)

def chamber (T:Tube G S) (s K:ℝ) (χ:Chi) (V:Config G c) (v:Finset (LocalLTE.Fan.Veil c f))
    (i:Greenbelt.Reserve S) (tag:S.Choices) : Coat T (Greenbelt.allot i) :=
  (Matter.preps (Greenbelt.prism T s χ K V (Greenbelt.allot i))
    (roster (LocalLTE.Fan.arm (S:=S) v))).taggedL tag

def hearing (T:Tube G S) (s K:ℝ) (χ:Chi) (V:Config G c) (v:Finset (LocalLTE.Fan.Veil c f))
    (read:∀ {F:Forest S.ratio}, (X:Coat T F)→momentSpace X→ℝ) : ℝ :=
  likely fun i:Greenbelt.Reserve S=>likely fun tag:S.Choices=>
    let X:=chamber T s K χ V v i tag
    ∫ z,read X z ∂moment X

variable (run:Run G) {I:Type} [Fintype I] (d:I→ℕ) (θ:ℝ) (y:∀i,run.family.label (d i)) (loc:I→Site f)

def issued {F:Forest S.ratio} (X:Coat T F) (β:ℝ) (z:momentSpace X) : PowerSeries ℂ :=
  ∏ i, Dict06.Wil.book (run.family.localSection (d i))
    ((run.family.labels.level (d i)).scaled θ⁻¹ (y i))
    (expandAt (loc i) (WilsonCoherentMayerField.direction (X.wrapY z.1) β z.2))

variable {j n l k M:ℕ} {χ:Chi} {q η r a b d' v' Y C' A B price k' θ' wJ zJ:ℝ}

theorem original (v:Finset (LocalLTE.Fan.Veil c f)) {select:Molecule S}
    (u:Mayer.Decors select M) (hs:select⊆LocalLTE.Fan.arm (S:=S) v) (hw:Mayer.decorOrder u≤M)
    (N:Captain H j C' d' v' Y A b r B q n χ)
    (law:Awning H N.conduit A b price a wJ zJ k l)
    (room:Q.goal L s≤k') (allow:Mayer.Approved k' θ' j M) (f':Head S→Insert T)
    (cohort:Mayer.Start select) (temp:0≤Pressure.temp s) (β:ℝ) (e:ℕ) (phase:ℂ→L[ℝ]ℝ) :
    hearing T s o.K χ 1 v (fun X z=>
      (Mayer.tagged H (LocalLTE.Fan.arm v) f' u).joint X z *
      phase (ordinary e (WilsonCoherentMayerField.marked run d θ y loc X β z))) =
    hearing T s o.K χ 1 v (fun X z=>
      Mayer.planned H (LocalLTE.Fan.arm v) u f' X z * phase (PowerSeries.coeff e (issued run d θ y loc X β z))) :=by
  unfold hearing
  congr 1
  funext i
  congr 1
  funext tag
  dsimp only
  let X:=chamber T s o.K χ 1 v i tag
  have present:X.manifest:=by
    change (roster (LocalLTE.Fan.arm (S:=S) v)).flags=RG.flags (Pressure.temp s) (1:Config G c)
    rw [LocalLTE.Fan.Field.rosterD]
    exact (Greenbelt.prism T s χ o.K (1:Config G c) (Greenbelt.allot i)).bowed temp
  have emptyFlags:RG.flags (Pressure.temp s) (1:Config G c)=∅:=by
    change RG.flags (Pressure.temp X.x) X.V=∅
    rw [←present]
    change (roster (LocalLTE.Fan.arm (S:=S) v)).flags=∅
    rw [LocalLTE.Fan.Field.rosterD]
  have regular:Healthy (Pressure.temp s) (H.unionP (LocalLTE.Fan.arm v)) X.V:=by
    change Disjoint _ (RG.flags (Pressure.temp s) (1:Config G c))
    rw [emptyFlags]; exact Finset.disjoint_empty_right _
  have P:=Mayer.physical_plan (X:=X) u hs hw N law room allow f' cohort regular rfl rfl rfl present
  apply integral_congr_ae
  filter_upwards with z
  have atOne:=WilsonCoherentMayerClear.at_one run d
    (Greenbelt.prism T s χ o.K (1:Config G c) (Greenbelt.allot i)) rfl v tag θ y loc β z
  have E:=congrArg (PowerSeries.coeff e)
    ((WilsonCoherentMayerField.received run d θ y loc X β z).2.trans atOne)
  rw [ps_at] at E
  exact congrArg₂ (·*·) (congrFun P z) (congrArg phase E)

end YM.Integration.WilsonCoherentMayerHearing
