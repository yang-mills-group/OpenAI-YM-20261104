import YM.Integration.WilsonPhysicalPositionTwoHomeObservable

/-! A leading frame has scale-by-scale freedom inside a finite set of leading choices.
The actual directed cocycle keeps the two dated chart changes separately. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceDatedGauge
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS Maxwell Maxwell.Free Spin
open scoped Classical BigOperators Topology
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}

def elected {I:Type*}(frames:I→ℝ→tower S)(atScale:ℝ→I)(r:ℝ):tower S:=frames (atScale r) r

theorem leading (F:Final C f S){I:Type*}[Finite I](frames:I→ℝ→tower S)(admitted:∀i,Leading F (frames i))
    (atScale:ℝ→I):Leading F (elected frames atScale):=by
  classical
  refine ⟨?_,?_,?_,?_⟩
  · intro d
    have all:=Filter.eventually_all.mpr (fun i=>(admitted i).equivariant d)
    exact all.mono fun r h=>h (atScale r)
  · intro d e de
    have all:=Filter.eventually_all.mpr (fun i=>(admitted i).raised de)
    exact all.mono fun r h=>h (atScale r)
  · intro d
    have all:=Filter.eventually_all.mpr (fun i=>(admitted i).unit d)
    exact all.mono fun r h=>h (atScale r)
  · intro n d v j K compact clear
    rw [Metric.tendstoUniformlyOn_iff]
    intro δ positive
    have all:=Filter.eventually_all.mpr (fun i=>Metric.tendstoUniformlyOn_iff.mp
      ((admitted i).lead n d v j K compact clear) δ positive)
    exact all.mono fun r h=>h (atScale r)

def coordinates (J:ℝ→tower S){d:ℕ}(r:ℝ)(home:change S d):=(J r d).trans home.symm

theorem reported (J:ℝ→tower S){d:ℕ}(outer inner:change S d)(r t:ℝ)(positive:0<t)
    (v:(Bel C.book).Field d):
    Frame.cocycle d J r t positive v=(Pert.Scale.gearIso C.labels d t positive).symm
      ((coordinates J r outer).symm ((inner.trans outer.symm) (coordinates J (t*r) inner v))):=by
  simp [Frame.cocycle,coordinates]

end YM.Integration.WilsonMeasuredPublicEntranceDatedGauge
end
