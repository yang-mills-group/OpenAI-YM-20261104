import YM.OPE.Compatible.Minuet.Pylon
import YM.OPE.Rate
/-!
 # Afresh dynamic powering. Service any filters across one stage, no dependence on previous reps. Truth uses corresponding real x. Patch may also keep Purchase for nominal Step.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard
open AnalyticBridge.VerifiedReset
open Next.Rank.Thirst YM.OPE
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P:Teller G} {D:Patch} {E:ConnectedActivityE6.Target G P} {L:Side} {W a σ C κ v γ t s w:ℝ} {m:ℕ}
structure Model (D:Patch)(P:Teller G)(L:Side) (E:ConnectedActivityE6.Target G P)(o:ConnectedActivityE6.Target.Order G W) (κ C:ℝ)(m:ℕ) where
   (c f: Side)
   V : StepData c f
   T : Tube G V
   R : Rep G f
   x : ℝ
   cash : Cash W x κ L E o C T R
   forest : Forest V.ratio
   sheet : Coat T forest
   g : LogField G c
variable {o:ConnectedActivityE6.Target.Order G W}
namespace Model
variable (A:Model D P L E o κ C m)
structure Ready : Prop where
   height : A.V.patch=D
   stamp : Stamp A.T
   Knows : HasSlots A.R.p A.R.activities
   walk : ∃ a b c:ℝ,Cash.Renewed m a b c A.cash
   moment : A.sheet.x=A.x
   weather : A.sheet.width=o.K
   healthy : RG.flags (Pressure.temp A.x) A.sheet.V=∅
   chart : A.sheet.V=represent A.g
   width : WilsonStartup.Decent A.R.clip A.R.p
   mass U:0≤A.R.eval U
variable {A}
lemma Ready.port (_h:A.Ready):A.V.patch.Branches A.V.kernel G ∧ A.V.patch.L=L∧ A.V.kernel=P.bind := by
    have hx:= A.cash.laws.data.funds -- uses Works?
    have he := A.cash.laws.intake.ready
    exact ⟨funds_branch he,hx.length_eq,he.knobs⟩
lemma Ready.budget (h:A.Ready) : A.R.Lawful P.top.width P.top.paths (loopBill G L A.x) (incomingE G L A.x) (incomingK G L A.x)∧ A.R.p.B=radiusB (betaF G A.x L)∧ A.R.p.threshold=Pressure.fiery G A.x L ∧ A.R.p.supportExponent=P.top.supportExponent∧ A.R.clip=P.top.clip∧ A.R.beta∈ Set.Icc ((betaF G A.x L)/2) (2* betaF G A.x L):=by
    have hx:= A.cash.laws.intake; have hz : A.V.patch.L = L:=h.port.2.1; have hv:=hx.cap; have hp:=hx.window; have he:=hx.sizes; have hf:=hx.received.temp
    rw [hz] at hv he hp; change A.R.p.threshold=fiery G A.x A.V.patch.L at hf; rw [hz] at hf; exact ⟨hv,he,hf,hx.exponent.symm,hx.received.clip.trans hx.ready.high,hp⟩
end Model
variable {ι:Type*} {l:Filter ι} {A:ι→ Model D P L E o κ C m}
def Chase (A:ι→ Model D P L E o κ C m) (l:Filter ι):= D.Branches P.bind G∧ foam E L ∧ 0<E.exp ∧ 0<κ ∧ Tendsto (fun i=>(A i).x) l atTop ∧ ∀ᶠ i in l,(A i).Ready
abbrev echoM (A:ι→ Model D P L E o κ C m) (i) := Delay.bill G L (A i).x
abbrev βM (A:ι→ Model D P L E o κ C m) (i) := betaF G (A i).x L
abbrev fate (A:ι→ Model D P L E o κ C m)(i) := Real.log (βM A i)
def Lite (A:ι→Model D P L E o κ C m) (l:Filter ι){U:Type*}[Norm U] (p:ι→U) := ∃ i:ℕ, ∀ᶠ x in l, ‖p x‖≤ echoM A x ^ i
abbrev Wage (A:ι→ Model D P L E o κ C m) (l:Filter ι){U:Type*}[Norm U] := RateLE l (fate A) (X:=U)
namespace Chase
variable (h: Chase A l)
include h
lemma select_height : Tendsto (fun i=>(A i).x) l atTop:= h.2.2.2.2.1
lemma port:∀ᶠ i in l,(A i).Ready:=h.2.2.2.2.2
lemma high : Tendsto (βM A) l atTop:= (Work.E09.betaF_growth G L).comp h.select_height
lemma tense : Tendsto (fate A) l atTop:= Real.tendsto_log_atTop.comp h.high
lemma echoes:Tendsto (echoM A) l atTop:= (echo_growth G L).comp h.select_height
lemma run {f:ℝ→ℝ}(hx:Rate G L a f): RateLE l (fate A) (fun i=>f (A i).x) a:=by
    intro t ht
    filter_upwards [h.high.eventually_gt_atTop 0,h.select_height.eventually (hx _ ht)] with i hi hk
    rw [show Real.exp (t*fate A i)=βM A i^t from (by rw [Real.rpow_def_of_pos hi,mul_comm])];exact hk
lemma wisdom {t:ℝ}:RateIs l (fate A) (fun i=> βM A i ^ t) t:=by
   refine ⟨(h.high.eventually_gt_atTop 0).mono fun i hi=> Real.rpow_pos_of_pos hi _,?_⟩
   apply tendsto_const_nhds.congr'; filter_upwards [h.high.eventually_gt_atTop 0,h.tense.eventually_gt_atTop 0] with j hj hL
   rw [Real.log_rpow hj]; change _=_*fate A j / _; rw [mul_div_cancel_right₀ _ hL.ne']
lemma finest {F:ι→ℝ}(hp:Lite A l F):RateLE l (fate A) F 0:=by
   obtain ⟨k,hk⟩:=hp; have he:RateLE l (fate A) (fun i=> echoM A i^k) 0:=by simpa only [zero_mul] using h.run (Rate.bill.pow k)
   exact RateLE.of_norm_le he hk
end Chase
end YM.PhysicalNext.Repeat.Aroma
