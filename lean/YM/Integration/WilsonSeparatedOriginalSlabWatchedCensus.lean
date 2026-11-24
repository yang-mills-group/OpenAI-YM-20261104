import YM.Integration.WilsonSeparatedOriginalSlabPhysicalBox
import YM.Integration.WilsonMacroscopicRichWatchLaw

/-! Fixed macroscopic exterior marks multiply the actual whole signed ultraviolet input on the same Wilson configuration. The relative test keeps its genuine common centre. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabWatchedCensus
open Function Set Filter MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Extraction Spec RG12 RG17
open Push Local RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Pulse RG05Readout.Records
open Next.UVStress WilsonReportingTerminalPrimaryStencil WilsonSeparatedOriginalSlabPhysicalBox
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {C:Family G} {I:Type}[Fintype I][DecidableEq I] {N per k:ℕ}

omit [DecidableEq I] in
def word (s:I→ℕ)(v:(i:I)→C.label (s i))(x:I→Site (C.side N per)):C(Config G (C.side N per),ℂ):=
  ⟨fun U=>∏i,C.O N per (v i) (x i) U,continuous_finsetProd _ (fun i _=>C.continuousO N per (s i) (v i) (x i))⟩

theorem tested (h:C.Makes)(W:Watch C)(s:I→ℕ)(v:(i:I)→C.label (s i)) (r:ℝ)(Ψ:Wave I)(top:k≤N){cap:ℝ}
    (rp:0<r)(enclosed:∀x∈tsupport Ψ.val,∀i,‖x i‖≤cap)(room:r*cap+2*C.S.a k<C.S.radius per)(m:ℕ)(g:Body):
    moment (C.beta N per) (fun U=>constellation s (fun i=>upper (N:=N) (per:=per) (v i)) r Ψ top m g U*W.plot N per U) =
      ∑x:I→Site (C.side N per), (weight (C:=C) s m N r * row C k r Ψ g (C.S.place ∘ x)) * moment (C.beta N per) (fun U=>(∏i,C.O N per (v i) (x i) U)*W.plot N per U):=by
  let a (x:I→Site (C.side N per)):=weight (C:=C) s m N r * row C k r Ψ g (C.S.place ∘ x)
  let Y:=∑x:I→Site (C.side N per), a x • word s v x
  calc _=WilsonMacroscopicRichWatchLaw.meter C W Y:=by
          rw [WilsonMacroscopicRichWatchLaw.same];apply congrArg;funext U
          rw [returned h s v r Ψ top rp enclosed room m g U];congr 1
          simp [Y,word,a]
    _= _ :=by simp only [Y,map_sum,map_smul,smul_eq_mul,WilsonMacroscopicRichWatchLaw.same];rfl

open WilsonReportHarvestReadmittedSource

theorem issued {f:Extraction.Order}{S:Table C.book}{F:Final C f S}(L:Layout F)(h:C.Makes)(W:Watch C)(s:I→ℕ)(r:ℝ)
    (w:(i:I)→C.label (s i))(U:(i:I)→Emblems C (s i))(m:ℕ)(mn:m≤N)(Ψ:Wave I)(top:k≤N){cap:ℝ}(rp:0<r)
    (enclosed:∀x∈tsupport Ψ.val,∀i,‖x i‖≤cap)(room:r*cap+2*C.S.a k<C.S.radius per)(g:Body):
    moment (C.beta N per) (fun V=>constellation s (fun i=>Many.point (U i) (filed L (s i) r (w i) (U i) m N per) m N) r Ψ top m g V*W.plot N per V) =
      ∑x:I→Site (C.side N per), (weight (C:=C) s m N r * row C k r Ψ g (C.S.place ∘ x)) * moment (C.beta N per) (fun V=>(∏i,C.O N per (atRef L (s i) r (N,per) (w i)) (x i) V)*W.plot N per V):=by
  simp_rw [carried L _ r _ _ m N per mn]
  exact tested h W s (fun i=>atRef L (s i) r (N,per) (w i)) r Ψ top rp enclosed room m g

end YM.Integration.WilsonSeparatedOriginalSlabWatchedCensus
