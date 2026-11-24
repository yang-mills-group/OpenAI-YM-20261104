import YM.Integration.WilsonSeparatedOriginalSlabLabelCorners
import YM.Integration.WilsonSeparatedOriginalSlabWatchedCensus

/-! The same fixed exterior detector and all independently sampled filed near coordinates on the original extraction. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabWatchCorners
open Finset Function Filter Set MeasureTheory Analysis Wilson Lattice RG Source Extra.Histories Extraction Spec Cells OPE.Cards
open MergeProof MergeProof.Accent MergeProof.Ribbons Trace.Physical Trace.Physical.GermGraph
open Overlay Work.G08 Bid Next.Rank Next.UVStress Price OPE OPE.Orbits RG12 RG17
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book} {I:Type} [Fintype I]
variable {F:Final C f S} (L:Layout F)(W:Watch C)(s:I→ℕ)

abbrev Arms:=I⊕Fin W.n

def grade : Arms (I:=I) W → ℕ :=Sum.elim s (fun i=>(W.q i).1)

def placed (N per:ℕ)(x:I→Site (C.side N per)):Arms (I:=I) W → Site (C.side N per):=Sum.elim x (W.among N per)

def measured (r:ℝ)(w:(i:I)→C.label (s i))(k:ℕ×ℕ):(a:Arms (I:=I) W)→C.label (grade W s a)
  | .inl i=>atRef L (s i) r k (w i)
  | .inr i=>(W.q i).2

def fixed (r:ℝ)(w:(i:I)→C.label (s i)):(a:Arms (I:=I) W)→C.label (grade W s a)
  | .inl i=>locatedRef L (s i) r (w i)
  | .inr i=>(W.q i).2

def corners (N per:ℕ)(x:I→Site (C.side N per)):=tag (C.S.a N) (lift ∘ placed W N per x ∘ runNames (Arms (I:=I) W))

theorem exact (r:ℝ)(w:(i:I)→C.label (s i))(N per:ℕ)(x:I→Site (C.side N per)):
    C.ensemble (grade W s ∘ runNames _) (placed W N per x ∘ runNames _)
      (fun i=>measured L W s r w (N,per) (runNames _ i))=
    moment (C.beta N per) (fun U=>(∏i,C.O N per (atRef L (s i) r (N,per) (w i)) (x i) U)*W.plot N per U):=by
  apply congrArg (Wilson.moment (C.beta N per));funext U
  let Q(a:Arms (I:=I) W):=C.O N per (measured L W s r w (N,per) a) (placed W N per x a) U
  exact (Equiv.prod_comp (runNames _) Q).trans (Fintype.prod_sum_type Q)

theorem uniform (E:Services C f S){l:Filter (ℕ×ℕ)}[l.NeBot](law:l≤f.fuse)(lens:l≤L.lens)
    (r:ℝ)(w:(i:I)→C.label (s i))(openRef:∀i,C.ref (s i)≤L.level r)
    (K:Set (Points (Fintype.card (Arms (I:=I) W))))(compact:IsCompact K)(separated:K⊆conf _){ε:ℝ}(ep:0<ε):
    ∀ᶠ k:ℕ×ℕ in l,∀x:I→Site (C.side k.1 k.2),corners W k.1 k.2 x∈K →
      ‖moment (C.beta k.1 k.2) (fun U=>(∏i,C.O k.1 k.2 (atRef L (s i) r k (w i)) (x i) U)*W.plot k.1 k.2 U) -
        S.value (grade W s ∘ runNames _) (corners W k.1 k.2 x) (fun i=>fixed L W s r w (runNames _ i))‖<ε:=by
  have varies (a:Arms (I:=I) W):Tendsto (fun k=>measured L W s r w k a) l (𝓝 (fixed L W s r w a)):=by
    cases a with
    | inl i=>exact RG17.tendsRef L lens tendsto_const_nhds (openRef i)
    | inr i=>exact tendsto_const_nhds
  have passed:=WilsonSeparatedOriginalSlabLabelCorners.uniform F E K compact separated (grade W s ∘ runNames _)
    (fun i=>fixed L W s r w (runNames _ i)) (fun k i=>measured L W s r w k (runNames _ i)) law (fun i=>varies _) ep
  filter_upwards [passed] with k current
  intro x hx
  have obs:=current (lift ∘ placed W k.1 k.2 x ∘ runNames _) hx
  have grid:wrap (C.side k.1 k.2) ∘ (lift ∘ placed W k.1 k.2 x ∘ runNames _)=placed W k.1 k.2 x ∘ runNames _:=funext fun _=>wrap_lift _
  rw [grid,exact L W s r w] at obs;exact obs

omit [Fintype I] in
theorem projected (r:ℝ)(w:(i:I)→C.label (s i))(i:I):S.project (s i) (fixed L W s r w (.inl i))=master L (s i) r (w i):=RG17.payRef L _

end YM.Integration.WilsonSeparatedOriginalSlabWatchCorners
