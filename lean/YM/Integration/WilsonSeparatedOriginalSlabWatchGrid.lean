import YM.Integration.WilsonSeparatedOriginalSlabRiemannExchange
import YM.Integration.WilsonSeparatedOriginalSlabWatchPlacement
import YM.Integration.WilsonSeparatedOriginalSlabWatchDensity

/-! The physical same-field moment with a fixed external detector converges inside the original common signed centre integral. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabWatchGrid
open Function Set Filter MeasureTheory Analysis Wilson Lattice RG Source Extra.Histories Extraction Spec Cells OPE OPE.Orbits RG17
open Next.UVStress RG05Readout.Native RG05Readout.Pulse WilsonSeparatedOriginalSlabPhysicalBox WilsonSeparatedOriginalSlabWatchCorners WilsonSeparatedOriginalSlabWatchSupport WilsonSeparatedOriginalSlabWatchDensity WilsonSeparatedOriginalSlabRiemann
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}{F:Final C f S}{I:Type}[Fintype I]

def sites {T:Type*} (z:Fin (Fintype.card I)→T):I→T:=fun i=>z ((runNames I).symm i)

def book (L:Layout F)(W:Watch C)(s:I→ℕ)(r:ℝ)(w:(i:I)→C.label (s i))(p:ℕ×ℕ)(x:I→Site (C.side p.1 p.2)):ℂ:=
  moment (C.beta p.1 p.2) (fun U=>(∏i,C.O p.1 p.2 (atRef L (s i) r p (w i)) (x i) U)*W.plot p.1 p.2 U)

theorem records (N per:ℕ)(X:Cloud I→ℂ)(Z:(I→Site (C.side N per))→ℂ):
    (∑x:I→Site (C.side N per),X (C.S.place ∘ x)*Z x)=
      ∑v:Var C.S (Fintype.card I) N per,X (native (centre C.S v))*Z (sites v):=by
  let e:(I→Site (C.side N per))≃Var C.S (Fintype.card I) N per:= {
    toFun:=fun x=>x ∘ runNames I
    invFun:=sites
    left_inv:=fun x=>funext fun i=>congrArg x ((runNames I).apply_symm_apply i)
    right_inv:=fun x=>funext fun i=>congrArg x ((runNames I).symm_apply_apply i) }
  refine Fintype.sum_equiv e _ _ fun x=>?_
  have same:sites (e x)=x:=e.left_inv x
  have pos:native (centre C.S (e x))=C.S.place ∘sites (e x):=rfl
  rw [pos,same]

theorem observed (L:Layout F)(W:Watch C)(s:I→ℕ)(E:OPE.Services C f S){l:Filter (ℕ×ℕ)}[l.NeBot](law:l≤f.fuse)(lens:l≤L.lens)
    (k:ℕ){r:ℝ}(rp:0<r)(w:(i:I)→C.label (s i))(openRef:∀i,C.ref (s i)≤L.level r)(Ψ:Wave I)(g:Body)(A:Set (Cloud I))
    (hA:IsCompact A)(enc:tsupport Ψ.val⊆A)(sep:band W k r A⊆conf _):
    Tendsto (fun p:ℕ×ℕ=>(C.S.a p.1:ℂ)^(4*Fintype.card I)*∑x:I→Site (C.side p.1 p.2),row C k r Ψ g (C.S.place ∘ x)*book L W s r w p x) l
      (𝓝 (∫x:Points (Fintype.card I),test C k r Ψ g x*signal L W s r w x)):=by
  simp_rw [records (C:=C) _ _ (row C k r Ψ g)]
  apply WilsonSeparatedOriginalSlabRiemannExchange.observed C.S f law (test C k r Ψ g) (signal L W s r w) (joint C k r Ψ g) (finite k rp Ψ g A hA enc) (WilsonSeparatedOriginalSlabWatchDensity.measured L W s k rp w Ψ g A hA enc sep) (fun p x=>book L W s r w p (sites x))
  intro δ dp
  have price:=WilsonSeparatedOriginalSlabWatchCorners.uniform L W s E law lens r w openRef (band W k r A) (WilsonSeparatedOriginalSlabWatchSupport.compact W k r A hA) sep dp
  filter_upwards [price,(WilsonSeparatedOriginalSlabWatchPlacement.chart (f:=f) (I:=I) W).filter_mono law] with p paid loc
  intro x live
  have nz:row C k r Ψ g (C.S.place ∘sites x)≠0:=live
  have sits:=registered W k rp Ψ g _ A enc nz
  have bill:=paid (sites x) ((loc _).symm ▸ sits)
  rw [loc] at bill
  exact bill.le

end YM.Integration.WilsonSeparatedOriginalSlabWatchGrid
