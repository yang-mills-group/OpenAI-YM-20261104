import YM.Integration.WilsonMeasuredRankedGerm

/-! Hear the complete signed regular return and its kinetic reversion at one
original address. Their full log budgets add before the physical projection. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredRankedLampPair
open Filter Function Finset Lattice RG Wilson Source Labels Push.Local Extra.Histories
open ProjectorNext.Equivariance Trace.Physical Trace.Physical.Germ QuadraticLocal Marker RG3.Forms RG3.Primary
open scoped Classical Topology BigOperators
variable {G : Gauge} {n : Side} {V T ι I : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    [Nonempty T] [Countable ι] [Countable I] {B : Census V} {o u : V → Site n} {W : Rep G n}
    {d : ℕ} {F : Frame G d}

theorem original (L : Gallery T ι o W B) (D : Lamps T I G W.p u B) (roots:o=u)
    {θ : V→ℝ} {κ regular lower hard budget : ℝ}
    (hw:∀v,0<θ v) (divisor:0<κ) (valid:W.activities.ForcedFamily W.p)
    (soft:L.E.Paid θ W.p.B (W.p.supportExponent+2) regular)
    (filed:D.Paid θ W.p.B (W.p.supportExponent+2) lower)
    (force:L.K.Paid θ W.p.B W.p.supportExponent hard)
    (x:T) (v:V) (Y:Hol G) (S:SectionData F) {μ:ℝ} (he:Readable Y S W.p n μ)
    (hu:∀ z∈S.stencil,∀ i:Axis,20*((z i).natAbs+1)≤n.val)
    (hd:d≤W.p.order) (hp:d≤W.p.power) (hs:∀ t,HasOrderAt (S.places t (o v)) 1 d)
    (A:Coefficient F n) (shape:A.Format (o v) Y W) (price:A.remBound (o v) W κ budget)
    (signed:A.density (o v) S W =ᶠ[𝓝 1] fun U=>(W.eval U:ℂ)*
      ((L.E.log x U).part (B.fire v)+(D.log x U).part (B.fire v))) :
    let r:=4*(regular+lower)
    let s:=(factor Y S W.p.supportExponent μ*(W.p.order.factorial:ℝ))*r
    let c:=(W.p.order.factorial:ℝ)*r+s+θ v*W.p.mass (S.footprint (o v)) (μ*(s/θ v))
    F.coeffSize A.x ≤ 2*(r+s)/θ v + WilsonMeasuredRankedGerm.wrapCost F Y *
      wraps W.p n*(budget+c/θ v) := by
  cases roots
  let pair:Gallery T (ι⊕I) o W B:=⟨L.E.join D,L.K⟩
  have validPair:=Lamps.joinPaid soft filed
  apply WilsonMeasuredRankedGerm.regular pair hw divisor valid validPair force x v Y S he hu hd hp hs A shape price
  refine signed.trans (EventuallyEq.of_eq (funext (fun U=>?_)))
  have width:0≤W.p.supportExponent+2:=by linarith only [W.p.exponent_pos]
  have sum:=Lamps.joinLog (L:=L.E) (A:=D) x U (soft.sums width hw x U) (filed.sums width hw x U)
  exact (congrArg (fun z : Poly B=>(W.eval U:ℂ)*z.part (B.fire v)) sum).symm

end YM.Integration.WilsonMeasuredRankedLampPair
