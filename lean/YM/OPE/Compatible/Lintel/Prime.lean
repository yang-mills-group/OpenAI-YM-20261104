import YM.OPE.Compatible.Lintel.Atom
/-! # Pilot kinetic crossing -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Work.F05
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J Y Z:Type}{G:Gauge}{n m c f:Side}{S:StepData c f}{p q:Clip}{R T:PathData G} {P:Patch}{K:KernelChoices}{V:ChartRatio G} {i j t r:ℕ} {s s' u α T₁ T₂ b b' d U ℓ:ℝ}
namespace Script
open Page Virgin
lemma folk_vol (H:Boxes G P K)(p:Clip)(R:PathData G)(hz:R.Bounds p s u b)(m:ℕ):folk (raft H.main (voteV P K R p m)):=folkT H.rocket2 (folkS (penne_unit R p P K hz m) _)
namespace Boxes
variable (B:Boxes G P K)
abbrev T3 (R:PathData G)(p:Clip):= raft B.main (voteV P K R p 3)
abbrev Fly (R:PathData G)(p:Clip): Script (Tile G P.L) 4:= cotton (ROOT B.dot) (voteV P K R p 3) (voteV P K R p 3)
abbrev Om (R:PathData G)(p:Clip):= voteV P K R p 4+(-3:ℝ)• B.Fly R p
def T4 (R:PathData G)(p:Clip):= raft B.main (B.Om R p)
lemma folk_fly (h:R.Bounds p s u b):folk (B.Fly R p):=by
   have hh:= folkS (p:=Penna P K R p 3) (penne_unit R p P K h 3) ((3:ℕ).factorial:ℝ); exact folk_cot (root_cash B.dot B.rocket1) hh hh
lemma folk_om (h:R.Bounds p s u b):folk (B.Om R p):= folkF (folkS (penne_unit R p P K h 4) _) (folkS (B.folk_fly h) _)
end Boxes
section
variable (S) (hr: Odd S.ratio.count.val) (X:Boxes G S.patch S.kernel)
local notation "F"=> forest S.ratio hr
variable {A:Bed}{L:Matrix (Body 1 f) (Body 1 c) ℝ}{g: Bid.Dir G c→AxisChart G (forest S.ratio hr)}(h:licensed S hr X p R L A g)(hp:R.Bounds p s u b)(hb: T.Bounds q s' U b')(hx:ClassicalMatch (forest S.ratio hr) p q R T g)
include h hp hb hx X
lemma lesson3 (t:S.Choices)(v:deck (Shade G) c): narrate c (inkV T q 3) v=narrate c (X.T3 R p) v:=by
    obtain ⟨x,rfl⟩:= (spool G c).surjective v; let V:= pane F t p R; let P:= dance S hr G; let w:=fieldT (cabin g) x
    let Y:= X.main; let Q:= voteV S.patch S.kernel R p 3; have hQ:folk Q:=folkS (penne_unit R p S.patch S.kernel hp 3) _; have hh:=dawn S hr X t h hp; let z:=spool G c x; have hz:Y.acts c *ᵥ z=P w:= (bounty S hr X t h x).symm -- ambiguity
    calc
      _= library c (inkV T q 3) (spool G c∘![x,x,x]):= congr_arg (library _ _) (funext fun i=>by fin_cases i <;> rfl)
      _= _:= (inkSongs T q c 3 0 hb).2.2 ![x,x,x]
      _= _:= (marchX t h.2.1 hx x).1
      _= library c Q (P ∘ ![w,w,w]):=(vote_here S hr h.1.cover t p R hp 3 ![w,w,w]).symm
      _= _:=by symm; unfold Boxes.T3 narrate; rw [raftReads _ X.rocket2 _ (folk_whole hQ)]; exact congr_arg (library c Q) (funext fun i=>by fin_cases i <;> exact hz)
lemma lesson4 (t:S.Choices)(v:deck (Shade G) c): narrate c (inkV T q 4) v=narrate c (X.T4 R p) v:=by
    obtain ⟨x,rfl⟩:= (spool G c).surjective v; let V:= pane F t p R; let P:= dance S hr G; let w:=fieldT (cabin g) x; let u' := fieldU (cabin g) x x
    let Y:= X.main; let Q:= voteV S.patch S.kernel R p 4; have hQ:folk Q:=folkS (penne_unit R p S.patch S.kernel hp 4) _; have HH:=dawn S hr X t h hp; let z:=spool G c x; have hz:Y.acts c *ᵥ z=P w:= (bounty S hr X t h x).symm
    have hb : -library c (X.Fly R p) (P ∘ ![w,w,w,w])=iteratedFDeriv ℝ 3 V 0 ![u',w,w]:= by erw [show P ∘ ![w,w,w,w]=![P w,P w,P w,P w] from funext fun i=>by fin_cases i <;>rfl]; exact HH.cots x w w X.rocket1 (folk_whole (folkS (penne_unit R p S.patch S.kernel hp 3) _))
    calc
      _= library c (inkV T q 4) (spool G c ∘![x,x,x,x]):= congr_arg (library _ _) (funext fun i=>by fin_cases i <;> rfl)
      _= _:= (inkSongs T q c 4 0 ‹T.Bounds q s' U b'›).2.2 ![x,x,x,x]
      _= _:= (marchX t h.2.1 hx x).2
      _= library c (X.Om R p) (P ∘![w,w,w,w]):= by
          symm; erw [show library c (X.Om R p) _ = _ from libAdd Q ((-3:ℝ) • X.Fly R p) (folk_whole hQ) (folk_whole (folkS (X.folk_fly hp) _)) (P ∘ ![w,w,w,w]),libScale (X.Fly R p) (P ∘ ![w,w,w,w]), vote_here S hr h.1.cover t p R hp 4 ![w,w,w,w]]; apply congr_arg; change (-3:ℝ)*_=3*iteratedFDeriv ℝ 3 V 0 ![u',w,w]; erw [← hb]; ring
      _= _:=by symm; unfold Boxes.T4 narrate; erw [raftReads _ X.rocket2 _ (folk_whole (X.folk_om hp))]; exact congr_arg (library c _) (funext fun i=>by fin_cases i<;> exact hz)
end
end Script
end YM.OPE.Flume
