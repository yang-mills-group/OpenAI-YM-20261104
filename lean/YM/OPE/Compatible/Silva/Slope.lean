import YM.OPE.Compatible.Silva.Bride
/-! # Pilot kinetic crossing -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Work.F05
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J Y Z:Type}{G:Gauge}{n m c f:Side}{S:StepData c f}{p q:Clip}{R T:PathData G} {P:Patch}{K:KernelChoices}{V:ChartRatio G} {i j t r:ℕ} {s s' u α T₁ T₂ b b' d U ℓ:ℝ}
namespace Script
open Page Virgin
variable (S) (hr: Odd S.ratio.count.val) (X:Boxes G S.patch S.kernel)
local notation "F"=> forest S.ratio hr
variable {A:Bed}{L:Matrix (Body 1 f) (Body 1 c) ℝ}{g: Bid.Dir G c→AxisChart G (forest S.ratio hr)}(h:licensed S hr X p R L A g)(hp:R.Bounds p s u b)(hb: T.Bounds q s' U b')(hc:TEX X p q R T α V)
include h hp hb hc X
lemma Teach3 (t:S.Choices)(x:Bid.Dir G c):iteratedFDeriv ℝ 3 (swornV q T) 0 ![x,x,x]=iteratedFDeriv ℝ 3 (pane F t p R) 0 ![fieldT (cabin g) x,fieldT (cabin g) x,fieldT (cabin g) x]:=by
    let U:=pane F t p R; let P:= dance S hr G; let w:=fieldT (cabin g) x
    let Y:= X.main; let Q:= voteV S.patch S.kernel R p 3; have hQ:folk Q:=folkS (penne_unit R p S.patch S.kernel hp 3) _; have hh:=dawn S hr X t h hp; let z:=spool G c x; have hz:Y.acts c *ᵥ z=P w:= (bounty S hr X t h x).symm -- ambiguity
    calc
      _= _:= (inkSongs T q c 3 0 hb).2.2 _ |>.symm
      _= narrate c (inkV T q 3) z:= congr_arg (library _ _) (funext fun i=>by fin_cases i <;>rfl)
      _= narrate c (X.T3 R p) z := by rw [hc.1,regaled _ (folk_whole (folk_vol X p R hp 3))]
      _= library c Q (P ∘ ![w,w,w]):= by unfold Boxes.T3 narrate; rw [raftReads _ X.rocket2 _ (folk_whole hQ)]; exact congr_arg (library c Q) (funext fun i=>by fin_cases i<;>exact hz)
      _=_:=vote_here S hr h.1.cover t p R hp 3 ![w,w,w]
lemma Teach4 (t:S.Choices)(x:Bid.Dir G c):iteratedFDeriv ℝ 4 (swornV q T) 0 ![x,x,x,x]=iteratedFDeriv ℝ 4 (pane F t p R) 0 ![fieldT (cabin g) x,fieldT (cabin g) x,fieldT (cabin g) x,fieldT (cabin g) x]+3*iteratedFDeriv ℝ 3 (pane F t p R) 0 ![fieldU (cabin g) x x,fieldT (cabin g) x,fieldT (cabin g) x]:=by
    let V:=pane F t p R; let P:= dance S hr G; let w:=fieldT (cabin g) x; let u':= fieldU (cabin g) x x
    let Y:= X.main; let Q:= voteV S.patch S.kernel R p 4; have hQ:folk Q:=folkS (penne_unit R p S.patch S.kernel hp 4) _; have HH:=dawn S hr X t h hp; let z:=spool G c x; have hz:Y.acts c *ᵥ z=P w:= (bounty S hr X t h x).symm
    have hy : -library c (X.Fly R p) (P ∘ ![w,w,w,w])=iteratedFDeriv ℝ 3 V 0 ![u',w,w]:= by erw [show P ∘ ![w,w,w,w]=![P w,P w,P w,P w] from funext fun i=>by fin_cases i <;>rfl]; exact HH.cots x w w X.rocket1 (folk_whole (folkS (penne_unit R p S.patch S.kernel hp 3) _))
    calc
      _= _:= (inkSongs T q c 4 0 hb).2.2 _ |>.symm
      _= narrate c (inkV T q 4) z:= congr_arg (library _ _) (funext fun i=>by fin_cases i<;>rfl)
      _= narrate c (X.T4 R p) z:= by rw [hc.2.1,regaled (X.T4 R p) (folk_whole (folkT X.rocket2 (X.folk_om hp)))]
      _= library c (X.Om R p) (P ∘![w,w,w,w]):= by unfold Boxes.T4 narrate; erw [raftReads _ X.rocket2 _ (folk_whole (X.folk_om hp))]; exact congr_arg (library c _) (funext fun i=>by fin_cases i<;> exact hz)
      _= _:= by
          erw [show library c (X.Om R p) _ = _ from libAdd Q ((-3:ℝ) • X.Fly R p) (folk_whole hQ) (folk_whole (folkS (X.folk_fly hp) _)) (P ∘ ![w,w,w,w]),libScale (X.Fly R p) (P ∘ ![w,w,w,w]), vote_here S hr h.1.cover t p R hp 4 ![w,w,w,w]]; apply congr_arg; change (-3:ℝ)*_=3*iteratedFDeriv ℝ 3 V 0 ![u',w,w]; erw [← hy]; ring
omit hp hb hc
lemma teach (t:S.Choices)(he:R.Bounds p s u b)(hp: LocalRatio V)(v:Bid.Dir G c):
    let A:= pane F t p R
    let w:=fieldT (cabin g) v
    let u':=fieldU (cabin g) v v
    X.silo R p V c ![spool G c v, spool G c v]=iteratedFDeriv ℝ 2 (springF F R) 0 ![w.2, w.2]+heatPay A (countingBasis F G) (FUND S hr X)⁻¹ w w u'-iteratedFDeriv ℝ 2 (taxY F V) 0 ![w.2,w.2]:=by
    let A:=pane F t p R; let D:=cabin g; let M:=FUND S hr X; let K:= countingBasis F G; have hM:=ulk_force S hr X; let P:= dance S hr G; let w:=fieldT D v; let u':=fieldU D v v; have hh:=dawn S hr X t h he; have ht:(M⁻¹).IsSymm:=by have he := hM.inv.isHermitian.eq; simpa only [Matrix.IsSymm, Matrix.conjTranspose_eq_transpose_of_trivial] using he
    have hf: tuneH X.dot (voteV S.patch S.kernel R p 3) (voteV S.patch S.kernel R p 4) c ![P w,P w]=heatPay A K M⁻¹ w w u':=by
        let x:=X.dot; let T:= ROOT (I:=Shade G) x; let y:= voteV S.patch S.kernel R p 3; let Y:= voteV S.patch S.kernel R p 4; have hY:Summable y:=folk_whole (folkS (penne_unit R p S.patch S.kernel he 3) _); unfold tuneH
        have ht1: -cityTap (T.acts c) (cotton T y y) ![P w, P w]=(M⁻¹*HATCH A K u').trace:= hh.ringQ v X.rocket1 hY
        have ht2: cityTap (T.acts c) Y ![P w,P w]=(M⁻¹*ROACH A K w w).trace:= hh.lineU (vote_here S hr h.1.cover t p R he 4) w
        have ht3: cityTap (T.acts c) (swing (Equiv.swap (1:Fin 4) 2) (cotton T y y)) ![P w,P w]= _ := hh.tapDouble w X.rocket1 hY ht
        dsimp only; erw [ht1,ht2,ht3]; rfl
    intro A₁ w₁ u₁; unfold Boxes.silo; erw [show (fun i=> X.main.acts c *ᵥ ![spool G c v,spool G c v] i)= ![P w,P w] from funext fun i:Fin 2=>by fin_cases i <;> exact (Script.bounty S hr X t h v).symm]; obtain ⟨hC,hB⟩:=marchY S hr hp he w; unfold Boxes.tuneP; erw [hC, hf,hB]; ring -- maybe change let
end Script
end YM.OPE.Flume
