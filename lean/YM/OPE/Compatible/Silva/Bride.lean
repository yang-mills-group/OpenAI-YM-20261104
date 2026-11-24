import YM.OPE.Compatible.Lintel.Paine
import YM.Progress.JOINT_CALENDAR.Germs
/-!
# Recover exact second height on arbitrary (testable) wrap. Lift
this using projectT.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Work.F05 Votive
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J Y Z:Type}{G:Gauge}{n m c f:Side}{S:StepData c f}{p q:Clip}{R T:PathData G} {P:Patch}{K:KernelChoices}{V:ChartRatio G} {i j t r:ℕ} {s s' u α l l':ℝ}
namespace Script
open Virgin Page
variable {B:Sponsor G}{H:Seasons B}
abbrev ReadyV (S:StepData c f) (he:Odd S.ratio.count.val)(x:Boxes G S.patch S.kernel)(A:Alps B H i l)(D: Alps B H j l')(W:Matrix (Body 1 f) (Body 1 c) ℝ)(g: Bid.Dir G c→AxisChart G (forest S.ratio he)):= licensed S he x A.clip A.live W A.sky g∧ Bid.HeatG (forest S.ratio he) A.clip A.live g D.sky
lemma testimony (P:Flight i j)(B:Sponsor G)(Q:Seasons B)(E:Alps B Q i l)(D:Alps B Q j l')(he:E.gear=P.wing)(hd:D.gear=P.land)(h:Mag i j)(X:Medal P.patch G B.K i)(ha:f.val=c.val * P.L.val)(hs: Bid.Larger (G:=G) (P.visit (f:=f) (c:=c) B.K ha)):
    let y:= P.visit (f:=f) (c:=c) B.K ha
    let T:= P.duo B.K.penalty
    ∃ g, ReadyV y P.odd (⟨i,h.1,X,E.gear⟩:Boxes G P.patch B.K) E D (installed y.ratio T.A0) g:=by
        intro S T
        have hB:= E.active; have hv:=D.active; let F:=forest S.ratio P.odd; have hz: Defined B.K.penalty (B.l i) P.wing E.sky:= he ▸ hB.2.1; have hf:Defined B.K.penalty (B.l j) P.land D.sky:= hd ▸ hv.2.1; have hh:Towers.Diagonal S E.sky D.sky T := Next.Free.diagonal B.K _ _ (B.h.net _) (B.h.net _) P h.2.1 E.sky D.sky hz hf ha
        obtain ⟨b,hb,H⟩:=(Bid.cospons Work.E02.answer Work.F01.answer Work.F02.answer Work.F03.answer Work.F04.answer P.L i B.K (B.X.η i) (B.X.eta_pos _) (G:=G)).χ; have hp:= hB.2.2.2.1 f; have hK:= hB.2.2.2.2 f
        obtain ⟨-,g,hs1,hh1,hk1⟩:=H _ _ S rfl rfl rfl hs F E.sky D.sky _ _ E.live _ _ _ _ _ _ T hh hp E.pays E.fills hK (hv.2.2.2.1 c)
        refine ⟨g,⟨⟨hs.1,?_,?_⟩,hs1,hh1,(Work.F03.answer G _ _ S hs F E.sky _ E.live _ _ _ _ _ hp E.pays E.fills hK (Work.F02.answer G _ _ _ _ _ E.pays)).2⟩,hk1⟩
        · have hf : Precision.K (E.sky.metric.acts f)=Precision.K ((pink B.K.penalty P.wing).acts f):= by unfold Precision.K; rw [hz.metric,Matrix.mul_assoc,Matrix.mul_assoc]; rw [(obligations B.K.penalty (B.l i) B.K.penalty_pos (B.h.net _) h.1 P.wing f).2.2.1]
          change treeMatrix G S F E.sky.metric=treeMatrix G S F (pink B.K.penalty E.gear); rw [he]; apply congr_arg (fun X : Matrix _ _ ℝ=> (tensor G X).submatrix (plant F) (plant F)); exact congr_arg (fun x: Matrix _ _ ℝ=> x+ _ ) hf
        change installed S.ratio (X.highCross E.gear)=_; rw [he]; exact X.trueMean S _ P.wing hs P.legal (Flight.tangent P B.K h.2.1 (c:=c) (f:=f) ha).1
variable (S) (hr:Odd S.ratio.count.val) (X:Boxes G S.patch S.kernel)
local notation "F"=>forest S.ratio hr
lemma TipL (A:Alps B H i l)(D:Alps B H j l'){W: Matrix (Body 1 f) (Body 1 c) ℝ}{g: Bid.Dir G c→AxisChart G F}(h:ReadyV S hr X A D W g)(t:S.Choices)(x y:Bid.Dir G c): iteratedFDeriv ℝ 2 (swornV D.clip D.live (n:=c)) 0 ![x,y]= iteratedFDeriv ℝ 2 (pane F t A.clip A.live) 0 ![fieldT (cabin g) x,fieldT (cabin g) y]:=by
   have he := Progress.Joint.tested_second A.sky h.1.2.1 h.1.2.2.2 D.sky h.2 (D.active.2.2.2.1 c) D.pays D.fills (D.active.2.2.2.2 c) t 2 (by decide); let Y:=cabin g; let T:=pane F t A.clip A.live; have hs:Stayed T Y:= viewer t h.1.2.1; have hx := (crit_home h.1.2.1).eventually (scoreS F t A.clip A.live); have hy:(fun i=>tested F t A.clip A.live i (g i))=ᶠ[𝓝 0] T ∘ viewS Y:=hx
   change iteratedFDeriv ℝ 2 (fun x=>mainTerm _ _ (represent x)) 0 _=_; rw [← he.2.2, (hy.iteratedFDeriv ℝ 2).eq_of_nhds, pay_second (by rw [hs.H0]; exact hs.origin) hs.hl,hs.H0,show iteratedFDeriv ℝ 2 (viewS Y) 0 ![x,y]=_ from hs.lower x y]; have hp:= hs.margin.self_of_nhds;rw [hs.H0] at hp; rw [hp]; exact zero_add _
end Script
end YM.OPE.Flume
