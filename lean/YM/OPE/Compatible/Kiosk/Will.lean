import YM.OPE.Compatible.Kiosk.Yen
/-! # PhaseH curved loan induction -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Votive
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Work.F05 Flume Flume.Script Frequency
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{n c f L:Side}{P:Patch}{K:KernelChoices}{I J M:Type}{m k r d:ℕ}{σ C s u z:ℝ}{B:Sponsor G} {H:Seasons B}{V:ChartRatio G}{p:Clip}
namespace Alps
open Page Virgin Planned.PrimaryIntegral295.Carrier Boxes Roles
abbrev dayU (r:ℕ)(i:TileC H P p V C):= (UA i).word r
abbrev dayV (r:ℕ)(i:TileC H P p V C):= (VA i).word r
abbrev marksD (r:ℕ)(i:TileC H P p V C):= dayU r i-dayV r i
def flagsH (P:Patch) (q:TileC H P p V C→ Script (Shade G) r) (i:TileC H P p V C):= Alps.display P B (UA i).gear (q i)
def tourP (T:Medal P G B.K P.J)(i:TileC H P p V C):= charmSeal T (UA i).gear
def tourV (T:Medal P G B.K P.J)(i:TileC H P p V C):= charmSeal T (VA i).gear
abbrev Tall (r m:ℕ):Prop:= Wcap H P p V C m (marksD r)
abbrev riseF (T:Medal P G B.K P.J)(r:ℕ)(i:TileC H P p V C):= stitch (player (tourP T i) (dayU r i))-stitch (player (tourV T i) (dayV r i))
abbrev hill (r:ℕ) (i:TileC H P p V C): Script (Shade G) r:= flagsH P (marksD r) i
section
variable {T:Medal P G B.K P.J}(B0: Roles (M:=TileC H P p V C) T UA VA s downK upperX)
include B0
lemma paper (h:∀ j,j<r+1→ 0 < j → Tall (H:=H) (P:=P) (p:=p) (V:=V) (C:=C) j m): Wcap H P p V C m (riseF T (r+1)-hill (r+1)):=by
     have he:=B0.pager (p:=fun i=>(UA i).word) (q:=fun i=>(VA i).word) (fun i=> ((UA i).fullK (r+1)|>.here (r+1))) (fun i=> ((VA i).fullK (r+1)|>.here (r+1))) (B0.uni₂ (r+1) m) (fun i=> ⟨_, stint_cut _ _ _ _ ((UA i).fullK (r+1)) ((VA i).fullK (r+1))⟩) h; exact he
lemma runIt (r:ℕ)(hh:tariffs G P B.K r m)(ht:r ≤ 3)(hq: Wcap H P p V C m ((marksD (r+1) ∘fallsF)-hill (r+1))): Tall (H:=H) (P:=P) (p:=p) (C:=C) (V:=V) (r+1) m:=by
   have he:= Loan.debit (B0.uni₁ (r+1) m) (B0.uni₂ (r+1) m) B0.fuel zero_le_one; apply onWheels (P:=P) (H:=H) (p:=p) (U:=marksD (r+1)) (W:=hill (r+1)) (V:=V) C m he hq -- arguments
   intro i c hp; exact hh (UA i).gear (marksD (r+1) i) c hp ((UA i).pollzz (VA i) ht) ((stint_cut _ _ _ _ ((UA i).fullK (r+1)) ((VA i).fullK (r+1))).sym _).1
lemma luckThree (hV:LocalRatio V) (hh: Crest G P B.K m)(h:∀ i,i<3→ 0 < i → Tall (H:=H) (P:=P) (p:=p) (V:=V) (C:=C) i m): Tall (H:=H) (P:=P) (p:=p) (V:=V) (C:=C) 3 m:=by
    apply runIt B0 2 hh.Tri (by omega); let v(i:TileC H P p V C):= (tourP T i).Tell 3-(tourV T i).Tell 3; have he: (marksD (p:=p) (H:=H) (P:=P) (V:=V) (C:=C) 3∘fallsF)=riseF T 3+v:=by
       ext1 i; have hx:= colorshift P T (UA i) _ (i.1.1.shot _) hV; have hy:= colorshift P T (VA i) _ (i.1.2.shot _) hV
       let X:= tourP T i; let Y:= tourV T i; let a:= UA i; let b:= VA i; have hz: dayU 3 (fallsF i)=stitch (X.T3 a.live a.clip):=hx.1; have hi:dayV 3 (fallsF i)=stitch (Y.T3 b.live b.clip):=hy.1; change dayU 3 _-dayV 3 _=riseF _ _ i+v i; rw [hz,hi,X.T3split a.pays,Y.T3split b.pays]; exact add_sub_add_comm ..
    rw [he,show _+v-hill 3=riseF T 3-hill 3+v by abel]; exact Loan.seize (paper B0 (r:=2) h) (B0.ear 3 m) B0.fuel (fun i=>(B0.tune i).le)
lemma luckFour (hV:LocalRatio V) (hh: Crest G P B.K m)(h:∀ i,i<4→ 0 < i → Tall (H:=H) (P:=P) (p:=p) (V:=V) (C:=C) i m): Tall (H:=H) (P:=P) (p:=p) (V:=V) (C:=C) 4 m:=by
    apply runIt B0 3 hh.Quad le_rfl
    let V'(i:TileC H P p V C):=(tourP T i).Tell 4-(tourV T i).Tell 4; let X(i:TileC H P p V C):=(tourP T i).Exc (UA i).live (UA i).clip-(tourV T i).Exc (VA i).live (VA i).clip; have hx: Wcap H P p V C m X:= B0.exc (h 3 (by omega) (by omega)); have he: (marksD (p:=p) (P:=P) (H:=H) (V:=V) (C:=C) 4∘fallsF)=riseF T 4+V'+X:=by
       ext1 i; let D:=tourP T i; let Y:=tourV T i; let a:= UA i; let b:=VA i; have ht:=colorshift P T (UA i) _ (i.1.1.shot _) hV; have hB:=colorshift P T (VA i) _ (i.1.2.shot _) hV; have hp:dayU 4 (fallsF i)=stitch (D.T4 a.live a.clip):=ht.2.1; have hh: dayV 4 (fallsF i)=stitch (Y.T4 b.live b.clip):=hB.2.1; change dayU 4 (fallsF i)-dayV 4 (fallsF i)= (riseF _ _ i+V' i)+ X i; rw [hp,hh,D.T4split a.pays,Y.T4split b.pays]; rw [add_sub_add_comm,add_sub_add_comm]
    rw [he,show _+V'+X-hill _=riseF T 4-hill 4 +V'+X by abel]; have hv:0 ≤ (downK:Crew H P p V C × ℕ→ℝ):=fun i=> (B0.tune i).le; exact Loan.seize (Loan.seize (paper B0 (r:=3) h) (B0.ear _ m) B0.fuel hv) hx B0.fuel hv
end
end Alps
end YM.OPE.Votive
