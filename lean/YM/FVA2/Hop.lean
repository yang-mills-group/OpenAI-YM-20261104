import YM.FVA2.SkimLaw
/-!
# Assembly of transformations. Right-action orientation (apply in order left through right).
 Grade-F & Grade-Strict categories, the flow. Only identity-leading maps.
-/
set_option autoImplicit false
set_option maxHeartbeats 364000
noncomputable section
namespace YM.FVA2.Verne
open Function Filter Set Pert Pert.Position Lattice Maxwell Maxwell.Free Pert.RawLabels PositionX PositionX.Jet PositionX.Ribbon PositionX.Detector PositionX.Bend Elegant PayAll ColorCode
open Panel Strat
open scoped Topology ContDiff Classical
variable {G:Gauge} (F:Labels.Frames G)
structure Hop (F:Labels.Frames G) where
   f:Word ℝ
   rooted: light f
   primary:f 1=1
   Z: Strat F
   tangent: Z.pulse
namespace Hop
variable {F} (W A B:Hop F)(P:Panel F) (s t:ℝ)
lemma loved : Genuine W.f:= ⟨ W.rooted,W.primary.symm ▸ one_ne_zero ⟩
@[ext] lemma ext {X Y:Hop F}(h:X.f=Y.f)(h':X.Z=Y.Z): X=Y:= by cases X; cases Y; congr
instance : Mul (Hop F) where
   mul X Y:=
      ⟨ ren Y.f X.f, (Jet.ren_light Y.rooted _).trans X.rooted, (by rw [Jet.tip Y.rooted _, Y.primary,one_smul,X.primary]), resume X.Z Y.f*Y.Z, Strat.pulse.grow _ _ ( Strat.pulse.near X.Z X.tangent Y.rooted ) Y.tangent ⟩ -- syntax
instance : One (Hop F) where
   one:= ⟨ headway, head_light, tip_head,1,Strat.initial ⟩
lemma walkF : (A*B).f= ren B.f A.f:= rfl
lemma walkZ : (A*B).Z= resume A.Z B.f*B.Z:= rfl
@[simp] lemma eF : (1: Hop F).f=headway:= rfl
@[simp] lemma eZ : (1: Hop F).Z=1:= rfl
instance : Monoid (Hop F) where
    one_mul A := Hop.ext (by rw [walkF, eF,head_ren A.rooted]) (by rw [walkZ,eZ,resume0,one_mul])
    mul_one A:= Hop.ext (by rw [walkF,eF,ren_head]) (by rw [walkZ,eF,eZ,resumeHead,mul_one])
    mul_assoc A B C:= by
        apply Hop.ext; simp_rw [ walkF ]; rw [Jet.asc C.rooted B.rooted]; simp_rw [ walkZ ]; rw [resumeT _ _ C.rooted,resumeM _ C.rooted B.rooted, ← walkF,mul_assoc ]
-- panel adapter
abbrev act (P:Panel F)(X:Hop F):Panel F:= (P.join X.f).flip X.Z -- namespace.P dot uses Hop positional.
lemma act_step (P:Panel F) : act ( act P W ) A= act P (W*A):= by unfold act; rw [join_flip _ _ _ A.rooted,join_step _ _ _ W.rooted A.rooted,flip_mul ]; rfl
lemma dormant (P:Panel F): act P 1=P:= by unfold act; rw [eF,eZ,join_id,leading]
-- Frame goes to ∆^-1K∆ under scale.
def glance (s:ℝ)(G:Hop F) : Hop F:= { G with
   Z:= Λ F (-s)* G.Z * Λ F s
   tangent:= Panel.grows_scl s G.Z G.tangent }
lemma bevel : (act P W).swell s= act (P.swell s) (glance s W):= by unfold act; rw [ scl,join_scl _ _ _ W.rooted ]; rfl
lemma timely : (glance s A).f=A.f:= rfl
lemma still (r t:ℝ): glance r (glance t W)= glance (r+t) W:= by
   apply ext;rfl; change Λ F (-r) * (Λ F (-t) * _ * Λ F t )*Λ F r= Λ F (-(r+t))*_ * Λ F (r+t); rw [ ← mul_assoc, ← mul_assoc,east, mul_assoc, east, neg_add, add_comm r t ] -- try
-- inverses with Detector. no Canonical Group instance necessary
variable (D:( d:ℕ )→ Detector F d) {R:ℝ} (T:Booth R F)
def undoV : Hop F:=
    let f:= Jet.inverse W.f; ⟨ f, Jet.lives _, (by unfold f; rw [ tip_inv W.loved, W.primary,inv_one ] ), resume (refresh D W.Z W.tangent) f, Strat.pulse.near _ ( right_refresh D W.Z W.tangent|>.1 ) (Jet.lives _ ) ⟩
lemma lefto : W * undoV W D=1:= by
   apply Hop.ext; · rw [walkF,eF]; exact guarded W.loved
   rw [walkZ,eZ]; let f:=Jet.inverse W.f; let X:= refresh D W.Z W.tangent; change resume W.Z f*resume X f=_; rw [← resumeT _ _ ( Jet.lives _ ),show W.Z*X=1 from (right_refresh D W.Z W.tangent).2.1, resume0 ]
lemma righto: undoV W D*W=1:= by
   apply Hop.ext; · rw [walkF,eF]; exact headback W.loved
   rw [walkZ,eZ]; let X:= refresh D W.Z W.tangent; change resume (resume X (Jet.inverse W.f)) W.f * W.Z=_; rw [ resumeM _ W.rooted ( Jet.lives _ ),headback W.loved,resumeHead ]; exact ( right_refresh D W.Z W.tangent).2.2
lemma approach (H:P.Fresh) : Fresh (act P W):= Panel.Fresh.matrix _ ( Panel.Fresh.pre P H W.rooted ) W.tangent
lemma interest (h:P.Fresh) : testable (act P W) D T= ren W.f (testable P D T):= by unfold act; rw [← Panel.money (P.join W.f) _ T ( Panel.Fresh.pre P h W.rooted ) W.tangent, Panel.fieldYear P D T h W.rooted ]
lemma distinct (h:P.Fresh)(hh:P.tangible D T)(he:act P A=act P B): A=B:= by
    obtain ⟨hp,hv⟩:= Panel.recognized_t P D T h hh A.tangent B.tangent A.rooted B.rooted he; exact Hop.ext hp hv
lemma presence (H:P.Fresh)(hp:tangible P D T): tangible ( act P W ) D T:= by
    unfold tangible; rw [ interest _ P D T H ]; -- placeholder adjust
    refine ⟨ ( Jet.ren_light W.rooted _ ).trans ( show Genuine _ from hp ).1,?_ ⟩; rw [ Jet.tip W.rooted _, W.primary,one_smul ]; exact hp.2
-- grade dot. emphasize converted Eq.
def gradedStep := Strat.only A.Z=A.Z
def flag (ξ: Strat F) (hx:ξ.pulse) : Hop F:= ⟨ headway, head_light, tip_head, ξ,hx ⟩
lemma flagP (h:A.f=headway) : A=flag A.Z A.tangent:= Hop.ext h rfl
lemma flag_act (ξ: Strat F) (hx:ξ.pulse) (P:Panel F): act P ( flag ξ hx )=P.flip ξ := by unfold act flag; simp only [ Panel.join_id ]
-- define scale implementation.T
abbrev Flo (P:Panel F)(s:ℝ)(W:Hop F): Prop:= P.swell s=act P W
lemma flow_focus (hP:Fresh P)(hc:P.tangible D T)(S:ℝ→Hop F)(h:∀t,Flo P t (S t)): S (s+t)= S t * glance t (S s):= by
   apply distinct _ _ P D T hP hc; rw [ ← h, ← act_step, ← h t,← bevel, ← h s ]; exact (Panel.swell_steps P _ _).symm -- directions edit.h P t wrong
lemma day_eq (V:Warehouse G)(P:Panel V.F) {A:Hop V.F}(D:(d:ℕ)→Detector V.F d)(hv:P.Fresh)(he:Ember.plain V P)(h:Ember.plain V ( act P A )): gradedStep A := Ember.obstruction V (P.join A.f) A.Z D (Panel.Fresh.pre _ hv A.rooted) A.tangent ( Ember.shapeμ V P he A.rooted ) h
end Hop
end YM.FVA2.Verne
