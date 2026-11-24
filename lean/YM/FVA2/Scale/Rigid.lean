import YM.FVA2.Scale.Select
/-!
# Uniqueness transfers to every one of the actual frames

Scalings and coupling laws at each degree but with SAME map everywhere.
No stronger assumption e.g. every grade needing a nonzero β-role.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Scale
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical
open Dframe Level Reg.Point Reg.Token Reg.Unique Reg.Choice Facets Equator Measure Jury
variable {G:Gauge}{n d k:ℕ}
abbrev Arenas (G:Gauge):= (d:ℕ) → Way G d -- contexts
abbrev Frames (G:Gauge):= (d:ℕ)→ Guard G d
structure Tangent (p:Cn) : Prop where
    start : Rooted p
    lead : PowerSeries.coeff 1 p=1
    real : Reg.Unique.CoreR p
variable {X:Arenas G} {p q:Cn}
namespace Tangent
lemma unit : Tangent (PowerSeries.X:Cn):= ⟨ by simp [ Rooted ],by simp,by unfold CoreR; simp ⟩
lemma fct (hp:Tangent p): Tangent (back p):= ⟨(covers p hp.start hp.lead).own, stamp_t p hp.start hp.lead, core_l p (covers p hp.start hp.lead) hp.real⟩
lemma invert (hp:Tangent p): Payment p (back p):= covers p hp.start hp.lead
lemma compose (hp:Tangent p)(hq:Tangent q): Tangent (p.subst q):= ⟨ circle _ _ hp.start hq.start, (by rw [ stating_one p q hq.start, hp.lead,hq.lead,mul_one ]), Reg.Choice.star_p hp.real hq.real hq.start ⟩
-- associativity orient explicitly
lemma steps (u:Cn) (hp:Tangent p)(hq:Tangent q) : PowerSeries.subst q (u.subst p)=u.subst (p.subst q):= subst_comp_subst_apply (licence _ hp.start) (licence _ hq.start) _
end Tangent
-- set of allowable comparisons
-- stronger even allows p not identity tangent.BUT require tangent herein.
def Unique (X:Arenas G) := ∀ (p q:Cn) (a b: Frames G), Tangent p → Tangent q → (∀ i,Base (a i)) →(∀ i,Base (b i))→(∀ i, actMark (a i) (couple p (X i))=actMark (b i) (couple q ( X i )))→ p=q ∧ a=b
section abstract
variable (hp:Tangent p)(hq:Tangent q) (X Y:Arenas G) (u:Frames G)
-- conjugation `act◦couple` uses right composition
include hp
lemma unique_through (h:∀ i, actMark (u i) ( couple p (X i) )= Y i) (H:Unique X) (he:∀ i, Base (u i)) : Unique Y:= by
    intro q r a b hq hr ha hb ht; let A i:= stepV q (u i) * a i; let B i:=stepV r (u i)*b i
    have heq {z:Cn}(hz:Tangent z)(i): couple z (Y i) = actMark ( stepV z (u i) ) ( couple ( p.subst z ) (X i) ):= ( by rw [ ← h, ← team _ _ _ hz.start, Facets.double _ p z hp.start hz.start ] );
    obtain ⟨hc,hV⟩:= H _ _ A B (hp.compose hq) (hp.compose hr) (fun i=> ((he i).switch hq.real).mul (ha i)) (fun i=> ((he i).switch hr.real).mul (hb i)) (fun i=> by specialize ht i; rw [ heq hq, heq hr, acts, acts ] at ht; exact ht)
    have hl:r=q:= by
       replace hV:= congr_arg (fun x:Cn=> (back p).subst x) hc -- shape
       rw [ ← Tangent.steps _ hp hq, ← Tangent.steps _ hp hr,hp.invert.left, subst_X (licence _ hq.start),subst_X (licence _ hr.start) ] at hV; exact hV.symm
    subst r; exact ⟨ rfl, funext fun i=> ((( he i ).switch hq.real ).lies.seed.mul_right_inj).mp (congr_fun hV i) ⟩
/-- Genuine action law on separated kernels with explicit position and field scalings. `Base`
required on the residual part of b (besides engineering diagonal used in report). -/
def Phase (t:ℝ)(X:Arenas G)(p:Cn)(u:Frames G): Prop:= ∀ i, actMark (u i) (scaling t (X i))=couple p (X i)
omit hp in
lemma once (p q:Cn)(hp:Tangent p)(hq:Tangent q)(t:ℝ)(A:Arenas G)(H:Unique A) (b c: Frames G)(hb:∀ i,Base (b i))(hc:∀ i,Base (c i)) (hv:Phase t A p b)(hk:Phase t A q c): p=q∧b=c:= by
    have hx {p:Cn}{u: Frames G} (he:∀ i, Base (u i))(hq:Phase t A p u) i: actMark (mirror (u i)) (couple p (A i))= scaling t (A i):= by rw [ ← hq, acts, (he i).turn',acts_h ]
    obtain ⟨h₁,h₂⟩:= H p q (fun i=> mirror (b i)) (fun i=> mirror (c i)) hp hq (fun i=>(hb i).rewind) (fun i=>(hc i).rewind) (fun i=> (hx hb hv i).trans (hx hc hk i).symm); exact ⟨h₁,funext fun i=> (hb i|>.twice).symm.trans ((congr_arg mirror ( congr_fun h₂ i )).trans (hc i|>.twice)) ⟩
-- Compose the phases by applying the second action to the scale derivative.
variable {μ ν:ℝ}
lemma compose_phase (v:Frames G)(hq:Tangent q)(h:Phase μ X p u)(H:Phase ν X q v): Phase (μ+ν) X (q.subst p) (fun i=> convertT ν ( u i ) * stepV p (v i)):= by
    intro i; rw [ ← acts, ← scales (X i) ν μ, ← pose_act, h i, couple_s, team _ _ _ hp.start, H i, Facets.double _ _ _ hq.start hp.start ] -- q & p RHS correct
omit hp
lemma empty_phase : Phase 0 X PowerSeries.X (fun _=>1):= by intro i; rw [ acts_h,team_one,stand_s ]
end abstract
namespace Specific
variable (Y:Initialize G){V:Normalize.Store G}(K:Rose.Pick V) (ν:ℝ){O:Booked (Press.portDeck G)}(T:MS_Data G O)
variable (S:Prescription (Press.portDeck G))(h:G.Simple)(hs:TaylorOKF T (Press.wickInput Y) S)(hr:Favors.Horder S)(ht:Ace.UnitP S)
local notation "Xp"=> Measure.start Y K
local notation "Wx"=> Measure.outlook Y K
local notation "M"=> wave ν T
local notation "χ"=> Measure.chi K ν T
local notation "φ"=> Measure.f K ν T
local notation "N"=> Measure.adjust Y K
local notation "Z"=> Measure.Z Y K ν T
include h hs hr ht
lemma vigor_f : Tangent ( Measure.f K ν T ):= by obtain hp:= Reg.Faith.hearty ν Y K S T h hs hr ht; exact ⟨ hp.cost.own, hp.slope, hp.trueQ ⟩
lemma vigor_x : Tangent ( Measure.chi K ν T ):= ⟨ (Select.vigor Y K ν T S h hs hr ht|>.launch), Reg.Choice.stance ν Y K S T h hs hr ht, Reg.Choice.token ν Y K S T h hs hr ht ⟩
lemma differing (d:ℕ) : wave ν T d=actMark (mirror ( stepV χ (Z d) )) ( couple χ ( Measure.outlook Y K d ) ):= by
    rw [← compares Y K ν T S h hs hr ht, ← team _ _ _ ( vigor_x Y K ν T S h hs hr ht|>.start ), acts, (( litZ Y K ν T S (d:=d) h hs hr ht ).switch (vigor_x Y K ν T S h hs hr ht|>.real)).turn', acts_h, Facets.double _ _ _ (vigor_f Y K ν T S h hs hr ht|>.start) ( vigor_x Y K ν T S h hs hr ht|>.start ),( Select.vigor Y K ν T S h hs hr ht ).left,team_one ]
include ν
lemma unique_X : Unique (start Y K):= fun _ _ _ _ H V=> Select.lock Y K ν T S h hs hr ht V.start H.start V.real H.real _ _ -- orientation
lemma unique_N : Unique (outlook Y K):= unique_through Tangent.unit Xp Wx N (fun i=> by rw [team_one]; rfl ) (unique_X Y K ν T S h hs hr ht) (fun _=> Measure.adj Y K ν T S h hs hr ht|>.scale)
include K
lemma unique_M : Unique (wave ν T):= unique_through ( vigor_x Y K ν T S h hs hr ht ) (outlook Y K) (wave ν T) (fun i => mirror ( stepV χ (Z i))) (fun i=> (differing Y K ν T S h hs hr ht i).symm) (unique_N Y K ν T S h hs hr ht) ( fun i=> (( litZ Y K ν T S (d:=i) h hs hr ht).switch (vigor_x Y K ν T S h hs hr ht|>.real) ).rewind )
-- eqconv unique testimonial.Phase across all admissible arities through d.
theorem unique_map (p:Cn)(B:Frames G) (hq:Tangent p)(hb:∀ i, Base ( B i ))(H:∀ i, actMark (B i) (couple p (wave ν T i))=Measure.outlook Y K i): p=φ ∧ B=Z:= unique_M Y K ν T S h hs hr ht p φ B Z hq (vigor_f Y K ν T S h hs hr ht) hb (fun i=> litZ Y K ν T S (d:=i) h hs hr ht) (fun i=> ( H i ).trans ( Measure.compares Y K ν T S (d:=i) h hs hr ht ).symm )
end Specific
end YM.FVA2.Scale
