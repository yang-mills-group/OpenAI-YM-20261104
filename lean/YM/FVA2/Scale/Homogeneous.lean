import YM.FVA2.Scale.Smoke
/-!
# Obtain the mass-independent check N under a scale criterion on physical reads

`Prepare`: one scale action satisfying `Law` -- with `Clear` and `Tracks` (polynomial
in log-scale parameter) and `Native` (grade-preserving). Use `Precise.only` for
existence and uniqueness of the adjustment when defined using this property (rather
than `PowerCondition`). This is a property of the *formal correlations*, independent
of specifying an `MS_Data`. We prove it using the comparison to the actual MS data.

No lack of uniqueness from choosing a scale order-by-order. Also prove the scale law
for the MS fields, and both will be packed with the comparison, `Scale/System`.
For the corresponding differential result see `Clef/Winds`.
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
open Meter GroupS
variable {G:Gauge}
section waltz
variable (A:Arenas G)(u:ℝ→Cn) (B:ℝ→Frames G)
/-- Full scale form. Include the group with inverse and coupling tangent and polynomial/smooth necessity.
And require grading (strictly stronger than Touched by itself).
Use for grading of N in §kfar. -/
structure Law (A:Arenas G)(u:ℝ→Cn)(B:ℝ→Frames G) : Prop extends Touched A u B where
    smooth : Clear u
    ready t k: Native ( B t k )
    proper d k: Tracks (fun t=> B t d) k
    invert d k: Tracks (fun t=> mirror ( B t d )) k
lemma Law.meets (H: Law A u B)(d:ℕ): PurePower (A d):= by
    have h(t): scaling t (A d)= actMark ( mirror (B t d) ) ( couple (u t) (A d) ):= by rw [ ← H.reads, acts, ( H.paid t d ).turn',acts_h ]; -- rfl
    intro n x v i; simp_rw [h]; exact ( rides _ _ ( Meter.together (fun _=> A d) ( fun n p i v=> Rhythm.const _ ) u H.smooth ) ( H.invert d ) ) n x i v
end waltz
namespace Precise
variable (ν:ℝ)(Y: Initialize G){V: Normalize.Store G}(K:Rose.Pick V){O:Booked (Press.portDeck G)}(T:MS_Data G O)
local notation "p"=> (GroupS.ψ K T ν)
local notation "f"=> Measure.f K ν T
local notation "x"=> Measure.chi K ν T
local notation "χ"=> GroupS.Ψ K T ν
local notation "U"=> outlook Y K
local notation "M"=> wave ν T
local notation "B"=> gaugeM Y K T ν
local notation "N"=> gaugeN Y K T ν
variable (S:Prescription (Press.portDeck G)) (h:G.Simple)(hs:TaylorOKF T (Press.wickInput Y) S)(hr:Favors.Horder S)(hu:Ace.UnitP S)
include h hs hr hu
local notation "A"=> Pace.formal.fixed
open Specific
lemma smooth : Clear p:= by
    have hP : Clear ( fun t:ℝ=> Reg.Choice.choice (ν-t) K T ) := by
        intro i; apply Rhythm.unit.mp; obtain he:= ( Known.method Y S T h hs hr hu K i ).pre ( Polynomial.C ν- Polynomial.X ); have ht(t:ℝ): Polynomial.eval t (Polynomial.C ν- Polynomial.X)=ν-t:=by rw [Polynomial.eval_sub (R:=ℝ),Polynomial.eval_C (R:=ℝ),Polynomial.eval_X (R:=ℝ)]
        simp_rw [ht] at he; exact he
    exact Pace.formal.substitute hP (A (fun _:Unit=> f)) (fun _ _=> ( vigor_f Y K ν T S h hs hr hu ).start)
lemma fitM : Clear χ:= Pace.formal.substitute ( Pace.formal.substitute ( A (fun _:Unit=>f) ) ( smooth ν Y K T S h hs hr hu ) ( fun _ t=> ( true_ψ ν Y K T S h hs hr hu t ).start ) ) ( A (fun _:Unit=>x) ) ( fun _ _=> ( vigor_x Y K ν T S h hs hr hu ).start )
variable (L:Arenas G)(Q:ℝ→Cn)(V':ℝ→Frames G)
omit hr hu
lemma lawfully (P:Touched L Q V')(hx:∀ i,StarGround (L i))(u:Clear Q) (H:∀ i,PurePower (L i))(he:∀ t i,Native (V' t i)): Law L Q V':= by
    let W (d:ℕ)(t:ℝ):= scaling t (L d); let K (d:ℕ)(t:ℝ):= couple (Q t) (L d); have hw(d):Gets ( W d ):= fun n a b c=> H d n a c b; have ht d:Gets (K d):= Meter.together ( fun _=> L d ) (fun _ _ _ _=>Rhythm.const _) Q u; have hV (t d): actMark (V' t d) (W d t)=K d t:= P.reads t d
    have hs' (d): Gets (fun t=> actMark (V' t d) (W d t)):= by simp_rw [hV]; exact ht d
    refine ⟨P,u, he, fun d k=> walks h _ _ k (fun t=> Manifest.fuel (L d) T Y S h hs (hx d) t) (hw d) (fun t=> P.paid t d) (hs' d), fun d k=> ?_ ⟩
    apply walks h (K d) (fun t=> mirror (V' t d)) k (fun t=> step_dawn _ (Q t) (hx d)) (ht d) (fun t=> P.paid t d |>.rewind); unfold Gets; simp_rw [ ← hV, acts,(P.paid ..).turn', acts_h ]; exact hw d -- ambiguity
include hr hu
lemma mainN : Law U p N := lawfully Y T S h hs _ _ _ ( scaleN ν Y K T S h hs hr hu ) (fun i=> scaled_sigma Y K ν T S (d:=i) h hs hr hu ) ( smooth ν Y K T S h hs hr hu ) (fun i=> ( adj Y K ν T S (d:=i) h hs hr hu ).homogeneous ) ( fun t _i=> fitsN ν Y K T S h hs hr hu t )
lemma mainM : Law M χ B:= lawfully Y T S h hs _ _ _ ( scaleM ν Y K T S h hs hr hu ) (fun i=> before ν T (d:=i)) ( fitM ν Y K T S h hs hr hu ) (fun _=> Equator.smooth ν T Y S h hs ) ( fun t _i=> fitsM ν Y K T S h hs hr hu t )
-- intrinsic version.Existence & character. group uses no mention of ν in statement.
include ν
def Prepare (Y:Initialize G){V:Normalize.Store G}(K:Rose.Pick V)(D: Frames G) : Prop := (∀ i,Base (D i) ∧ Scale.remainder (D i)) ∧ ∃ (φ:ℝ→Cn)(Z:ℝ→Frames G), Law (fun i=> actMark ( D i ) (start Y K i)) φ Z
lemma only (D:Frames G): Prepare Y K D ↔ D=Measure.adjust Y K:= by
    constructor; · rintro ⟨hL,Q,X,H⟩; exact funext fun i=> ( onlyT Y K ν T S h hs hr hu _ ).mp ⟨ (hL i).1,(hL i).2,H.meets ( fun i=> actMark ( D i ) ( start Y K i )) Q X i ⟩ -- parameters
    rintro rfl; exact ⟨fun i=> ⟨( adj Y K ν T S (d:=i) h hs hr hu ).scale, ( adj Y K ν T S h hs hr hu ).strict⟩, p,N, mainN ν Y K T S h hs hr hu⟩
end Precise
end YM.FVA2.Scale
