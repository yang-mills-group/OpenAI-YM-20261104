import YM.FVA2.Scale.Rigid
/-!
# One-parameter groups on positions

Entire labels, fixed units and engineering factors, include log sign:
 scaling t (for t positive) probes **smaller** distances. This is already
 a group law on ALL orders & every finite horizon. No finite-coupling
 or multiple-coherent-family assumptions. Construct the group using exactly
 this and every $MS_Data$. `PurePower` verified independently (from coincidence on
 common regulator and polynomial pricing). Differential reading and quantitative
 upgrades addressed separately.
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
variable {G:Gauge} (ν:ℝ) (Y: Initialize G){V:Normalize.Store G}(K:Rose.Pick V){O:Booked (Press.portDeck G)}(T:MS_Data G O)
/-- Uniquely characterize fields at every real change of log measurement scale.
 Does not vary the horizon when comparing two such renormalizations. -/
structure Touched (A:Arenas G) (p:ℝ→Cn)(B:ℝ→Frames G): Prop where
    led t : Tangent (p t)
    paid t i: Base (B t i)
    reads t: Phase t A (p t) (B t)
    continues t {i j:ℕ}(h:i≤j): Walk h (B t i) (B t j)
    whole : Unique A
namespace Touched
variable {A:Arenas G}{p:ℝ→Cn}{B:ℝ→Frames G}
theorem additive (h:Touched A p B)(μ ν:ℝ): p (μ+ν)=( p ν ).subst (p μ) ∧ ∀ i, B (μ+ν) i=convertT ν ( B μ i ) * stepV (p μ) ( B ν i ):= by
    let v(i:ℕ):= convertT ν ( B μ i ) * stepV (p μ) ( B ν i ); obtain ⟨hs,hq⟩:= once _ _ ( h.led (μ+ν)) ((h.led ν).compose (h.led μ)) (μ+ν) A h.whole _ v (h.paid (μ+ν)) (fun i=> ( converts ν _ ( h.paid μ i ) ).mul (( h.paid ν i ).switch (h.led μ|>.real)) ) (h.reads _) ( compose_phase ( h.led _ ) _ _ _ ( h.led _ ) ( h.reads μ ) (h.reads ν) ); exact ⟨hs,congr_fun hq⟩ -- order
lemma ground (h:Touched A p B): p 0=PowerSeries.X ∧ ∀ i,B 0 i=1:= by obtain ⟨hf,hb⟩:= once (p 0) PowerSeries.X (h.led _) (Tangent.unit) 0 A h.whole _ (fun _=>1) ( h.paid 0 ) ( fun _=> Base.one ) (h.reads 0) (empty_phase A); exact ⟨hf,congr_fun hb⟩
lemma specify (H:Touched A p B) (t:ℝ) (q:Cn)(a:Frames G)(hp:Tangent q)(hb:∀ i,Base (a i))(hv:Phase t A q a): q=p t ∧ a=B t:= once _ _ hp ( H.led t ) t A H.whole _ _ hb (H.paid t) hv ( H.reads t )
end Touched
namespace GroupS
local notation "P"=> Measure.start Y K
local notation "U"=> Measure.outlook Y K
local notation "φ"=> Measure.f K
local notation "χ"=> Measure.chi K
local notation "L"=> Measure.liftT K
local notation "Z"=> Measure.Z Y K
-- irrespective of the specified MS outputs: uniqueness on X will give same result for that
-- action. Need choose once.
def ψ (ν:ℝ) (t:ℝ): Cn := (Measure.chi K (ν - t) T).subst (Measure.f K ν T)
def gaugeB (ν t:ℝ)(d:ℕ): Guard G d:= mirror ( convertT t (Measure.liftT K ν T d) ) * stepV (ψ K T ν t) ( Measure.liftT K (ν-t) T d )
def gaugeN (ν t:ℝ)(d:ℕ): Guard G d:= mirror ( Measure.Z Y K ν T d ) * stepV (ψ K T ν t) ( Measure.Z Y K (ν-t) T d ) -- Δ exponent cancels by Hom.
local notation "τ"=> ψ K T ν
local notation "S'"=> gaugeB K T ν
local notation "Z'"=> gaugeN Y K T ν
def Ψ (ν:ℝ)(t:ℝ): Cn:= PowerSeries.subst ( Measure.chi K ν T ) ( (Measure.f K ν T).subst (ψ K T ν t) )
abbrev tie (ν t:ℝ)(d:ℕ): Guard G d:= Measure.Z Y K ν T d * gaugeN Y K T ν t d * mirror (stepV (ψ K T ν t) ( Measure.Z Y K ν T d ))
def gaugeM (ν:ℝ)(t:ℝ)(d:ℕ): Guard G d:= stepV (Measure.chi K ν T) (tie Y K T ν t d)
open Scale.Specific
variable (S:Prescription (Press.portDeck G)) (h:G.Simple)(hs:TaylorOKF T (Press.wickInput Y) S)(hr:Favors.Horder S)(hu:Ace.UnitP S)
include h hs hr hu ν
variable (t:ℝ){d e:ℕ}
local notation "f" => φ ν T
local notation "x" => χ ν T
local notation "π"=> Ψ K T ν
lemma true_ψ : Tangent ( ψ K T ν t ):= ( vigor_x Y K (ν - t) T S h hs hr hu ).compose ( vigor_f Y K ν T S h hs hr hu )
lemma true_m : Tangent (π t):= ( (( vigor_f Y K ν T S h hs hr hu ).compose ( true_ψ ν Y K T S h hs hr hu t )).compose ( vigor_x Y K ν T S h hs hr hu ) ) -- whitespace
lemma pact : ( φ (ν-t) T ).subst (τ t)= φ ν T:= by
    unfold ψ; rw [ ← Tangent.steps _ ( vigor_x Y K (ν-t) T S h hs hr hu ) ( vigor_f Y K ν T S h hs hr hu ), ( Select.vigor Y K (ν-t) T S h hs hr hu|>.left ), subst_X (licence _ (vigor_f Y K ν T S h hs hr hu|>.start)) ]
lemma contract0 : (π t).subst (Measure.f K ν T)= ( Measure.f K ν T ).subst (τ t):= by
    unfold Ψ; rw [ Tangent.steps _ ( vigor_x Y K ν T S h hs hr hu ) ( vigor_f Y K ν T S h hs hr hu ),( Select.vigor Y K ν T S h hs hr hu|>.right ), X_subst ] -- name
-- generalized scale law from comparison.T
local notation "Tg"=> true_ψ ν Y K T S h hs hr hu t
local notation "Zκ"=> Measure.litZ Y K
local notation "B'"=> gaugeM Y K T ν
lemma apply_p (X: Way G d) (f':ℝ→Guard G d)(hp:∀ v:ℝ,Base (f' v)) (H:∀ v:ℝ,actMark (f' v) (couple (φ v T) (wave v T d))=X): actMark (mirror (convertT t ( f' ν )) * stepV (τ t) ( f' (ν-t) )) ( scaling t X )=couple (τ t) X:= by
    nth_rw 1 [ ← H ν ]; rw [← H (ν-t), pose_act, couple_s, clocks ν T Y S h hs ]; rw [ acts, ← mul_assoc, (converts t _ (hp ν )|>.turn'), one_mul, ← Facets.team _ _ _ (Tg).start, Facets.double _ _ _ ( vigor_f Y K (ν-t) T S h hs hr hu |>.start ) ((Tg).start), pact ν Y K T S h hs hr hu t ]; -- acts orientation
lemma actionX : Phase t (start Y K) (τ t) (S' t):= fun d=> apply_p ν Y K T S h hs hr hu t _ (fun v:ℝ=> liftT K v T d ) (fun v=> Measure.charges Y K v T S h hs hr hu ) (fun v=> Measure.together Y K v T S h hs hr hu d )
lemma actionY : Phase t (Measure.outlook Y K) (τ t) (Z' t):= by intro d; have H:= apply_p ν Y K T S h hs hr hu t _ (fun v=> Measure.Z Y K v T d) (fun v=> litZ Y K v T S h hs hr hu) (fun v=> compares Y K v T S h hs hr hu); simp_rw [ old_g t ( Measure.Z Y K ν T d ) ( precise Y K ν T S h hs hr hu ) ] at H; exact H
lemma true_B : Base (gaugeB K T ν t d):=( converts t _ ( Measure.charges Y K ν T S h hs hr hu )|>.rewind ).mul (( Measure.charges Y K (ν-t) T S h hs hr hu ).switch ((Tg).real))
lemma true_N : Base (gaugeN Y K T ν t d):= (Measure.litZ Y K ν T S h hs hr hu|>.rewind).mul ((litZ Y K (ν-t) T S h hs hr hu).switch (Tg).real)
lemma true_Mt : Base (tie Y K T ν t d):= ((litZ Y K ν T S h hs hr hu).mul (true_N ν Y K T S h hs hr hu t)).mul ((litZ Y K ν T S h hs hr hu).switch (Tg).real |>.rewind)
lemma true_M : Base (gaugeM Y K T ν t d):= ( true_Mt ν Y K T S h hs hr hu t ).switch ( vigor_x Y K ν T S h hs hr hu|>.real )
-- actual intertwine formula R.Z.Point
lemma formula_phi : stepV f (B' t d)= tie Y K T ν t d:= by rw [gaugeM, Frame.step_repeat _ _ _ (vigor_x Y K ν T S h hs hr hu|>.start) ( vigor_f Y K ν T S h hs hr hu|>.start ), ( Select.vigor Y K ν T S h hs hr hu|>.right ), Frame.step_identity ]
lemma contractM : stepV f (B' t d) * stepV (τ t) ( Z ν T d ) = Z ν T d * Z' t d:= by rw [formula_phi ν Y K T S h hs hr hu, tie,mul_assoc, ((litZ Y K ν T S (d:=d) h hs hr hu).switch (Tg).real|>.turn),mul_one ]
lemma actionM : Phase t (wave ν T) (π t) (B' t):= by
    intro d; let A:=wave ν T d; let a:=actMark (B' t d) (scaling t A); let b:=couple (π t) A; let V:=stepV (τ t) ( Z ν T d );
    have hv := ( litZ Y K ν T S (d:=d) h hs hr hu ).switch (Tg).real; have ho := actionY ν Y K T S h hs hr hu t d;
    let hP:= ( vigor_f Y K ν T S h hs hr hu ).start; let hQ:= ( vigor_x Y K ν T S h hs hr hu ).start
    rw [ ← Measure.compares Y K ν T S h hs hr hu,pose_act, old_g _ _ (precise Y K ν T S h hs hr hu), Facets.acts ] at ho
    have hp:actMark V ( couple f a )=actMark V ( couple f b ):= by
        rw [show couple f a=_ from (team (scaling t A) (B' t d) f hP).symm, Facets.acts, show stepV f (B' t d)*V=_ from contractM ν Y K T S h hs hr hu t, ← couple_s, ho ]; -- need ho defeq A
        unfold V b; rw [ ← Facets.team _ _ _ (Tg).start, Facets.double _ _ _ hP (Tg).start, Facets.double _ _ _ ( true_m ν Y K T S h hs hr hu t|>.start ) hP, contract0 ν Y K T S h hs hr hu t ] -- reverse team? LHS now couple τ X; RHS currently tall.Frame
    have hb(y): actMark (mirror V) (actMark V y)=y:= by rw [ acts,hv.turn',acts_h]
    replace hp:=congr_arg (actMark (mirror V)) hp; simp_rw [hb] at hp; replace hp:=congr_arg (couple x) hp; simp_rw [ Facets.double _ _ _ hP hQ,( Select.vigor Y K ν T S h hs hr hu |>.left ), team_one ] at hp; exact hp
-- mass-independent vs position; it is THE SAME running coupling in X measures.
lemma fitsN : Native ( Z' t d ):= Base.befits ((litZ Y K ν T S h hs hr hu).rewind) ((litZ Y K ν T S h hs hr hu).matter (precise Y K ν T S h hs hr hu)) ((litZ Y K (ν-t) T S h hs hr hu).switch (Tg).real) (Base.paid_sub _ (precise Y K (ν-t) T S h hs hr hu))
lemma fitsM : Native ( B' t d ):= by
    have he:= fitsN ν Y K T S (d:=d) h hs hr hu t; obtain hv:= ( litZ Y K ν T S (d:=d) h hs hr hu ); have hz:= ( precise Y K ν T S (d:=d) h hs hr hu ); apply Base.paid_sub; exact ( hv.mul ( true_N ν Y K T S h hs hr hu t ) ).befits ( hv.befits hz ( true_N ν Y K T S h hs hr hu t ) he ) ((hv.switch (true_ψ ν Y K T S h hs hr hu t|>.real)).rewind) ((hv.switch ( true_ψ ν Y K T S h hs hr hu t|>.real )).matter ( Base.paid_sub _ hz )) -- avoid shadow
lemma walkX (a:d≤e): Walk a ( S' t d ) (S' t e):= by obtain hv:= ( Measure.linkage K ν T a ).dial t; exact ( Walk.rewind hv ( converts t _ ( charges Y K ν T S h hs hr hu ) ) ( converts t _ ( charges Y K ν T S h hs hr hu ) ) ).mul ( ( linkage K (ν-t) T a ).steps _ )
lemma walkN (a:d≤e): Walk a ( Z' t d ) (Z' t e):= by obtain hv:= walks_o Y K ν T S h hs hr hu a; exact ( Walk.rewind hv ( litZ Y K ν T S h hs hr hu ) ( litZ Y K ν T S h hs hr hu ) ).mul ( ( walks_o Y K (ν-t) T S h hs hr hu a ).steps _ )
lemma walkM (a:d≤e): Walk a ( B' t d ) (B' t e):= by obtain hv:= walks_o Y K ν T S h hs hr hu a; exact Walk.steps (( hv.mul ( walkN ν Y K T S h hs hr hu t a ) ).mul ((hv.steps (τ t)).rewind ((litZ Y K ν T S h hs hr hu).switch (Tg).real) ((litZ Y K ν T S h hs hr hu).switch (Tg).real))) _
theorem scaleX : Touched (Measure.start Y K) τ S':= ⟨ fun t=> true_ψ ν Y K T S h hs hr hu t,fun t _i=> true_B ν Y K T S h hs hr hu t,actionX ν Y K T S h hs hr hu,fun _ _ _ hz=> walkX _ _ _ _ S h hs hr hu _ hz,unique_X Y K ν T S h hs hr hu ⟩
theorem scaleN : Touched (Measure.outlook Y K) τ Z':= ⟨ fun t=> true_ψ ν Y K T S h hs hr hu t,fun t _i=> true_N ν Y K T S h hs hr hu t,actionY ν Y K T S h hs hr hu,fun _ _ _ hz=> walkN _ _ _ _ S h hs hr hu _ hz,unique_N Y K ν T S h hs hr hu ⟩
theorem scaleM : Touched (wave ν T) π B':= ⟨ fun t=> true_m ν Y K T S h hs hr hu t,fun t _i=> true_M ν Y K T S h hs hr hu t,actionM ν Y K T S h hs hr hu,fun _ _ _ hz=> walkM _ _ _ _ S h hs hr hu _ hz,unique_M Y K ν T S h hs hr hu ⟩
local notation "γ"=> Measure.adjust Y K
lemma relatingN : S' t d * stepV (τ t) (γ d) = convertT t (γ d) * Z' t d:= by
    -- exact via uniqueness at X in scaled positions
    apply Manifest.unique (scaling t (P d)) _ _ h _ _ ( Manifest.fuel _ T Y S h hs ( Measure.dawn Y K ν T S h hs hr hu ) t )
    · rw [ ← acts, actionX ν Y K T S h hs hr hu t, Facets.team _ _ _ (Tg).start ]; rw [ ← acts, ← pose_act ]; exact ( actionY ν Y K T S h hs hr hu t d ).symm
    · exact Base.mul ( scaleX ν Y K T S h hs hr hu|>.paid t d ) (( Measure.adj Y K ν T S h hs hr hu |>.scale ).switch (Tg).real )
    exact Base.mul ( converts t _ ( Measure.adj Y K ν T S h hs hr hu|>.scale ) ) ( scaleN ν Y K T S h hs hr hu |>.paid t d )
end GroupS
end YM.FVA2.Scale
