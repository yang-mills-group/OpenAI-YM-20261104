import YM.FVA2.Clef.Forge
/-!
 # Wind after precomposition

 This exhibits the generator prescription on the **actual formal scale group** after
 any permitted near-free frame; no grading hypothesis in differentiating. Turns
 come from conjugation by engineering dimensions. Gives growth law with inverse.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Clef
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical
open Dframe Reg.Point Reg.Token Reg.Unique Reg.Choice _root_.YM.FVA2.Scale
open YM.FVA2.Scale.Facets Scale.Level Scale.Equator Scale.Measure Scale.Jury
open Scale.Meter Scale.GroupS Scale.Beta Generator.Der Generator.Drive
variable {G:Gauge}{d n i j:ℕ}
local notation "𝒢" => (Guard G d)
variable {X:Arenas G}{p:ℝ→Cn}{B:ℝ→Frames G}
-- precomposition on right of Z
abbrev rendition (X:Arenas G)(A:Frames G) : Arenas G := fun i=> actMark (A i) ( X i )
def breeze (A:Frames G)(p:ℝ→Cn)(B:ℝ→Frames G)(t:ℝ) : Frames G := fun i=> mirror (convertT t (A i)) * B t i * stepV (p t) (A i)
variable {A: Frames G}
local notation "V" => rendition X A
local notation "S" => breeze A p B
variable (hp:Touched X p B)(h:∀ i,Base (A i))
include hp h
lemma fare (t:ℝ)(d:ℕ): Base ( S t d ):= (((converts t _ ( h d )).rewind).mul (hp.paid t d)).mul ( ( h d ).switch ( hp.led t|>.real ) )
omit hp in
lemma freeze (t:ℝ)(d:ℕ): (convertT t (A d))*S t d=B t d * stepV (p t) (A d):= by rw [breeze,mul_assoc ( mirror _ ),← mul_assoc, (converts t _ (h d)).turn', one_mul]
lemma character (t:ℝ): Phase t V ( p t ) (S t):= fun d=> by unfold rendition; rw [pose_act, Facets.acts, freeze h t d, ← Facets.acts, hp.reads,Facets.team _ _ _ ((hp.led t).start) ] -- binder
-- unique at each horizon compatible timeframe.V reparam not needed.
lemma pulls : Unique V:= unique_through Scale.Tangent.unit X V A ( fun i=> by rw [ Facets.team_one ] ) hp.whole h
variable (H:∀ i j (u:i≤j),Walk u (A i) (A j))
include H
lemma growth : Touched V p S:= by refine ⟨ hp.led,fare hp h,character hp h,?_,pulls hp h⟩; exact fun t i j T=> (( ((H i j T).dial t).rewind (converts t _ (h _)) (converts t _ (h _)) ).mul ( hp.continues t T ) ).mul (( H i j T ).steps _)
omit H
-- Differentiated relation even for arbitrary implementation of precomposed frames
variable {U:ℝ→Frames G}{Q:Frames G}
variable {Γ Ψ: Guard G d}
lemma eligible (d:ℕ)(q:ℝ→Cn)(K:Touched V q U): q=p ∧ ∀ t:ℝ,U t d=S t d:= by
    have hz(t:ℝ): p t=q t∧ S t=U t:=Scale.once _ _ (hp.led _) (K.led _) _ _ K.whole _ _ (fare hp h t) (K.paid t) (character hp h t) (K.reads t); exact ⟨ funext fun t=>(hz t).1.symm, fun t=> congr_fun (hz t|>.2.symm) d ⟩
lemma adjust_by (q:ℝ→Cn)(K:Touched V q U)(f:Clear p)(c:Instant (fun i=>B i d) Γ 0)(e:Instant (fun i=>U i d) Ψ 0) : Γ * A d + Generator.Drive.central (beta p) (Generator.Drive.D (A d))= weight (A d)+ A d * Ψ:= by
    have hc:=(combine c (chart (Scale.Beta.origin p f) ( fun t=> (hp.led t|>.start) ) hp.ground.1 (A:=A d) )); have he:=(combine ( applyD (A d) ) e); rw [ hp.ground.2 d,one_mul,hp.ground.1, Scale.Frame.step_identity ] at hc; rw [ K.ground.2 d,mul_one, neutral,show (fun t=> _ * U t d)=(fun t=> B t d * stepV (p t) (A d)) from ?_ ] at he; exact hc.once he; exact funext (fun t=>by rw [ (eligible hp h _ q K).2 t, freeze h ])
omit hp h in
lemma tag_witness (g:ℝ→Guard G d)(T:Guard G d)(he:Instant g T 0)(hq:∀ t,Base (g t)): coeff 0 T=0:= he.zero_col 1 fun t=> (hq t).zero
-- later specialize. no hidden assumptions.
local notation "δ" => applyD
omit hp h in
lemma turn_rev (C:Guard G d)(H:Base C)(t:ℝ): mirror (convertT t C)=convertT t (mirror C):=(converts t _ H).alone (by rw [ ← Scale.commuting, H.turn' ]; exact old_g _ _ (Base.house.mpr Base.house₀))
/-- The generator obtained by the *matrix operation on derivatives at 0*.
    $N^{-1}(b N +β N' - [d,N])$; below shown equivalent to the expression
    using $𝖽-N^{-1}𝖽 N+N^{-1}b N+N^{-1}βN'$. -/
def casting (A:Guard G d)(p:Cn)(X:Guard G d) := mirror A * ( X*A+ Generator.Drive.central p ( Generator.Drive.D A ) - weight A )
omit hp h in
lemma cast_on (C:Guard G d)(p:Cn)(X:Guard G d)(H:Base C) : casting C p X= ( PowerSeries.C ( bill d ) - mirror C * PowerSeries.C ( bill d ) * C ) + mirror C * X * C + mirror C * Generator.Drive.central p ( Generator.Drive.D C ) := by
    -- distribute. Have explicit ring patch
    have he {A: Type} [Ring A] (x y z:A): x * (y-z)= x*y - x*z:= mul_sub ..
    rw [ casting, he (mirror C), mul_add, weight, he (mirror C), ← mul_assoc ( mirror C ) ( PowerSeries.C _ ),← mul_assoc (mirror C) C, H.turn,one_mul ]; rw [mul_assoc ( mirror C ) X]; abel -- check
omit hp h in
lemma derivative_eq {A : Guard G d}{F:ℝ→Guard G d}(h:Instant F A 0): engine F=A:= by unfold engine; split_ifs with h'; exact (h'.choose_spec (p:=fun q=>Instant F q 0)).once h; exact False.elim ( h' ⟨ A,h ⟩ )
-- Any compatibility p.B. Show candidate F chosen by breeze INSTANT using independent witness above algebra
include H
lemma casted_c (f: Clear p)(g: Instant (fun i=> B i d) Γ 0): Instant (fun i=> S i d) ( casting (A d) (Scale.Beta.beta p) Γ ) 0:= by
    have hu := ( combine (combine (applyD (mirror (A d))) g) ( chart ( A:= A d ) (Scale.Beta.origin p f) ( fun t=> (hp.led t|>.start) ) hp.ground.1 )); let Fp i:= S i d; let Δ:= Scale.Beta.beta p
    have hm : (fun t=> convertT t ( mirror ( A d ) ) * B t d * stepV (p t) ( A d ))=Fp:= by unfold Fp breeze; simp_rw [ turn_rev _ (h d) ] -- arguments maybe unused
    rw [ hm ] at hu; -- use adjust_by
    have he:= adjust_by hp h p ( growth hp h H ) f g hu; -- uses ΓS auto
    convert hu using 1; unfold casting; rw [ he ]; -- simplify ring
    let Q:= (weight (mirror (A d)) * B 0 d + convertT 0 (mirror ( A d )) * Γ ) * stepV (p 0) (A d) + convertT 0 (mirror (A d)) * B 0 d * Generator.Drive.central (Scale.Beta.beta p) ( Generator.Drive.D (A d) ); -- association?
    rw [add_comm ( weight ( A d ) ), add_sub_cancel_right (A d * Q) (weight (A d)), ← mul_assoc, (h d).turn,one_mul ]; -- arg
end YM.FVA2.Clef
