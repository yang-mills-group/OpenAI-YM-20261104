import YM.FVA2.Position.Brass
/-!
# Preserving the meromorphy requirements of MS under H rotation

In particular prove `floorS`: the `hoop` action commutes with the analytic continuation
of loops in the supplied MS construction (their `Town` convention etc.). The proof works even with those
detailed Form/Knot mathematical assumptions from the supplied calculus. This permits the
averaging/uniqueness arguments without any additional pole-choice assumptions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Position.Park
open Function Set Filter Finset MeasureTheory
open MS MS.Heat MS.Plane MS.Momentum MS.Arts MS.Arts.Spin MS.Landau MS.Koszul
open MS.Arc MS.Garment MS.Rock MS.Motif MS.Outlook MS.Plane.Wire
open MS.Rock.Path MS.Rock.Oceans MS.Plum -- name.
open Brass -- Weft lamp collides
open Complex (I)
open scoped Topology ContDiff BigOperators Classical
variable {J:Type}{m n:ℕ}{G:Gauge}(s t:Signed)
variable {X Y:Rack G m}{A B F: Mob G}{f:ℂ→Mob G}{U:Rip G}
-- kernel on all dimensions. right action
abbrev hoop : Mob G→ₗ[ℂ] Mob G where
 toFun F m:= Brass.cash s m ( F m)
 map_add' F G:= funext fun m=>map_add _ (F m) (G m)
 map_smul' i F:= funext fun m=> map_smul _ i (F m)
local notation "L₀"=> hoop s
lemma hop (w:Legs (Shore G m)): hoop s F m w = (Brass.Track s w:ℂ)* F m (Brass.rack s w):= Brass.evaluate ..
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
abbrev rolls (G:Gauge)(m:ℕ)(E:Type)[ NormedAddCommGroup E][NormedSpace ℝ E]:= Wire (Cfield G m) E (SectorP m)
def spoor (w: rolls G m E): rolls G m E:= w.map (fun i=> (toward s i.1,(viewD s m).turn.toContinuousLinearMap.comp i.2))
lemma sails (w:rolls G m E)(x:E): Brass.rack s (sail w x)=sail (spoor s w) x:=by unfold Brass.rack sail spoor; simp only [List.map_map]; rfl
lemma trace_p (w:rolls G m E)(x y:E): Brass.Track s (sail w x)=Brass.Track s (sail w y):= by unfold Brass.Track sail; simp only [List.map_map]; rfl
lemma rolling {z:UScale J}{f:J→Mob G}{a:J→ℝ}(h:fell z a f): fell z a (fun i=>hoop s (f i)) := by
 intro m E _ _ _ w; unfold fieldVal; simp_rw [hop,sails,fun x:E=> trace_p s w x 0]; exact (h m E (spoor s w)).L (ContinuousLinearMap.mul ℝ ℂ ( (Brass.Track s (sail w 0) :ℝ):ℂ ))
lemma flows (h: Form0 false F): Form0 false (L₀ F):= ⟨rolling s h.price, Weft.strong _ F h.token⟩
lemma holS {D:Set ℂ}(h:Hol D f): Hol D (fun i=>L₀ (f i)):= by refine ⟨fun c R hX hY=> rolling s (h.price c R hX hY),fun m l c hc=> ?_⟩; simp_rw [hop]; exact (h.top m _ c hc).const_mul _
lemma frame (h: Sync false f): Sync false (fun i=>L₀ (f i)):= ⟨ ⟨h.eye.price.elim fun u ⟨hu,hg⟩=> ⟨u,hu,rolling s hg⟩, holS s h.eye.sky⟩, fun i hi=> Weft.strong _ ( f i ) (h.vote i hi) ⟩
lemma shoot (hU:Knot true U)(F:Rack G m)(h: Pass (U m) F (Px m)): Brass.cash s m (Ccy (U m) F (Px m))=Ccy (U m) (Brass.cash s m F ) (Px m):= by
 let W:=flagS (viewD s m) G; exact Pilot.leadC W (viewD s m).volume (viewD s m).turn.toHomeomorph.measurableEmbedding (hU.token.turn m (viewD s m) (fun i=> Bool.noConfusion i)) F h
lemma lesser (hu:RockB U true) : RockB U false:= ⟨ hu.toKnot.clearer,hu.gear ⟩
lemma oceans (h: RockB U true)(hp: Form0 false F)(i:ℂ)(hi:i∈Town): hoop s (ocean i U F)= ocean i U (hoop s F):= by
 let Q:= lesser h; refine Sync.drape (frame s (Q.volume0 hp.sync)) (Q.volume0 (flows s hp).sync) (fun n=>?_) hi; change (Brass.cash s n) (ocean n _ F n)=_
 rw [lamp Q hp.sync n,lamp Q (flows s hp).sync n, Rock.LinearMapRealm, shoot s h.toKnot (F n) ( theory hp.price h.price n ) ]; rfl
lemma floorS (h: Knot true U)(hp:Form0 false F)(i:ℂ)(hi:i∈Town): hoop s (ocean i U F)= ocean i U (hoop s F):= by
 let T:= newer h.clearer; funext m l; let X(n:ℕ):= twine (fade n) U
 have hx : ∀ n, hoop s (ocean i ( X n ) F)=ocean i (X n) (hoop s F):= fun n=> oceans s (tried h (fade n ) (being n) (sold n)) hp i hi
 obtain he := lean (carries (steak hp) T hi) (Brass.rack s l); have hv:= lean (carries (steak (flows s hp)) T hi ) l
 -- limit
 obtain hb:Tendsto (fun n=>hoop s (ocean i (X n) F) m l) atTop (𝓝 ( hoop s (ocean i U F) m l )):= by simp_rw [ hop ]; exact he.const_mul _
 simp_rw [hx] at hb; exact tendsto_nhds_unique hb hv
end YM.FVA2.Position.Park
