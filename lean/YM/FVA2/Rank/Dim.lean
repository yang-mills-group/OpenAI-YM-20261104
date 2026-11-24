import YM.FVA2.Rank.Camp
/-! # Apply slot parity to Mell via point evaluations before epsilon elimination. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Position.Glazer
open Function Set Filter Finset MeasureTheory
open MS MS.Plane MS.Momentum MS.Arts MS.Arts.Spin MS.Landau MS.Koszul MS.Landau.Detect
open MS.Book MS.Arc MS.Garment MS.Rock MS.Motif MS.Outlook MS.Plane.Wire MS.Alps
open MS.Rock.Path MS.Rock.Oceans MS.Plum MS.Hem MS.Dock MS.Train MS.Pearl
open _root_.YM.MS.Shine Brass MS.Color
open Complex (I)
open scoped Topology ContDiff BigOperators Classical
open Hue MS.Hem.Mell
variable {J:Type}{m n k:ℕ}{G:Gauge}
variable {X Y:Rack G m}{A B F: Mob G}{f:ℂ→Mob G}{U:Rip G} {b:Bool} {r q:ℤ}
lemma plow_t (x:ℂ)(t:ℝ): plow x t ((hue G) F)= (hue G) (plow x t F):= by ext l i; rw [ spark ]; dsimp only [plow]; rw [ spark ]; simp only [sr,List.length_map]; exact mul_left_comm ..
lemma nervous {i:ℂ}(h:Mell.Trail A B i): Mell.Trail ((hue G) A) ((hue G) B) i:= by refine ⟨ fun t=>?_⟩; intro m w; simp_rw [ plow_t,spark ]; exact (h.derive t _ w).const_mul _
lemma station (h:Home F k): Home ((hue G) F) k:= by intro x; rw [plow_t,h x]
lemma W {L:Filter J}{v:J→ Mob G}(h:Wind v L F): Wind ((hue G) ∘ v) L ((hue G) F):= by intro m l; simp_rw [Function.comp_apply,spark]; exact ( h m l ).const_mul _
lemma cone_t (h:Cool f): Cool (fun i=>(hue G) (f i)):= by
    let Q:= tapeL (G:=G) (fun _=>(hue G)); suffices he: cone G ≤ Submodule.comap Q (cone G) from he h; refine Submodule.span_le.mpr ?_; rintro f ⟨m,h,F,rfl⟩; change Cool (fun i=>(hue G) ( Ice m F i )); simp_rw [Ice,map_smul]; exact iceC _ m h
-- `Flats` = stores arbitrary ℓ, fixed each rank.)
def sock (G:Gauge) : Coat G→ₗ[ℂ] Coat G:= tapeL fun _=> (hue G)
def tints (G:Gauge) : Flats G→ₗ[ℂ] Flats G:= blast 0 (sock G)
lemma coat_x (f:Coat G)(x:ℂ): sock G f x=(hue G) (f x):= rfl
lemma tones (F:Flats G)(x:ℕ): ( tints G F ) x= sock G (F x):=blade 0 F (sock G) x
lemma tonal (F:Coat G)(i:ℕ): tints G (Finsupp.single i F)=Finsupp.single i (sock G F):= blast_sl ..
variable {X Y P: Flats G}{p f: Coat G}
lemma clash (h:ClockD b q r X): ClockD b q r (tints G X):= by intro i; rw [tones]; exact top (h i)
lemma sky_t (h:Vibe k X Y): Vibe k (tints G X) (tints G Y):=by filter_upwards [h] with i hi l; rw [tones,tones]; exact nervous (hi l)
lemma billow {f:Coat G}(h:Return X f k): Return (tints G X) (sock G f) k:= by filter_upwards [h] with i hi; simp_rw [tones,coat_x, plow_t]; exact W hi
lemma ticket_y (f:Mob G)(x:ℂ)(h ℓ:ℕ)(y t:ℝ) : hikeP x h ℓ y t ((hue G) f)= (hue G) (hikeP x h ℓ y t f) := by unfold hikeP; rw [plow_t,map_smul]
lemma card (F:Flats G)(x:ℂ)(h:ℕ)(y u:ℝ): Parade (tints G F) h y u x= (hue G) ( Parade F h y u x ):= by
 induction F using Finsupp.induction_linear with -- syntax
 | zero=> simp_rw [map_zero,pageZ,Pi.zero_apply,map_zero];
 | add X Y hx hy=> simp only [map_add,page_add, Pi.add_apply,hx,hy]
 | single i A=> rw [tonal,page_sl,page_sl]; exact ticket_y ..
lemma Direct (h:Joint k P X f p): Joint k (tints G P) (tints G X) (sock G f) (sock G p):= by
 refine ⟨ sky_t h.advance,fun y t=>?_, ?_, cone_t h.ice, hot h.worth, fun i=> station (h.back i), by rw [← map_add]; exact billow h.sip⟩
 · rw [funext (card X · k y t) ]; exact live (h.toll y t)
 intro m; rw [tones]; exact hot (h.wet m)
end YM.FVA2.Position.Glazer
