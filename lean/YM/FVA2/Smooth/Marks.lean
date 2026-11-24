import YM.FVA2.Smooth.Lifetime
import YM.MS.Dial.Reg
/-!
# Insert multiple external momentum factors in the MS continuum kernel

Building operators using `force` at specified marks. Prove they satisfy the
`Fields` validation here and consequent pricing (`verdict`). Thus able to
work on all separated-point derivative orders (`Smooth/Point` and `DerivD`).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Smooth.Slots
open Set Function Filter Finset Metric MeasureTheory Real
open MS MS.Plane MS.Koszul MS.Landau MS.Landau.Detect MS.Heat MS.Tone MS.Latch MS.Latch.Job MS.Rake
open MS.Book MS.Book.Convolve MS.Plane.Flux MS.High MS.Rake.Geo MS.Vane MS.Vista MS.Motif MS.Plane.Wire
open MS.Tone.Frame MS.City MS.Osc MS.Osc.Snap Belt
open MS.Land MS.Local.Physical MS.Dial MS.Port
open Lifetime
open Complex (I)
open scoped Topology ContDiff BigOperators Interval Classical
variable {W I : Type}{G:Gauge}{P Q:Geo I}{b:Deck G}{M:Booked b}{L:Belt I}
local notation "ℳ"=> (fun (_:I)=>planeF)
local notation "Δ"=> Rake.Geo.constantP G I (PlanetD G)
variable (S:MS_Data G M) (μ:ℝ) (σ : List Axis)
def chargeF (A: Rake.Site G I): List Axis → Rake.Site G I
 | []=> A
 | i::l => fun j=> force i (chargeF A l j)
abbrev beamH (S:MS_Data G M)(P: Geo I)(p: Rake.Label b):= chargeF ( rowM P S p )
variable (P)
local notation "Ω"=> approach P S
lemma ready (x:Rake.Label b)(l:List Axis)(j:ℕ): Tip P false false (x.h+l.length) ( beamH S P x l j ) := by
 induction l with| nil=> exact tagF P S x j| cons i l ih=> exact Lifetime.marks_h i ih
lemma willing (x:Rake.Label b)(l:List Axis): Ven ℳ Δ Δ (approach P S) ( beamH S P x l ) := by
 induction l with| nil=> exact VeniceD P S x| cons i l ih=> exact venH i Δ Δ Ω _ ih
-- any rank any W.Ball.Sturdy.
variable (u:W→Rake.Label b)
local notation "C"=> W→List Axis
abbrev Hmark (f:W→Rake.Label b)(u:C)(w:W):= (f w).h+(u w).length
def att (L:C)(i:W):= beamH S P (u i) (L i)
variable (s:W→ List Axis) [LinearOrder W]
local notation "Χ"=> att P S u s
local notation "υ"=> Hmark u s
variable (x:Position W I)
-- Lean type meta. Need disamb Position with YM.FVA2.Position namespace (not type)
omit [LinearOrder W] in
lemma toTour (hx:Mesh P x): Tour Δ Δ P x false Ω Χ υ:= ⟨ hx, masterD .., fun _ _=> tagD P S _, fun _ _n=> ready P S _ _ _,fun _=> willing P S _ _⟩
lemma arch (l:Belt I)(h:Gold P l): Arch l Δ Δ Ω Χ υ := by
 let a:= Dial.Architect ( b:=S ) u l h; refine ⟨ a.main,a.χ,a.states,fun i n=>?_ ⟩;
 suffices he: ∀ s:List Axis, Here false false l (beamH S P (u i) s n) ( rateS l ( ((u i).h+s.length:ℕ):ℤ ) ) from he _; intro s; induction s with
 | nil=> exact a.first i n
 | cons i l ih=> exact step_price i _ _ ih
local notation "χ"=> Rake.Dance G I W
def charted (Y:Rake.Dance G I W): Prop:= Fields x ℳ Δ Δ Ω Χ Y
def curve (L:C): χ:= story x ℳ Δ Δ (approach P S) ( att P S u L )
omit [LinearOrder W] in
lemma twisting (u:I→ℝ)(s:ℤ)(F:Rake.Glade G I)(i:Axis): force i (twist s u F)=twist (s+1) u (force i F):= by
 funext j k w; change turn i (net w)*(Port.τ ( pitch w - s ) (u j)*_)=_
 change _= Port.τ (pitch w -(s+1)) (u j)*(turn i (net (Alps.sr (u j) w))*F _ _ _)
 rw [ Alps.net_sr, _root_.map_smul ]; simp only [Complex.real_smul]; let z:=Port.τ (pitch w-(s+1)) (u j); rw [ show Port.τ ( pitch w - s ) (u j)=z*(((Real.exp (u j)):ℝ):ℂ) from ?_ ]; · ring
 rw [show (((Real.exp (u j)):ℝ):ℂ)=Port.τ 1 (u j) from (?_) , show z= _ from rfl, T_add ]; congr 1; omega; simp [Port.τ]
variable {P}
local notation "θ"=> charted P S u s x
lemma arrived (h:Mesh P x): charted P S u s x (curve P S u x s):= by
 refine ⟨ st_0 ..,fun _=> st_u ..,fun U hx n=>?_ ⟩; apply (Rake.stage ( masterD G I P ) h ( ( toTour P S u s x h ).energy ) ?_ U (Finset.card_pos.mp (by omega)) n |>.2 hx).2; -- inspect
 intro t n; exact ⟨ _,(toTour P S u s x h).obey t n⟩
lemma verdict {Y: Rake.Dance G I W} (h: Mesh P x)(he: charted P S u s x Y)(l:Finset W)(hh:l.Nonempty)(n:ℕ): Verdict P ( charge (Hmark u s) l) 0 (Y l n):= Vane.closure (toTour P S u s x h) (arch P S u s (Gulf P) gulfG) (arch P S u s (West P) westV) he hh n
omit [LinearOrder W] in
lemma rowT (b:I→ℝ)(h:∀ i, Q.η i=P.η i+b i)(t:Rake.Label ‹Deck G›): beamH S P t σ= glide ( beamH S Q t σ ) b ( (t.h + σ.length :ℕ) :ℤ ) := by
 induction σ with| nil=> exact hoof S h _ | cons i l ih=> funext n; change force i (beamH S P t l n)= _; rw [ ih ]; exact twisting b _ _ _
lemma traveled {Y:Rake.Dance G I W}(b:I→ℝ)(h:∀ i, Q.η i=P.η i+b i)(he:charted Q S u s x Y): charted P S u s (moved b x) ( loom b (Hmark u s) Y ):= by
 obtain hv:= steer b ( Hmark u s ) x he; rw [ fees S h ] at hv; unfold charted; rw [ show att P S u s=(fun i=> glide (att Q S u s i) b ((Hmark u s i):ℤ)) from funext fun i=> rowT S (s i) b h (u i) ]; exact hv
end YM.FVA2.Smooth.Slots
