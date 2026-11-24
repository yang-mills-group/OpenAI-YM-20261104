import YM.GradedFar.Round.Geometry
import YM.GradedFar.Round.H

/-!
# Grid C5 input of the supplied proof

Exact statement of the portions used, along random T in the Sense.
Do not presume C5 on unrounded two-zone uses even in the continuum.
-/
namespace YM.FVA2.GradedFar.Physical.Round
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh
open Moving Growth Pose Books Scale Dframe Jury Facets
open Continuation Continuation.Window
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n m h k t p : ℕ} {I V:Type} {d : Fin n → ℕ}{e: Fin m→ℕ} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple} {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
local notation "ν"=> Teller.logNu 1
local notation "α"=> Measure.adjust N.scheme N.criterion
variable {R : Family G} {f : Extraction.Order} {P : Table R.book}
    (U : Spec.Final R f P) (J K : FramesH P)
local notation "F"=> familyPoint U J
local notation "Fρ"=> familyPoint U K
-- hypothesis, not theorem; user continuation
/-- **Prior physical input** on which this (G.9) result rests, in addition to
`Ample` compact input. PoseFit C5 on the **grid points**; already uses the geometry
purchase of line `1655` (and the `r`-shape rounding cost there, at each
needed exponent A). No claim to prove earlier Preparation, program-specific
(f-grid buys), period prices etc. Supply the functions Z,V by rounding to
those grid points of the book. It suffices to have two tables with these
properties. Need not stipulate the values at bad w (requests made eventually).
Using all `r`-HATS in true voter W. Stating quantifiers on shapes and all t'
&m (see RoundMeter and F3 lines of proof; these are continuum hypotheses of
the earlier lemmas of the supplied proof). `Grid` doesn't assume (G.9)'s
estimate holding at same unrounded x, Ty. Neither use H cells or change on
merely guessed position calendar. `A` finite polynomial exponent any
chosen before booking. Homogeneous-at-cap-h later will reduce to actual caps
of `X`, `Y`. Read also empty arguments (as in Pose & books).

Need C5 once with these budgets, one orientation. In fact S.pt comparison
through all compact labels `a:Tags G h (n+m)` in final line can do on finitely
many (any basis, then extend by multilinearity). Relative t'∼g hypothesis is from
line `1337`. (F.2),(F.3) *consequences* applied via `Round.Sign` (not premises).
-/
def Grid : Prop := ∀ B C:ℝ,0<B→ 0<C→ ∀ (n m h p A:ℕ), 6≤h → 1≤p →∀ (X:Set (Points n))(Y:Set (Points m)),
    IsCompact X → X⊆conf n → IsCompact Y→ Y⊆Outside m→
    let T:= Continuation.Window; let Q:=upper G C B; let L:=g∘Window.len; let f:=windows Q
    ∃ (q k:ℕ)(t:T→ℝ)(D:T→Normalize.Change G h)(E:T→Normalize.Change G 6) (Z:T→XSet X Y→Points n)(V:T→XSet X Y→Points m),
      May G Q (XSet X Y) (fun i=>i.1.val) (fun i=>i.2.val) Z V A ∧ p≤q ∧ p+1≤k ∧
        Tendsto (fun i=> t i/L i) f (𝓝 1) ∧ Tendsto (fun i=> guide G h (D i)) f (𝓝 0) ∧
        Tendsto (fun i=>guide G 6 (E i)) f (𝓝 0) ∧
        (∀ a:Fin (N.store.survey 6).n, let u := (N.store.survey 6).scope a
         Notice N f Window.len q k (familyPoint U J 6) t E (tsupport u.t) u.p) ∧
        (∀ s:XSpace.Rose.Badge,
         Notice N f Window.len q k (familyPoint U J 6) t E (tsupport (XSpace.Rose.test N.criterion))
            (XSpace.Rose.missing (XSpace.Rose.tag G) s)) ∧
        (∀ a: Fin (N.store.survey h).n, let u:=(N.store.survey h).scope a
         Notice N f Window.len q k (familyPoint U J h) t D (tsupport u.t) u.p) ∧
        ∀ a:Tags G h (n+m), Terms f (fun i=> L i^k) (fun w i=> familyPoint U J h (Window.len w) (n+m) (along w (Z w i) (V w i)) a -
            crop q (t w) (Pose.line N (along w (Z w i) (V w i)) (stand (D w)∘a)))
variable (E : (d:ℕ)→ℝ→FieldEnd G d) (R' : (d:ℕ)→ℝ→ Prediction G d) (θ : ℝ→ℝ)
    (W : Bookshelf N U J K E R' θ) (Q : Earned N M U J K θ)
    (hq : ∀ᶠ r in τ,∀ u : Sec G h,K r h u= J r h (E h r u))

/-- Use on any comap-filter along w (with more stock parameters, as needed). -/
def Duly (Q:Set Continuation.Window)(T:Filter I)(p:I → Continuation.Window)(hp:Tendsto p T (windows Q))(simple:G.Simple) : Board I :=
   let b:= boarded simple Q
   { l:=T, «g»:=b.g∘p, s:= b.s∘p, spacious:= b.spacious.comp hp, positive:=hp.eventually b.positive, shrinking:=b.shrinking.comp hp }
variable (hGrid : Grid N U J) {C B:ℝ}(hB:0<B)(hc:0<C)
    {X:Set (Points n)}{Y:Set (Points m)}
    (hX:IsCompact X)(hx:X⊆conf n)(hY:IsCompact Y)(hy:Y⊆Outside m)(hz:6≤h)
include hGrid H hq W Q hX hx hY hy hz hc hB
local notation "Q₀"=> upper G C B
local notation "Ξ"=> XSet X Y
local notation "g₀"=> gYM G ∘ Window.len
local notation "Γ"=> windows Q₀
/-- Get PhaseFit currency (F.3) on this booking, including log projection union
from the actual same calls. It prices the comparison on those (rounded) positions. -/
theorem booked_grid (A p:ℕ)(hp:1≤p) :
   ∃ (Z:Continuation.Window→ XSet X Y→ Points n)(V:Continuation.Window→ XSet X Y→ Points m),
    May G Q₀ (XSet X Y) (fun i=>i.1.val) (fun i=>i.2.val) Z V A ∧
    ∀ (T:Filter I)(w:I→ Continuation.Window) (hw:Tendsto w T Γ)(q:I→XSet X Y)
      (X':Set (Points n))(Y':Set (Points m)), IsCompact X' → X' ⊆ conf n → IsCompact Y' →Y'⊆ Outside m→
       ∀(P:I→ XSet X' Y'),(∀ᶠ i in T, Z (w i) (q i)=(P i).1.val ∧ V (w i) (q i)=(P i).2.val)→
       ∀ a:Tags G h (n+m),
        let t (i:I):= along (w i) (Z (w i) (q i)) (V (w i) (q i)); let r:=Window.len∘w
        Bill (Duly Q₀ T w hw simple) (p+1) 0 (fun i=> (familyPoint U K h (r i) (n+m) (t i) a- crop p (θ (r i)) (boundary N a (t i)))) := by
   obtain ⟨q,k,t,D,A',Z,V,H0,hp',hk,ht,hD,hE,P,E,P',V'⟩:= hGrid B C hB hc n m h p A hz hp X Y hX hx hY hy
   have hV : Buys Γ (fun i=>guide G 6 (A' i)) g₀ k:= targeted N M H Γ _ (windows_short _) (W.fixed _) ht hE q k (N.store.survey _) P
   have hU : Buys Γ (fun i=>guide G h (D i)) g₀ k:= targeted N M H Γ _ (windows_short _) (W.fixed _) ht hD q k (N.store.survey _) P'
   have he:Buys Γ (fun i=> (θ (Window.len i):ℂ) - (t i:ℂ)) g₀ (p+1) := by rw [W.known]; exact received N M H Γ Window.len (windows_short _) ht (W.fixed 6) q k hp' hk hp hV E
   refine ⟨Z,V,H0,fun T w hw r X' Y' hx hx' hy hy' R hR a=>?_⟩
   let z i:= along (w i) (Z (w i) (r i)) (V (w i) (r i)); let p':= Window.len ∘ w; let b:=Duly Q₀ T w hw simple
   have hr : Tendsto p' T τ:=(windows_short _).comp hw
   have hR':∀ᶠ i in T,z i=flute (R i) (b.s i):=hR.mono fun i hi=> by unfold z; change _=flute _ (Window.sep (w i)); rw [hi.1,hi.2,to_along]
   have hh a: Priced b p (θ∘p') 0 (fun i=> familyPoint U J h (p' i) _ (flute (R i) (b.s i)) a) (fun i=> Pose.line N (flute (R i) (b.s i)) a) := by
      apply before_sale N M H hx hx' hy hy' b p' hr rfl k q hp' hk (Y:=fun i v=>familyPoint U J h (p' i) _ (flute (R i) (b.s i)) v) (t':=t ∘w) (D':=D∘w) (ht:=ht.comp hw) _ ((hr.eventually (paid_reading simple θ Q.clock)).mono fun i h=> h.2.2.2) (he.comp_tendsto hw) (hU.comp_tendsto hw)
      have he0 : Buys T (fun i=>familyPoint U J h (p' i) (n+m) (z i) a- crop q (t (w i)) (Pose.line N (z i) (stand (D (w i))∘a))) (g₀ ∘w) k := IsBigO.comp_tendsto (V' a) (show Tendsto (fun i=>(w i,r i)) T (comap Prod.fst Γ) from tendsto_comap_iff.mpr hw)
      exact he0.congr' (hR'.mono fun i h=> by dsimp [comp_def]; rw [h]) (EventuallyEq.refl ..)

   exact (just_payment N M H U J K _ R' θ W Q hq b p' R hr rfl p a hh).2.apply_eq (hR'.mono (fun i h=> by change _=familyPoint U K _ _ _ (z i) a - crop _ _ (boundary N a (z i)); rw [h]; rfl))
end
end YM.FVA2.GradedFar.Physical.Round
