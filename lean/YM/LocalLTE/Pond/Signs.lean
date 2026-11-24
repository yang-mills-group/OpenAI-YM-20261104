import YM.LocalLTE.Pond.Colors
/-! Budget handoff, oxidizing pre+post affines. No receptive assumptions on stencil prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Collection.Price
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf
open LocalLTE.FrameBox LocalLTE.FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable (G : Gauge) {n : Side} {j:ℕ} {C V: ℝ}
attribute [local instance] Gauge.frobInner
-- uniform over all low rows. weights only station 
open Residual Geo Animals
open Quotes
variable {G}
variable {w : ℕ} {κ k :ℝ} {a:RegularAddress n}
def Art.turn (A:Art a w) (s : Seat n) (y:RegularAddress n)(hs:y.site=affine s.1 s.2 a.site)(hp:y.support=s.spread a.support): Art y w := {
    grove:=by rw [hs]; exact Hall.transplanted s.1 s.2 A.grove
    radius:=A.radius
    crisp:=hp.trans (by rw [A.crisp]; exact Scarf.normRange hs w)
    hearth:=A.hearth
    bonus:= A.bonus }
-- coefficients commute reanchor.Consequence existence at ALL angular.w.
variable (A:Art a w) {g:Config G n→ℝ}
lemma translatedPoly {o i:Site n} (s:Seat n)(G' : Grove o)(n:ℕ)(hp:i=affine s.1 s.2 o)(hr:Reliable G κ k)(h:Replicated G' n κ w g) : let X:Grove i:=by rw [hp]; exact Hall.transplanted s.1 s.2 G'
    Replicated X n κ w (g∘ s.view):=by
    subst i; obtain ⟨P,h⟩:= h; intro X; rw [h]; exact ⟨_,Hall.packet s.1 s.2 G' hr _ P⟩
lemma rotatedG (i:ℕ)(s:Seat n)(y:RegularAddress n)(hs:y.site=affine s.1 s.2 a.site)(hp:y.support=s.spread a.support)(hr:Reliable G κ k)(h:Replicated A.grove A.radius κ i g) : Replicated (A.turn s y hs hp|>.grove) (A.turn s y hs hp|>.radius) κ i (g ∘ s.view):= translatedPoly s A.grove _ hs hr h
variable (R:PathData G)(P:BudgetPoint)(X:Listing G n) (d:ℕ)(V:Tour X d)
def pruned (i:ℕ) : Option (Σ z:ℕ,Art (tubeX R P X (.inl i)) z):= Option.map (fun (v:Art (X.reg i) d)=>⟨d,⟨v.grove,v.radius,extents v,v.bonus,v.hearth⟩⟩) (V i)
def painting (h:3 ≤ P.B)(i: Spikes n)(hx:High.length R i.2 < P.B) : Art ⟨(0:Site n),bloomH R P 0 i.2, erect _ _ _ _ (High.small_home ..)⟩ (2*P.B) where
   grove:=cane _
   radius:= P.B
   crisp:= if_pos hx
   bonus:= by omega
   hearth:= by omega
def sights (h:3 ≤ P.B)(i:Faces n)(hx:Low.length R i.2 < P.B) : Art ⟨(0:Site n),i.2.home R P 0,Low.small_home ..⟩ P.B where
   grove:=cane _
   radius:= P.B-1
   crisp:= tightL P R 0 i.2 hx.le
   bonus:= by omega
   hearth:= by omega
lemma ridgeLoc (i:Spikes n) : (Price.ridge R P i).site=affine i.1.1 i.1.2 (0:Site n):=by simp [ridge,Lattice.affine, Seat.reg] -- omit
lemma lowLoc (i:Faces n) : (lowEntry G R P i).site=affine i.1.1 i.1.2 (0:Site n):=by simp [lowEntry,Lattice.affine,Seat.reg]

def gallery (h:3 ≤ P.B)(i:EKey n) : Option (Σ z:ℕ, Art (Price.tubeX R P X i) z):=
   match i with
   | .inl x => pruned R P X d V x
   | .inr (.inl x) => if hz: Low.length R x.2 < P.B then Option.some ⟨P.B, Art.turn (Price.sights R P h x hz) x.1 _ (lowLoc R P x) rfl⟩ else Option.none
   | .inr (.inr x) => if hz: High.length R x.2 < P.B then Option.some ⟨2*P.B, Art.turn (Price.painting R P h x hz) x.1 _ (ridgeLoc R P x) rfl⟩ else Option.none

variable {f:ℕ→ Config G n→ℝ}
lemma alikeness (h:3 ≤ P.B) (j:ℕ)(hr:Reliable G κ k)(c:Clip)(hv:Portrays X d κ j f V)(hx:2*P.B ≤ d)(α Δ:ℝ) : Alike _ (Price.tubeX R P X) (Price.vane R c P X d V κ α Δ j f) κ (Price.gallery R P X d V h) j d:=by
    rintro (i|i|i)
    · cases hs: V i with
      | none=>
         rw [show Price.gallery R P X d V h (.inl i)=none from (by simp [gallery,pruned,hs])]; exact ⟨fun _=> (by simp only [vane,Sum.elim_inl,hail,hs]; rfl),fun _ _ H=>  by cases H⟩
      | some A'=>
         have ht:Replicated A'.grove A'.radius κ (pie j+1) (Price.vane R c P X d V κ α Δ j f (.inl i)):= by
             simp only [vane,Sum.elim_inl,hail,hs]; exact Price.quake _ _ _ (hv.frame i _ hs)
         let B: Art (Price.tubeX R P X (.inl i)) d:= ⟨A'.grove,A'.radius,extents A',A'.bonus,A'.hearth⟩; have hz: gallery R P X d V h (.inl i)=Option.some ⟨d,B⟩:=by unfold gallery; simp [pruned,hs]; rfl -- edit
         rw [hz]; refine ⟨fun H=>  (by cases H),fun z Q h=>?_⟩; have hx:= Option.some.inj h; obtain ⟨rfl,rfl⟩:= Sigma.mk.inj hx; exact ⟨le_rfl,ht⟩
    · unfold gallery; dsimp only; split
      next hz =>
       refine ⟨fun H=> (by cases H), fun z Q h'=>?_⟩; have hX:= Option.some.inj h'; obtain ⟨rfl,rfl⟩:= Sigma.mk.inj hX
       refine ⟨by omega, rotatedG (Price.sights R P h i hz) (pie j+1) i.1 _ _ rfl hr (g:=swan R c P j κ 0 _ i.2) ?_⟩ -- edit
       unfold swan; rw [if_pos hz]; exact ⟨_,rfl⟩
      next hz=> exact ⟨fun _=> by simp only [vane,Sum.elim_inl,Sum.elim_inr,swan,if_neg hz]; rfl, fun _ _ h=>  by cases h⟩
    unfold gallery; dsimp only; split
    next hz=>
         refine ⟨fun H=> (by cases H), fun z Q h'=>?_⟩; obtain ⟨rfl,rfl⟩:= Sigma.mk.inj (Option.some.inj h'); refine ⟨hx,rotatedG (Price.painting R P h i hz) (pie j+1) i.1 _ _ rfl hr (g:=craneH R P j κ 0 _ _ i.2) ?_⟩ -- edit
         unfold craneH; rw [if_pos hz]; exact ⟨_,rfl⟩
    next hz=> exact ⟨fun _=> by simp only [vane,Sum.elim_inr,craneH,if_neg hz]; rfl,fun _ _ h=>  by cases h⟩
end YM.AnalyticBridge.VerifiedReset.Collection.Price
