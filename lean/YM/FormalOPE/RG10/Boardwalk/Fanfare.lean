import YM.FormalOPE.RG10.Boardwalk.Trellis
/-! # Power accuracy on k-frame orientation (prior to regulator alignment checks)
 Apply `bands` first at near-stock and the queries at that same height; even bootstrap with
 divergent raw origins doesn't formally cost when using this credited preprocessing. Then
 prep of 6's whole connected list, earning also quantitative stability through the Peal
 **re-solve** of coupling. Slope limit at common $g_k$ procedure from comparisons is genuine
 input! May differ depending on convention but in WilsonX that limit should be 1. Keep ℝ for
 canonical Stock tests as earlier (not β actual). -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.Boardwalk.Trellis
open Filter Function Finset PowerSeries Clearing Ledger Rates InversionTop
open Carryon PertExtension Position Maxwell Labels Extraction Filter Extra.FD
open PertExtension MeasureTheory Topology Metric PertExtension.Position Triangle Lawn
open RG10.Profile Gliss Gazebo Matrix Position.Grade Peal
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge}{F:Frames G}{I:Type*}{l:Filter I}{P:Path l}{r d n:ℕ}
variable {D:Stock F}
local notation "Ψ" d=>Mark (Deck F d) PertExtension.Physical.Profile.n
local notation "κ" d=>Deck F d
local notation "ins" d=>PertExtension.Position.insert (Deck F d) PertExtension.Physical.Profile.n
local notation "Κ" d=>Matrix (Deck F d) (Deck F d) fps
variable {x y:I→ Mark (Deck F d) PertExtension.Physical.Profile.n→fps}
variable {f g : I→ Mark (Deck F 6) PertExtension.Physical.Profile.n→fps}
variable {L M:I→Matrix (Deck F d) (Deck F d) fps}{V:I→ Matrix (Deck F 6) (Deck F 6) fps}

-- priceable Arc over actual q treatment. e.g. x BARE, y matched B after stabilization. On
-- only declared Stock and heights. The *broader* frame relation needed for the glyph below is
-- constructible on these procedures when using this scheme along all thresholds. Still open.
structure Fanfare (P:Path l) (D:Stock F)(r)(x y:I→Mark (Deck F d) PertExtension.Physical.Profile.n→fps)(L:I→Matrix (Deck F d) (Deck F d) fps): Prop where
 standard : Official D
 heartbeat : listens (D:=D) (l:=l) x
 vertical : ∀ i, Upright (L i)
 breach : Tendsto (fun a=> Stg (L a) 0) l (𝓝 1)
 alert : Alert P D r (fun i=>(ins d) (x i) (L i)) y
namespace Fanfare
variable (Q:Fanfare P D r x y L)
variable (W:Fanfare (d:=6) P D r f g V)
-- when requiring joint & issue clusters call Moves multiple times with same Shape clocks.
def Faces  (P:Path l) (r:ℕ)(x y:I→ Mark (Deck F d) PertExtension.Physical.Profile.n→fps)(L:I→Matrix (Deck F d) (Deck F d) fps)(s:I→Test n) := Stage P r (fun i=>(ins d) (x i) (L i)) y s
include Q in
lemma bands {s:I→ Test n} (h:Faces P r x y L s) : Stage P r (fun i=>post D (x i)) (fun i=>post D (y i)) s:= Alert.credited Q.standard Q.heartbeat Q.vertical Q.breach Q.alert h

def Polls  (P:Path l) (r:ℕ)(x y:I→ Mark (Deck F 6) PertExtension.Physical.Profile.n→fps)(L:I→Κ 6) : Prop := ∀ (n:ℕ)(v : Fin n ↪ Fin 3), Faces P r x y L (fun _=> Peal.near v)
-- injection only inhabited n≤3
variable (hk: Polls P r f g V)
abbrev peal (D:Stock F)(x:Mark (Deck F 6) PertExtension.Physical.Profile.n→fps):= Carryon.charged (post D x)
include W hk
lemma touch (v:Fin n ↪ Fin 3) : Posi P r (fun i=> Peal.touch F (post D (f i)) v) (fun i=> Peal.touch F (post D (g i)) v):= by
 have h:=W.bands (hk n v); exact Posi.sum (univ:Finset (Fin n→ Deck F 6)) (fun k _=> (Posi.fixed (PowerSeries.C (∏ i,tune F (v i) (k i)))).mul (h k))
lemma together : Posi P r (fun i=>Peal.together F (post D (f i))) (fun i=>Peal.together F (post D (g i))):= by
 have hu:= W.touch hk (Function.Embedding.refl (Fin 3)); have hv:= Posi.sum (univ:Finset (Fin 3)) (fun i _=>(W.touch hk (Fin.succAboveEmb i)).mul (W.touch hk (Peal.single i)))
 exact (hu.minus hv).join ((Posi.fixed (2:fps)).mul (Posi.product (univ:Finset (Fin 3)) (fun i _=> W.touch hk (Peal.single i))))
lemma fares : Posi P r (fun i=> (peal D (f i)).x) (fun i=> (peal D (g i)).x):= by
 have h:= W.together hk; have hh:= h 0 (Nat.zero_le _); simp only [coeff_zero_eq_constantCoeff_apply] at hh
 exact (Posi.fixed (PowerSeries.C (slope G)⁻¹)).mul (h.minus (Posi.showC hh))

variable (R:Position.Grade.Rails F) -- not redefining N after comparing
variable {a: ℝ}(ha : a≠0)(ht:Tendsto (fun i=>coeff 1 (peal D (f i)).x) l (𝓝 a))

def rear (D: Stock F)(R:Position.Grade.Rails F)(f: Mark (Deck F 6) PertExtension.Physical.Profile.n→fps) (x:Mark (Deck F d) PertExtension.Physical.Profile.n→fps) := (ins d) ((peal D f).refund.charge ∘ post D x) (R.book d)
def adjusted (D: Stock F)(R:Position.Grade.Rails F)(f: Mark (Deck F 6) PertExtension.Physical.Profile.n→fps) (x:Mark (Deck F d) PertExtension.Physical.Profile.n→fps) := (ins d) (post D x) ((R.book d).map (peal D f).charge)

-- Choose direction: compare at original $g$ or remeasure in Peal (needs slope)
include Q hk
variable {s:I→ Test n}(h: Faces P r x y L s)
include h W
lemma unitConventions : Stage P r (fun i=> adjusted D R (f i) (x i)) (fun i=>adjusted D R (g i) (y i)) s:= (Q.bands h).seen (L:=fun i=> (R.book d).map (peal D (f i)).charge) (M:=fun i=> (R.book d).map (peal D (g i)).charge) (fun a b=> Posi.century (Posi.fixed ((R.book d) a b)) (W.fares hk))
include ha ht
lemma measured : Stage P r (fun i=> rear D R (f i) (x i)) (fun i=>rear D R (g i) (y i)) s:= (((Q.bands h).calendar (q:= fun i=> (peal D (g i)).refund) (p:=fun i=>(peal D (f i)).refund) (Regatta.refund ha ht (W.fares hk))).seen (L:=fun _=> R.book d) (M:=fun _=> R.book d) (fun _ _=> Posi.fixed _))
-- relate choices exactly (prep before comparing)
omit Q W h hk ha ht
lemma priced (D:Stock F)(x:Mark (Deck F d) PertExtension.Physical.Profile.n →fps)(f: Mark (Deck F 6) PertExtension.Physical.Profile.n→fps)(H:(peal D f).Hot) : adjusted D R f x=(peal D f).charge ∘ rear D R f x := by
 let p:=peal D f; have he : p.charge ∘ p.refund.charge = id := funext (fun i=> show p.charge (p.refund.charge i)= i from by rw [← Carryon.Warp.take,p.deposit H,Warp.still_charge]); -- type cast issues
 unfold adjusted rear; rw [← Carryon.Warp.untie,← Function.comp_assoc, he]; rfl

-- dangerous omit?
end Fanfare
end YM.FormalOPE.RG10.Boardwalk.Trellis
