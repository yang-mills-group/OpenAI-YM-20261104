import YM.MS.Fleet.Shore
import YM.MS.SpaceOut.Saga
/-!
Mark stencil affordability. Sets only at the absolute cover offsets. `Purpose` fits any specified
pole period x-n range by choosing M.bank >= 1+ logν and the indicated placement offsets (cluster
size, no term for proximity to UV spacing). Used with superpolynomial side.

For exact-term decoupling we allow _generic_ finite stencils, not just physical matched ones.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Fleet
open Set Filter Function Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native
open Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit Cog
open scoped Topology ContDiff Interval
variable {G:Gauge}{I W:Type}[LinearOrder W]{L:I→Side}{S:Finset W}{g:ℤ}
    {X:Rake.Dance G I W}{Q:Seeds G I W}{F:I→Law G}{n:ℕ}
variable (c:Berth ( W:=W ) ( I:=I )) {A:Faces I}{V:Vista.Visa I}
local notation "Ψ"=> ( outside L )
local notation "ιW"=> ( Orbit.uniform G I )
open Vista Vane Land High Program Native.Wilsonian Paint Wind Menus
variable {B:Local.Physical.Deck G}{T:Prescription B}{R: Rake.Geo I}{l:W→ Rake.Label B}{W':LitBook B}
local notation "πA"=> Scope G (Wind.skyline G T.team) R.η
variable { U:W→ Actor G}{ η:I→ℝ}

def Stops (V:Visa I)(c:Faces I): Prop := paid (arrival V) (fun i=> ‖Tone.embed ( c i )‖) 1
structure WidthW (V:Vista.Visa I)(η:I→ℝ)(c:Berth ( W:=W ) ( I:=I )): Prop where
   proper : SpaceOut.warmV η V
   size w : Stops V ( c w )
lemma cash_η (h:SpaceOut.warmV η V): paid (arrival V) (fun i=>‖η i‖) 1:= ⟨1,zero_lt_one,1,fun i=> by simp only [pow_one,one_mul,Pi.one_apply,mul_one]; change |η i|≤V.bank i; linarith [h i]⟩
lemma cash_L (hp:Lease false true (arrival V) F 1)(hx:Stops V A): Lease false true ( arrival V ) (fun i=>lodging ( A i ) (F i)) 1:= by
   intro E _ _ w h1 h2; unfold Cape Plane.Chart; simp_rw [ lodg, sail_net ]; exact pulse_bill (net w) (hp E w h1 h2) ( paid_at (S:=( arrival V )) hx (fun _=>zero_le_one)) -- cost vs length
lemma rep_α {φ:Actor G}{b: Bool}(h:Circle G φ b g)(hu:Stops V A)(ht:paid (arrival V) (fun i=>‖η i‖) 1)(n:ℕ): let F(i:I):=frameL (A i) ( run ( φ (η i) n ) ); Knits (coast0 F) ∧ Lease false true (arrival V) F 1:= by
   intro F; obtain H:= openOrigin φ n h; let S:= ( arrival V ); have hm : Lease false true S (fun i=>run (φ (η i) n)) 1:= by apply maximumT (S:=S) (η:=η) (a:=fun _=>0) (T:=0) (fun i=> by simp) (fun i=>rfl) (fun s=>borne (φ s n)) H ht
   exact ⟨ cap_lod A ( feesBuy H η ), cash_L ( SpaceOut.owns_money (fun _=>le_rfl) hm ) hu⟩ -- cast.Voice shadow
-- torus program by specified column, series and period
variable (η)
def goalsK (V: W→ Actor G)(t:Finset W): ℕ→ I→Law G:= fun n i=>if h:t.Nonempty then if t.card=1 then frameL (c (t.min' h) i) ( run ( V ( t.min' h ) ( η i ) n ) ) else 0 else 0
lemma goals_m (w:W)(k:ℕ)(i:I) : goalsK c η U {w} k i= frameL (c w i) ( run ( U w ( η i ) k ) ):= by unfold goalsK; simp
lemma goals_t (h:S.card≠1): goalsK c η U S=0:= by
   funext n i; unfold goalsK; by_cases hp:S.Nonempty; · rw [dif_pos hp, if_neg h]; rfl
   rw [dif_neg hp]; rfl
variable {η}
lemma moneyM (h:WidthW V η c)(hp: ∀ i,∃ b g,Circle G (U i) b g): SpaceOut.FlowSet V (goalsK c η U):= by
   intro i; by_cases H:i.card=1; swap; · rw [ goals_t c η H ]; exact ⟨ fun i=> knit0 ..,fun _=> Lease.zero (fun _=>zero_le_one) ⟩
   obtain ⟨p,rfl⟩:= Finset.card_eq_one.mp H; obtain ⟨ b,g,hg⟩:= hp p; have ht(n:ℕ):= rep_α hg ( h.size p ) ( cash_η h.proper ) n; rw [show goalsK c η U {p}= (fun n i=>_) from funext (fun n=> funext (fun i=> goals_m c η p n i)) ]; exact ⟨fun n=> ht n|>.1,fun n=> ht n|>.2⟩
-- specialize, then afford.Vp
abbrev SeedsW (V:LitBook B)(T:Prescription B)(l:W→ Rake.Label B)(R: Rake.Geo I): Seeds G I W:= goalsK c R.η ( (PortEntry V T) ∘ l )
lemma seedW_ok : Crew0 W' T l R.η c ( SeedsW c W' T l R ):= ⟨fun p n i=> goals_m c R.η p n i,fun p h=> goals_t c R.η (by omega) ⟩
lemma cashSeeds (T:Prescription B) (l:W→ Label B) (W':LitBook B)(h: WidthW V R.η c): SpaceOut.FlowSet V ( SeedsW c W' T l R ):= moneyM c h (fun _=>⟨ false,0,decor W' ..⟩)
end YM.MS.Fleet
