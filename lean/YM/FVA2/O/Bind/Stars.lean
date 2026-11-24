import YM.FVA2.O.Bind.Weather
/-!
# Gluing the MS unit-shape coefficients

Complete compatible FAR approximation. Use the compact-local `Fetch` from `O/Enh/Sale`,
then `O/Bind/Local` for consistency, bootstrap the error to the next power (`Basket_step`)
and construct one global family `Phoenix`. Not yet the usual near-radius point OPE
(see `O/Project`).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Bind
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick Metric Real
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix
open FVA2.Scale MS.Rake MS.Theater Level O.Score LogTime MS.Plane MS.Heat MS.Tone Momentum Rake.Geo
open Equator Facets Dframe O.Enh
variable {G:Gauge}{ I J: Type }{ n m d k i j:ℕ }{O:Booked ( Press.portDeck G )}{M:MS_Data G O}{ν:ℝ}
variable {A: Album G}{ V:Arenas G }{B:ℝ→ Frames G}{R:ℝ→Cn}
variable {f g:Fable G n}{s:Set (Points n)}{ x:Points n}{u:Scan G n}
local notation "VΩ"=> install V
abbrev Off (f:Fable G n): Prop:= ∀ i,i∉conf n→ f i=0
abbrev PaceX (f:Fable G n): Prop:= ∀ b:Q G,∀ i:ℕ,ContinuousOn (fun j=> coeff i ( f j b )) (conf n)
def AllC (A:Album G)(u:Scan G n)(f:Fable G n) : Prop:= Off f ∧ PaceX f ∧ ∀ s,IsCompact s→ s⊆ conf n→ ∀ k d:ℕ,Fiasco A s k 1 d u f
lemma philosophy (h: PaceX f)(hp: IsCompact s)(ht:s⊆ conf n): PlainF s f k d:= by
    intro q he i hi; obtain ⟨C,h⟩:= hp.exists_bound_of_continuousOn ( (h q i).mono ht ); exact ⟨ C, fun i=> h i.val i.property ⟩
lemma independent (h:Law V R B)(hp:Ground V)(ht:Regular V)(he: Observed VΩ)(hx: AllC VΩ u f)(hv:AllC VΩ u g): f=g:= by
    funext x; by_cases hm:x∈conf n; swap; · rw [ hx.1 x hm,hv.1 x hm ]
    funext q; ext i; let k:= heft q; have hs:=isCompact_singleton (x:=x); have hP:= singleton_subset_iff.mpr hm;
    exact uniqueK h ht hp he zero_lt_one le_rfl ( hx.2.2 {x} hs hP k (i+1) ) ( hv.2.2 _ hs hP _ _ ) ( philosophy hx.2.1 hs hP) ( philosophy hv.2.1 hs hP ) x ( mem_singleton x ) q le_rfl i ( Nat.lt_succ_self i )
-- MS Kernel supply
local notation "A0"=> install ( Equator.wave ν M )
def Fetch (ν:ℝ)(M: MS_Data G O)(u:Scan G n)(s:Set ( Points n ))(h:IsCompact s)(he:s⊆ conf n)(k d:ℕ): Fable G n:= Classical.choose ( Locals ( ν:=ν ) ( u:=u ) (k:=k) ( d:=d ) M h he )
lemma ref (h:IsCompact s)(he:s⊆conf n): let V':=Fetch ν M u s h he k d; Fiasco A0 s k (eps_gain/2) d u V' ∧ PlainF s V' k d:= Classical.choose_spec (Locals M h he)
def Phoenix (ν:ℝ)(M:MS_Data G O)(u:Scan G n) : Fable G n:= fun x b=> if h:x∈conf n then PowerSeries.mk ( fun i=> coeff i ( Fetch ν M u {x} isCompact_singleton (singleton_subset_iff.mpr h) (heft b) (i+1) x b )) else 0
local notation "F"=> Phoenix ν M u
lemma off_F : Off ( Phoenix ν M u ):= fun _ hx=> funext fun _=> dif_neg hx
variable (H:Law ( Equator.wave ν M ) R B)
local notation "v"=> (eps_gain/2)
lemma both_g : 0< eps_gain/2 ∧ eps_gain/2≤1:= by have h:= p_gain; have he:=s_gain; constructor <;> linarith
include H
lemma pivotal (h:IsCompact s)(he:s⊆ conf n): Same s k d ( Fetch ν M u s h he k d ) F := by
    intro x hx p hm j hj; rw [ Phoenix,dif_pos ( he hx ), coeff_mk ]; let S:= ( {x}:Set (Points n) ); have hS:IsCompact S:=isCompact_singleton; let i:= heft p; let f:= Fetch ν M u s h he k d; let V:=Fetch ν M u S hS ( singleton_subset_iff.mpr ( he hx ) ) i ( j+1 ); obtain hh:= ref (M:=M) ( ν:=ν ) ( k:=k ) ( d:=d ) ( u:=u ) h he; obtain hp : Regular ( Equator.wave ν M ):= regular_wave ν M; obtain hV := seenMS ν M; have hx: S⊆ s:= singleton_subset_iff.mpr hx
    have h0: Fiasco A0 S i ( eps_gain/2 ) (j+1) u f := subsetF hx ( watch ( Nat.succ_le_of_lt hj ) ( levels H hp hV hh.2 hh.1 hm both_g.1.le both_g.2 ) );
    obtain hW:= ref (M:=M) ( ν:=ν ) ( k:=i ) (d:=j+1) ( u:=u ) hS ( subset_trans hx he ); exact uniqueK H hp (fun _=> Equator.before ν M ) hV both_g.1 both_g.2 h0 hW.1 ( restrict_P hx ( paths_F hm ( Nat.succ_le_of_lt hj ) hh.2 ) ) hW.2 x ( mem_singleton _ ) p le_rfl j (Nat.lt_succ_self j)
lemma seam_F (h:IsCompact s)(he:s⊆ conf n): Fiasco A0 s k 1 d u ( Phoenix ν M u ):= by
    obtain hh:= ref ( ν:=ν ) ( M:= M ) ( k:=k+1 ) (d:=d) ( u:=u ) h he;
    exact rotate_p ( Same.inherits (pivotal H h he) ( d:=d ) ( k:= k+1 ) ( Nat.le_succ _ ) ( le_refl d ) ) ( Basket_step H ( regular_wave ν M ) ( seenMS ν M ) hh.2 hh.1 ( both_g.1.le ))
lemma Pace_F : PaceX F := by
    intro p i x hx; obtain ⟨s,hs,hx',hp⟩:= exists_compact_subset ( conf_open n ) ( show x∈conf n from hx ); let k:= heft p; obtain h:=ref ( ν:=ν ) ( M:= M ) ( k:=k ) ( d:=i+1 ) ( u:=u ) hs hp;
    obtain H0 := charm_ζ hs hp (seenMS ν M) H ( regular_wave ν M ) ( fun _=> before ν M ) both_g.1 both_g.2 h.1 h.2 k le_rfl i ( Nat.lt_succ_self i ); let g:= Fetch ν M u s hs hp k ( i+1 );
    have hh : ContinuousOn ( fun t=> coeff i ( Phoenix ν M u t p ) ) s:= ContinuousOn.congr ( show ContinuousOn ( fun t=> coeff i ( g t p ) ) s from continuousOn_iff_continuous_restrict.mpr ( H0 p.item ) ) ( fun i' ht=> ( pivotal H ( k:= k ) ( d:=i+1 ) hs hp i' ht p le_rfl i ( Nat.lt_succ_self i ) ).symm ); exact ( hh.continuousAt ( mem_interior_iff_mem_nhds.mp hx' ) ).continuousWithinAt
lemma FAR : AllC A0 u F:= ⟨ off_F, Pace_F H, fun _ hs ht _k _d=> seam_F H hs ht ⟩
end YM.FVA2.O.Bind
