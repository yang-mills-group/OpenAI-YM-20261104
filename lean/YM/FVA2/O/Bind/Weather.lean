import YM.FVA2.O.Bind.Local
/-!
# Continuity of FAR selectors. Does not require derivative bounds at huge separations.
 Uniform reconstruction of leading reader by sampler.
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
variable { G: Gauge }{n m k i d : ℕ }{v:ℝ }{ V:Arenas G }{B:ℝ→Frames G}{R:ℝ→Cn}{A:Album G}
variable {s:Set (Points n)}{K:Set (Points m)}{y:Points m}{x:Points n}{f g:Fable G n}{a:Scan G n}{u:Scan G m} {w:ℕ}
local notation "A0"=> install V
lemma crossC ( h:IsCompact s )(hp:s⊆conf n): ∀ᶠ t:ℝ in atTop, ∀ x∈s, forest x (squeeze (-t) RootG)∈conf (n+1) := by
    filter_upwards [clusterE h hp ( S:={RootG} ) (isCompact_singleton) ( singleton_subset_iff.mpr ok_wall ), eventually_ge_atTop (0:ℝ) ] with t H ht x hx;
    let P:Geo Unit:= ⟨fun _=> t,0,fun _=>ht⟩; let X (_:Unit):= x; let Y (_:Unit):= RootG; obtain ⟨ h0,hH,hP,hV,hY⟩:= H ( P:=P ) (fun _=> le_rfl) X Y (fun _=> hx) ( fun _=> mem_singleton _ ); exact due ( f:=fun i=> forest ( X i ) ( Stretch P Y i ) ) ( colored ( P:=P ) ( Seam.mesh_sep h0 ) ( Seam.mesh_sep hP ) (fun i j=> hY j i) ) ()
-- cursor continuity
abbrev W_cont (s:Set ( Points n ))(f:Fable G n)(k i:ℕ):=∀ v:Grade G k, Continuous (fun x:↥s=> coeff i ( f x.val (Score.own v) ))
lemma sparse_cont (h:∀ j<k,∀ v ≤ i,W_cont s f j v)(he:∀ v < i,W_cont s f k v): Continuous (fun x:↥s=> sparse A f k x.val y u i):= by
    unfold sparse wage Settle; simp_rw [map_sum, coeffF ]; exact Continuous.add ( continuous_finsetSum _ (fun j hj=> continuous_finsetSum _ (fun q _=>continuous_finsetSum _ (fun w hw=> ( h j ( Finset.mem_range.mp hj ) w ( by have ht:= Finset.mem_range.mp hw; omega ) q ).mul continuous_const ) ) )) (continuous_finsetSum _ (fun j _=>continuous_finsetSum _ (fun i hi=> ( he i ( Finset.mem_range.mp hi ) j ).mul continuous_const)))
lemma advanceV (h:IsCompact s)(hp:s⊆conf n)(he:Observed A)(hx:∀ j<k,∀ v ≤ i,W_cont s f j v)(ht:∀ v < i,W_cont s f k v)(b:Toon G k) (a:Scan G n) : ∀ᶠ t:ℝ in atTop, Continuous ( fun x:↥s=>vision A f a b x.val t i ) := by
    filter_upwards [crossC h hp] with t hQ; unfold vision sample; let y:= squeeze (-t) RootG; let v:=Single (flash b); refine Continuous.mul continuous_const ( Continuous.sub ?_ ( sparse_cont (u:=v) ( y:=y ) hx ht )); rw [← continuousOn_univ]; let F:= fun x:↥s=> forest x.val y; exact ( he _ ( Fin.append a v ) i ).comp ( ( continual ( f:=fun i:↥s=>i.val ) continuous_subtype_val continuous_const : Continuous F ).continuousOn ) (fun i _=> hQ _ i.property ) -- name
lemma fortune (h:IsCompact s)(hp:s⊆conf n)(he:Observed A0)(hV:Law V R B)(hA:Regular V)(hG:Ground V)(hv:0<v)(hx:Fiasco A0 s k v d a f)(hi:i<d)(ht:∀ j<k,∀ v ≤ i,W_cont s f j v)(hh:∀ v < i,W_cont s f k v): W_cont s f k i:= by
    have hr(b:Toon G k) : Continuous (fun x:↥s=> read_n V f x.val i k b):= ( Blot hV hx hv hi b ).continuous ( Frequently.mono ( Eventually.frequently ( advanceV h hp he ht hh b a )) (fun t h=> h) )
    intro v; let F (x:↥s): Grade G k→ℂ:= finPath x.val f k i; let P:= Enh.detect V k; have hF:Continuous F:= by
        rw [ show F=( P.leftInverse ∘ (P∘ F) ) from funext (fun i=> ( LinearMap.leftInverse_apply_of_inj (tactile hG hA k) (F i) ).symm ) ]; exact P.leftInverse.continuous_of_finiteDimensional.comp (continuous_pi hr)
    exact (continuous_apply v).comp hF
lemma charm_ζ (h:IsCompact s)(hp:s⊆conf n)(he:Observed A0)(hV:Law V R B)(hA:Regular V)(hG:Ground V)(hv:0<v)(hs:v≤1)(hx:Fiasco A0 s k v d a f)(hP:PlainF s f k d)(j:ℕ)(hh:j≤k): ∀ i<d, W_cont s f j i:= by
    induction j using Nat.strong_induction_on with | h j ih=>
      intro i hi; induction i using Nat.strong_induction_on with| h i IH=> exact fortune h hp he hV hA hG hv (levels hV hA he hP hx hh hv.le hs) hi (fun j hj k hk=> ih j hj ( hj.le.trans hh ) k ( lt_of_le_of_lt hk hi ) ) (fun j hj=> IH j hj (hj.trans hi))
end YM.FVA2.O.Bind
