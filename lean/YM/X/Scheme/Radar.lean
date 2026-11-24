import YM.X.Scheme.Front
import YM.X.Journey.Bare
/-!
# Stable recalibration modulo near-Jet precritical real H frame (association joins).
Any-order statement, used in FO with singular shape estimates.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX
open Lattice Function Filter Set Pert Pert.Position Pulse Detector Jet
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{F:Labels.Frames G}{d n:ℕ}
local notation "B"=> Bank F d
namespace Ribbon
open Reed
local notation "C'"=> pureBank F d
local notation "Fℕ"=>(atTop:Filter ℕ)
-- FO bank limit ∗before coupling T and N*. none in any state! independent
variable (S:Bare.Shop F)(q:ℕ+)(hq:1<q.val)(hg:G.Simple)(s:Pert.Position.Section F d)
omit hq in
lemma closureW(x:ℕ → Bank F d)(h:∀s:Pert.Position.Section F d, Released (fun i=> lookie F s (x i))): ∃ y:Bank F d, ∀s:Pert.Position.Section F d,Tendsto (fun i=> lookie F s (x i)) atTop (𝓝 (lookie F s y)):= by
    choose C h using h; let f(n:ℕ) (t:Test n) : Lens F d n:= fun i=> C ⟨n,baring F d ∘ i,t⟩; let y(n:ℕ)(t:Test n):=emerge F (f n t); refine ⟨y,fun s=>?_⟩; have ht:Tendsto (fun i=>expose F s.f (x i)) atTop (𝓝 (expose F s.f y)):= by
      apply tendsto_pi_nhds.mpr; intro i; change Tendsto _ _ (𝓝 (emerge F _ _)); rw [reads_emerge]; exact h ⟨_,baring F d ∘ i,s.f⟩
    rw [← market_zero F y, cross_leaves]; have he:= ((cross_smooth F s.p).continuous.tendsto (expose F s.f y,0)).comp (ht.prodMk_nhds (tendsto_const_nhds (x:=0))); apply he.congr; intro i; change cross F s.p (expose F s.f (x i),0)= _; rw [← cross_leaves,market_zero]
-- official FO PT limit ∗pred only
include hq
def firstX(d:ℕ) := (closureW (x:=fun k=> S.uncut hg q k d 1) (fun i=> full_heart S hq hg i)).choose
lemma limit₁ : Tendsto (fun k=>lookie F s (S.uncut hg q k d 1)) atTop (𝓝 (lookie F s (firstX S q hq hg d))):= (closureW (fun k=> S.uncut hg q k d 1) (fun i=> full_heart S hq hg i)).choose_spec s
variable (e:ℕ)(h:d≤e)
local notation "W" x=> S.uncut hg q x d
include h
lemma radars_same : firstX S q hq hg d= pulls (up F h) (firstX S q hq hg e):= by
   suffices he:∀ t:Pert.Position.Section F d,lookie F t (firstX S q hq hg d)=lookie F t (pulls (up F h) (firstX S q hq hg e)) by funext n t;exact MultilinearMap.ext (fun p=> he ⟨n,p,t⟩)
   intro t; rw [pulls_at]; apply tendsto_nhds_unique (limit₁ S q hq hg t); refine (limit₁ S q hq hg _).congr' ?_; filter_upwards [S.uncut_up hg q hq h] with i hi; rw [← pulls_at, show pulls (up F h) _= _ from ?_]; exact congr_fun hi 1
omit h
lemma first_h(p: Detector F d) (hp:p=nested F hg S d): p.D (firstX S q hq hg d)=0:= by
    let E:= firstX S q hq hg d; let f(i:ℕ):= S.uncut hg q i d 1; let a:= p.rail; let t:= a.tableMap; let g: a.Target→ Buffer F d:= fun v=> t (v,0); have hL(v:Bank F d): g (p.read v)=p.D v:= by unfold g; change p.rail.tableMap (p.read v,0)=_;rw [p.chartD,market_zero]
    have hv : Continuous g:= p.rail.tableMap_smooth.continuous.comp (show Continuous (fun v:a.Target=>(v,(0:Buffer F d))) from by fun_prop); have he:Tendsto (fun i=>g (a.common (f i))) Fℕ (𝓝 (g (a.common E))):= hv.continuousAt.tendsto.comp (p.rail.common_limit (fun t=> limit₁ S q hq hg t)); rw [← hL]; apply tendsto_nhds_unique_of_eventuallyEq he (tendsto_const_nhds (x:=0)); filter_upwards [S.chamber hg q hq d] with i hi; rw [show g (a.common (f i))= _ from hL (f i)]; change p.D (f i)=0; rw [hp]; exact congr_fun hi.1 1
lemma radar_s : pulls (par F d) (firstX S q hq hg d)=- firstX S q hq hg d:= by
    suffices he:∀ s:Pert.Position.Section F d,lookie F s (pulls (par F d) (firstX S q hq hg d))=lookie F s (- firstX S q hq hg d) by funext n t; exact MultilinearMap.ext fun i=> he ⟨n,i,t⟩
    intro s; rw [pulls_at,map_neg]; apply tendsto_nhds_unique_of_eventuallyEq (limit₁ S q hq hg _) ((limit₁ S q hq hg s).neg); filter_upwards [S.uncut_par hg q hq d] with k hk; change lookie F _ (S.uncut hg q k d 1)= -lookie F s _; have hp:=congr_fun hk 1; rw [← pulls_at]; change pulls _ _= _ at hp;rw [hp,turn,map_smul]; simp
end Ribbon
end YM.PositionX
