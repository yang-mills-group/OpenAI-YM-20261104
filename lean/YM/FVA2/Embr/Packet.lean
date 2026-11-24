import YM.FVA2.Embr.Event
/-!
 # Shared target at open field $y$, compatibility of $N$ costs and log quantities

 Not just a scalar reachability argument after sealing. Income
 `Fk.birth` affirmed against same RG10/Step kernel. Publish before further
 observation charges and matching at physical level. Costs simultaneous through a
 given order AND factor count grades as filled. All linked to same Evolution
 across the whole specification. Don't claim any cover-wide estimate
 from any lemma here.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Embr
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots Function Filter Finset MeasureTheory Metric PertExtension Precision Lattice GaussianScore Chart RG
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric Papers MarkovChain Warp Line Roof Router OpenSlots.Quadratic
open PertExtension.Orb PertExtension.Series Tested Radial Facade Hearth Sync Route Gists Marker Extra.Trajectories
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge}{A B:Type}{N:ℕ}{n:Side}{L:Fabric G n}{T:Cloth L}{J:ChartRatio G}
open Arrival RGComparison.Core16 Lumen
variable {w:L.Accounts→ℝ→ℝ} {x: Flats G (Bottom L)} {s:G.ColorIndex} {Ω:Lumen.Shelf G Unit (Warm T)} {j:Warm T→Site n}
local notation "P"=> home T w x s Ω j
variable {Y:XSpace.Initialize G} (z:L.Accounts→PowerSeries ℝ) (hz:∀i,0<term (z i) 0) (hw:∀ i, Through N (amount (w i)) (z i)) (H:∀ i,ContDiffAt ℝ ω (w i) 0)(hj:LocalRatio J)
set_option quotPrecheck false
local notation "Π"=> Facade.headquarters z
local notation "b"=> collared T z hj hz
variable {I:Type}[Fintype I][DecidableEq I](R:Census I) (φ: I→ Folio G)
variable (T J Y)
local notation "Q"=> logway R T (z∘some) Π (beginOn Y R φ n) J b
variable (F:Habitat T w x s Ω) (V:ℕ)(hv:∀ u:R.Mode,Folio.asset (Embr.mark R φ u)+ V ≤ N)
variable ( w x s Ω j)
def fkFrame : Word R:= FormalOPE.RG10.Word.package (fun u:R.Mode=> let l:= Embr.mark R φ u; Sync.align ( PowerSeries.mk ( Fk.read P J (tease T s) (lens T x s (Hearth.rad T (Folio.scenario Y n l) )) (Folio.asset l))))
-- THEN entry reads LOG. Staging & budgets.P
local notation "W"=> fkFrame T J w x s Ω j Y R φ -- order inspect
local notation "K"=> FormalOPE.RG10.Word.package (fun u:R.Mode=> observed T Y R φ z hz hj u x)
include hw H hj F hv
omit [Fintype I] in
lemma rehearsals : Through V W K:= by
 refine Through.views.mpr fun u i hi=>?_ ; unfold fkFrame; rw [FormalOPE.RG10.Word.see_package,FormalOPE.RG10.Word.see_package]; unfold Sync.align observed; erw [PowerSeries.coeff_map,PowerSeries.coeff_map, PowerSeries.coeff_mk]; exact congr_arg _ (posts F Y (Embr.mark R φ u) hj z hz N hw H i ((Nat.add_le_add_left hi _).trans (hv u))) -- name ambiguous
lemma genuine_readout (u:Multi.Hot R): Through V (FormalOPE.RG10.Word.see u.val (FormalOPE.RG10.Word.logWord W)) (run (Sync.tint (natural (Bottom L) G) x) (Q u)):= by
 have hV:= ( rehearsals (T:=T) (J:=J) (w:=w) (j:=j) (Y:=Y) (x:=x) (s:=s) (Ω:=Ω) z hz hw H hj R φ F V hv ).logCongr
 rw [walker (hj:=hj) (hz:=hz)] at hV; rw [← Gists.sees]; exact (Through.views.mp hV u.val)
omit H hw F hv
-- preserving exact restrictions on markers. independent of list order.
section
variable {S:Census I}
variable {I':Type}[Fintype I'][DecidableEq I'] {S':Census I'} (u:Extra.Trajectories.Names R S') (ψ:I'→Folio G) (Z1:∀ i,φ i=ψ (u.e i))
include Z1
lemma transferNames (i:R.Mode) : Gists.program R Q i= Gists.program S' (logway S' T (z∘some) Π (beginOn Y S' ψ n) J b) (u.share i):= by
 let f:= query Y R φ n; let g:= query Y S' ψ n
 have he:f i=g (u.share i):=by unfold f g; rw [fidelity Y R φ i L.even, fidelity Y S' ψ (u.share i) L.even]; unfold Extra.Trajectories.Names.share; rw [prod_image u.e.injective.injOn]; exact Finset.prod_congr rfl (fun i _=> congr_arg ( fun k=> digital (natural n G) (markValue Y [k] n)) (Z1 i))
 rw [ runUp,runUp,show Gists.program R (beginOn Y R φ n) i=f i from Gists.Card.moment_law R f i (query_nil Y R φ), show Gists.program S' (beginOn Y S' ψ n) (u.share i)= g _ from Gists.Card.moment_law S' g _ (query_nil Y S' ψ), he]
lemma restriction : K= FormalOPE.RG10.Word.eraseMarks u ( FormalOPE.RG10.Word.package (fun k:S'.Mode=> observed T Y S' ψ z hz hj k x) ):= by
 apply FormalOPE.RG10.Word.observe_ext; intro i; rw [ FormalOPE.RG10.Word.see_eraseMarks, FormalOPE.RG10.Word.see_package,FormalOPE.RG10.Word.see_package,reported,reported, transferNames (hj:=hj) (hz:=hz) (u:=u) (ψ:=ψ) (Z1:=Z1) ]; -- args check
lemma restriction_log : FormalOPE.RG10.Word.logWord K= FormalOPE.RG10.Word.eraseMarks u ( FormalOPE.RG10.Word.logWord (FormalOPE.RG10.Word.package (fun k:S'.Mode=> observed T Y S' ψ z hz hj k x)) ):= by
 rw [restriction (hj:=hj) (hz:=hz) (u:=u) (ψ:=ψ) (Z1:=Z1), FormalOPE.RG10.Word.restrict_log]; rw [ FormalOPE.RG10.Word.boot, FormalOPE.RG10.Word.vac_eq,FormalOPE.RG10.Word.see_package,reported,Gists.blank,map_one ]; simp
end
end YM.FVA2.Embr
