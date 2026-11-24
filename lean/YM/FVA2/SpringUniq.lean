import YM.FVA2.BilledClock
import YM.FVA2.RealRep
/-!
# Removing hidden choice (`Data`, representatives)

For any Booked, any two valid MS lean computations differ by amplitudes only in
arbitrarily irrelevant germs (or at bad arguments `dotty`); here the projection agrees everywhere.
Thus unique MS separated prescription even before regulator match.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Atoll
open Filter Topology Set Function MeasureTheory
open MS MS.Plane MS.Tone MS.Land MS.Theater MS.Landau MS.Landau.Detect MS.Rake MS.Rake.Geo MS.Tide MS.High MS.Local.Physical MS.Menus
open MS.Pearl MS.Train MS.Outlook MS.Mach MS.Hem.Mell MS.SpinCode MS.Dock MS.Vane
open ColorCode Pic Panel Elegant Verne ArchTurn
open Pert Pert.Position Maxwell Maxwell.Free Pert.RawLabels PositionX PositionX.Jet PositionX.Ribbon PositionX.Bend
open scoped Topology Classical ContDiff
variable {G: Gauge}{B:Deck G}{O:Booked B} (A P: Land.MS_Data G O)
variable {d k m:ℕ}
lemma main_bulk : Archive 4 A.bulk= Archive 4 P.bulk:= archive_h (Land.uniq A P).2.1 (fun i=> ( Dock.gang ( A.bulkOK i ) ).dost ) (fun i=> ( Dock.gang ( P.bulkOK i ) ).dost )
lemma optic_bulk (d:ℕ)(i:Plaid B d): Archive d ( A.marks d i )=Archive d ( P.marks d i ):= archive_h ( ( Land.uniq A P ).2.2 d i|>.2 ) (fun j=> ( Dock.gang ( A.markOK d i j ) ).dost ) (fun j=> ( Dock.gang ( P.markOK d i j ) ).dost )
lemma alignmentM {V:BookM B}{Q:Prescription B}(h:TaylorOKM A V Q): TaylorOKM P V Q:= by
    refine ⟨ ?_, fun d i=> (?_) ⟩; rw [ ← main_bulk A P ]; exact h.bulk
    rw [ ← optic_bulk A ]; exact h.mark d i
lemma spines {W:Type}[LinearOrder W] (v:W→ Label B)(Z:W→ QP)(y:ℝ) (h:Injective Z): Dial.spine A v y Z= Dial.spine P v y Z:= by
    have hp {I:Type}(Y:Rake.Geo I): rowM Y A= rowM Y P := by unfold rowM; simp_rw [optic_bulk A P ]; -- hm rewrite right
    obtain hc:= Dial.pin P v y h; unfold MS.Vane.DOrd at hc; rw [ approach, ← main_bulk A P, ← hp ] at hc; exact perfect ( Dial.pin A v y h ) hc -- DOrd ns?
lemma bouquet_eq {W: Type}[LinearOrder W] (v:W→ Label B)(Z:W→ QP)(y:ℝ)(h:Injective Z) (w:Finset W)(n:ℕ): Dial.tour A v y Z w n=Dial.tour P v y Z w n:= by unfold Dial.tour Dial.book; rw [ spines A P v Z y h ]; -- policy
section points
variable (V: Warehouse G){p:ℝ} (R:Booth p V.F){O:Booked (wings G)} (X Y:MS_Data G O)(t:ℝ) {g:G.Simple}
local notation "F"=> V.F
lemma markings : Pic.marked V X t=Pic.marked V Y t := by
    apply Panel.ext; intro d n a; funext i; apply ( Module.Basis.ext_multilinear (fun _:Fin n=>sameAxis V.F d)); intro w; change Fountain.phys V X t i a.val d ( sameAxis V.F d ∘ w )=Fountain.phys V Y t i a.val d ( sameAxis V.F d ∘ w ); rw [Fountain.onLit,Fountain.onLit ]; exact bouquet_eq X Y _ _ t ( Fountain.metric_conf a.property ) Finset.univ i
lemma w_live : Spring.ms V X t d= Spring.ms V Y t d:= by rw [ ← Pic.payMark V X t d, ← Pic.payMark V Y t d,markings V X Y ]
include g
lemma metric_unify : Elegant.ξ g V X t R= ξ g V Y t R:= by rw [ ← Pic.realizer V X, ← Pic.realizer V Y, markings V X Y ]
lemma world_is : Pic.L V X t g= Pic.L V Y t g:= by apply Strat.ext; intro h; unfold Pic.L Pic.normalize; simp_rw [turns]; -- maybe rfl
                                                                   rw [w_live V X Y]
lemma Xsame : Pic.X V g X t R= Pic.X V g Y t R:= by unfold Pic.X; rw [metric_unify V R X Y,world_is V X Y, markings V X Y]
lemma Charges_eq (P:Land.Prescription (wings G))(HS: Blaze.ExactSpin V P)(HU:Frost.Trusted P) (H:TaylorOKM X ( V.native (wings G) ) P) (Q:Land.Prescription (wings G))(hp:Blaze.ExactSpin V Q)(hc:Frost.Trusted Q)(ht:TaylorOKM Y (V.native (wings G)) Q) {q:ℕ+}(hq:1<q.val)(A:Knocker g R q hq (BoxOffice.warehouse V)): Clock.rate P.team= Clock.rate Q.team ∧∀ x y n d, Counterpart.bareD V P x y n d=Counterpart.bareD V Q x y n d:= by
   let u:= MixedStory.ceases X V H g; let v:= MixedStory.ceases X V ( alignmentM Y X ht ) g; exact ⟨ Plot.clock_eq V X R P HS HU u hq A hp hc v, fun x y n d=> Erase.field_eq V X R P HS HU u Q hp hc v hq A x y n d⟩
lemma checked (T:Pic.pass V g X R)(Q:Pic.pass V g Y R) : Forge.transfer V X R t T=Forge.transfer V Y R t Q ∧ Forge.Check V X R t T= Forge.Check V Y R t Q := by
   have h : Forge.transfer V X R t T= Forge.transfer V Y R t Q:= by apply Hop.ext; unfold Forge.transfer Forge.Pay; simp only; rw [metric_unify V R X Y ]; unfold Forge.transfer Forge.Pay; simp only; rw [world_is V X Y,metric_unify V R X Y ];
   exact ⟨ h, by rw [ Forge.agrees, Forge.agrees,h,markings V X Y ] ⟩
end points
end YM.FVA2.Atoll
