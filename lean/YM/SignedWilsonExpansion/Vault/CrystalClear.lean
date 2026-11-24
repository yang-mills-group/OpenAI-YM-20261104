import YM.Integration.WilsonOriginalObservedRoseCorrectedWords
import YM.Integration.WilsonIndependentConditionedDenseFilmTerminal
import YM.Integration.WilsonIndependentConditionedDenseFilmBank
import YM.SignedWilsonExpansion.Vault.Cordial
import YM.SignedWilsonExpansion.Ink.Reams
/-!
# Fits: the two-flat output with normalized numerical series, paying clocks.

For **the purchased** `↑Y`, *same program* independently cold-stopped pole.
Actual K product including marker face is `DenseFilmBank.upper` exactly. Permit
 all Pane axes & sizes. `Age` & posing center needed for payment later. Definitional conversion archive.

Port: digit tape at **A.loc**, not a tree learned after forecasts. Works even cap unit, mask empty. The uncut product supported at K and ALL masks keep their dense histories.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 280000
noncomputable section
namespace YM.Integration.Election.VaultM.Cordial.Fits
open Function Finset Set Filter MeasureTheory Lattice RG Wilson Source Labels Marker Multi
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Winding
open WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Bank
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Soil WilsonCoeffUV.Embroider
open OriginalMarkedSourceComet StressFlux.Matching Extraction Next.UVStress
open SignedWilsonExpansion SignedWilsonExpansion.Homes HeartT HeartT.Spritz SignedWilsonExpansion.StageG
open WilsonOlderFreshSoftSocketTotal (normalized)
open WilsonReceivedChronologicalMaterialCapture (placed)
open WilsonIndependentCollarOrdinaryCruise (address)
open WilsonIndependentCollarDatedPrior (onLevels)
open WilsonReceivedChronologicalMaterialSites (digits physical)
open WilsonIndependentConditionedDenseFilmBank (upper)
open WilsonOriginalObservedRoseCorrectedWords (votes)
open WilsonPositionProgramBlockedTrialAddBack (uncut)
open WilsonMeasuredPublicEntrancePanel (Panel)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonReceivedCanonicalVersePortfolio (Selection)
open WilsonIndependentConditionedDenseFilmTerminal (output)
open Liner InkP Pane SignedWilsonExpansion.Commission Cells Pert.Asymptotics
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer.Xa MarqueQ Precision MarqueQ.Crops
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G : Gauge} (R : Run G) {n j₀:ℕ} {N per f K v c P first pwr b t:ℕ} {d D:Fin n→ℕ}
variable {fk:f≤j₀+1+1}{ck:c≤j₀+1+1}{cut:j₀+1+1≤N}{B:ℝ} {F:Filed R d ( j₀+1+1 )} {A:Panel R d N per f ( j₀+1+1 ) fk cut t pwr b B}
local notation "C₀" => R.family
local notation "ZK" => j₀+1+1
local notation "w₀" => votes R d (N:=N) (per:=per) F A.names A.turn
local notation "rK" => regulatorRun C₀ N per
private lemma unroll {K K':Levels G}(h:K=K')(t:Digits K' (Fin n)):onLevels h (onLevels h.symm t)=t:=by cases h;rfl
lemma tally (s: Finset (Fin n))(Y : Fin n → Site ((C₀).side K per)) : digits R Y=InkP.Ladder R per K s Y:=rfl
variable {x:Fin n→ Cover} {X Y:(i:Fin n)→ ( R.family ).label (d i)} (z:Pane R F A x X Y) (s: Finset (Fin n))
include z
lemma stool : placed R fk A.loc=location ((C₀).S) f (j₀+1+1) per ∘ x :=by
    rw [z.seats]; funext i; unfold Cells.location Function.comp WilsonReceivedChronologicalMaterialCapture.placed; simp only [dif_pos fk]
lemma rooted (h:Ballots.rolls (C₀).S (location ((C₀).S) f (j₀+1+1) per ∘ x) ck=0): ∀i, physical R (placed R fk A.loc) ck i=0:= by rw [stool R z]; exact congr_fun h
lemma certifiedK : Y=w₀:=by rw [z.vote]; unfold WilsonOriginalObservedRoseCorrectedWords.votes; rw [←z.stations,←z.home]; rfl
lemma stem : stemK C₀ d x Y f N per (j₀+1+1) s=upper R d (N:=N) fk A.loc (w₀) (capM s):=by
   rw[←z.K_stem R s]; funext U; exact (Finset.prod_coe_sort s
      (fun i:Fin n=>uncut R (d i) N per ( ZK ) (((C₀).S.toDepth fk per).embed (A.loc i)) ((w₀) i) U)).symm
lemma seeded {V : Realm G ((WilsonReceivedChronologicalFixedReserve.terms d (fun _=>0) P).order+1) Credit.leanC}
    (draw : V.draws=R.family.path.levels) (pt : Fin n → Chamber) (c degree : ℕ) :
   calcT ( rK (first+1):ℂ ) degree (InkP.valued R d (D:=D) pt N per ( first+1 ) (j₀+1+1) c Y (location ((C₀).S) f (j₀+1+1) per ∘ x) s)=
   output (R:=R) (d:=d) (P:=P) (N:=N) (j:=j₀) (per:=per) (first:=first) (V:=V) (draw:=draw) (lens:=D) (pt:=pt) (fine:=fk) (site:=A.loc) (votes:=w₀) (mask:=capM s) c degree:=by
    rw [ ← stool R z, certifiedK R z, signalsT ]; unfold WilsonIndependentConditionedDenseFilmTerminal.output; simp only [Nat.sub_self,WilsonReceivedChronologicalMaterialLine.homes,WilsonReceivedChronologicalFixedCellFee.tape,unroll,tally R s]; rfl
lemma literal (hk:v≤j₀+1+1) : born₀ C₀ d x Y f N per v (j₀+1+1) s= actualTransport C₀ (N:=N) (upper R d (N:=N) fk A.loc (w₀) (capM s) ) hk 1 :=by rw[born₀,dif_pos hk,stem R z s]
end YM.Integration.Election.VaultM.Cordial.Fits
end
