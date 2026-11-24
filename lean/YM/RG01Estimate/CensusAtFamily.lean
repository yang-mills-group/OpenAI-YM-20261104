import YM.RG01Estimate.CensusStep
import YM.UVExtension.Reports.Ultraviolet
import YM.Pert.Asymptotics.RawAxis

/-!
# Invoke on the shared construction

Exposes the particular listing to consumers, on the FULL UV Family/Final of this release,
not a different `Org.Bolt` construction. `p` is *period index*, not expansion order.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate

open Function Filter Set Lattice Wilson RG Pressure MeasureTheory
open Push Push.AbsoluteSums SectorMeasure Oriented Shoot Precision
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open PriceCompiler Org Input Supply Time Source
open PhysicalNext PhysicalNext.Repeat Roost Opera Match Legato
open ConnectedActivityE6
open UVExtension Oasis Spire Camp Mast Cellar Upland
open Pert.Asymptotics CensusStep
open scoped Topology BigOperators Classical

variable {G : Gauge} (hG : G.Simple)
variable {M : Metals G} {D : Rolls M.p} {A : Alloy M D}

section family
variable (R : Factor A) (S : Uses R hG)
variable {t : ℕ → ℕ} {K : ℕ → ℝ} {w : Bid.Worth} {Q : Bandage R K w} (L : Cellar S t Q)
local notation "C" => Cellar.yard (Mast.roseA S) L

/-- All finite orders on one witnessed realization. Step output is *pre-reset*,
its p is the actual BudgetPoint. `assembled` uses precisely that listing, masks,
scalar and kinetic receipt. -/
def CensusOrders := ∀ r : ℕ,
    ∀ᶠ m in atTop, ∀ N p, m < N →
    let U:= (C).path.rep N p (m+1)
    let V:= (C).path.rep N p m
    let P:= (C).path.levels.budget m
    let g:= regulatorRun (C) N p (m+1)
    ∃ (H : Guide A.B R.shape N m p U) (X : Alliance H H 1 0),
      0 < g ∧ X.units=Equiv.refl _ ∧ V.p=P ∧ Account R H H X r ∧
      (∀ O : Tree.Forest ((C).path.levels.clock.op m p).ratio,
          V.eval = earlyValue (ledger R H) V.path V.clip P (vacuum R H H X) U.beta
            (Song.weighty H Chi.canonical O) (A.B.kin.alpha N m)) ∧
      ((ledger R H).read (discarded R H H X r)).EBound P ((2*g)^(r+1)) ∧
      ((ledger R H).read (vacuum R H H X)).KBound P
        (Real.sqrt ((C).path.levels.clock.forcedAllowance m) * ((2*g)^(r+1)))

-- invoke rule
lemma orders (hh : (C).Makes) : CensusOrders hG R S L := by
  intro r
  filter_upwards [CensusStep.cluster_tail hG R r] with m hm N p hp
  intro U V P g
  have hz:= S.ticking N p (Uses.centerP A.B.a)
  have ht : Lives A.B.bake N m p V := (hz.prices m (Nat.zero_le _) hp.le).1
  have hP:= hz.prices (m+1) (Nat.zero_le _) hp
  have hU : Lives A.B.bake N (m+1) p U:= hP.1
  have hV : U.beta∈Shoot.band A.B.a (m+1):= hP.2
  obtain ⟨H,he⟩:= Opera.feature A.B R.shape hp R.pledging.conducts.full R.pledging.conducts.income hU hV
  let X:= Match.staple (H:=H) (J:=H) rfl rfl rfl
  have hs:= hm N p hp U U H H X he hV
  refine ⟨H,X,(StepRate.calibration A.B.a hV).2.1,rfl,ht.point,hs,fun O=>?_,
    (VacuumListing.proper_caps P hs.high).1, Time.K_rises (VacuumListing.proper_caps P hs.fullSize).2 hs.reserve⟩
  have hv : V.path=A.B.kin.path N m := by rw [ht.path, A.B.bases]
  funext Y
  calc
    _ = (A.B.a.clock.op m p).push U.beta U.eval Y := congr_fun (hh.wilson.steps N p m hp).1 Y
    _ = _ := by rw [hv, ht.clip]; exact hs.integral O Y
end family

theorem uv_census {C : Family G} (h : Oasis.Floral (hG:=hG) C) {f : Extraction.Order}
    {T : Table C.book} (F : Spec.Final C f T) :
    ∃ (M : Metals G) (P : Rolls M.p) (A : Alloy M P)
      (R : Roost.Factor A) (S : Uses R hG) (T' : Bolt A)
      (t : ℕ → ℕ) (K : ℕ → ℝ) (w : Bid.Worth)
      (Q : Bandage R K w) (L : Cellar S t Q),
        Arc R S T' ∧ C = Cellar.yard (roseA S) L ∧ Oasis.Spring S ∧ CensusOrders hG R S L := by
  obtain ⟨M,P,A,R,S,T',t,K,w,Q,L,H,rfl,hS,-⟩:= h
  exact ⟨M,P,A,R,S,T',t,K,w,Q,L,H,rfl,hS,orders hG R S L F.room.cutoff⟩

end YM.RG01Estimate
