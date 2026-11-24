import YM.Integration.WilsonVacuumPreResetStation
import YM.RG01Estimate.Stanchion

/-! Finite, symmetry-complete portions of the genuine physical census.
Their regular remainders use the original rooted pre-reset norm. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetCatalogue
open Function Filter Finset Lattice Wilson RG RG.Shoot Pressure
open AnalyticBridge VerifiedReset Collection Quotes PhysicalNext PhysicalNext.Repeat Legato
open ConnectedActivityE6.Coat Push.SectorMeasure Push.AbsoluteSums.Animals RG01Estimate RG01Estimate.CensusStep
open RG01Estimate.Abacus WilsonLimitConstruction.FundedCensusVacuum
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G){N per m:ℕ}(S:Station R N per m)
local notation "H" => S.guide
local notation "X" => ledger R.kit H
local notation "d" => vacuum R.kit H H S.identity
local notation "B" => R.alloy.B.a.budget m
local notation "α" => R.alloy.B.kin.alpha N m
local notation "U" => R.family.path.rep N per (m+1)

def catalogue (t:ℕ):Finset (Song.Magazine H):=
  (Finset.range t).image (fun i=>(Song.pennant H i).2)

def portion (r:ℕ)(π:Finset (Song.Magazine H)) :=
  Song.choir (fun q=>if q∈π then Height.lower H S.identity Chi.canonical (lit R.kit H H S.identity r) α q else 0)
    ∘ Song.pennant H

theorem selected (r:ℕ)(π:Finset (Song.Magazine H))(i:ℕ):
    portion R S r π i=if i∈Caddy.entries H π then (kept R.kit H H S.identity r).logRead i else 0:=by
  have mem:i∈Caddy.entries H π ↔ (Song.pennant H i).2∈π:=by
    unfold Caddy.entries
    simp only [mem_map_equiv,Equiv.symm_symm,mem_product,Finset.mem_univ,true_and]
  by_cases hit:(Song.pennant H i).2∈π
  · rw [if_pos (mem.mpr hit)]
    unfold portion Function.comp Song.choir
    dsimp only
    rw [if_pos hit];rfl
  · rw [if_neg (fun h=>hit (mem.mp h))]
    unfold portion Function.comp Song.choir
    dsimp only
    rw [if_neg hit]
    exact smul_zero _

def address (r q:ℕ)(π:Finset (Song.Magazine H))
    (houses:∀ i:Song.Magazine H,i∈π→∀x,Meadow.share H B x i≠0→
      (Beam.contents H B i).support⊆neighbors q x):
    Abacus.Rack X q (portion R S r π) where
  atW:=Caddy.entries H π
  seat i j:=Meadow.garnerAt H B j i
  bound i hi:=by rw [selected,if_neg hi]
  sums i _:=Meadow.paysOne H B i
  paid i _ x:=Meadow.nonnegative H B x i
  priced:= (Caddy.rack B Chi.canonical H S.identity α ∅ r q π houses).priced


theorem paid {r:ℕ}{ε:ℝ}(ep:0<ε)
    (h:CensusStep.Account R.kit H H S.identity r):
    ∀ᶠt:ℕ in atTop,let g:=portion R S r (catalogue R S t)
    let K:=Abacus.revise d g
    let E:=Abacus.revise d ((d).logRead-g)
    let w:=Time.forecastK R.alloy.B.a m R.kit.scout (U).beta
    Local X B K (Opera.earlyFee (p:=R.kit.expense) R.alloy.B N m (U).beta) w ∧
    Local X B E ((2*gStep (U).beta)^(r+1)+ε) w ∧
    E.logRead=(d).logRead-K.logRead ∧ E.hardRead=(d).hardRead ∧ K.hardRead=(d).hardRead:=by
  let k:=kept R.kit H H S.identity r
  let e:=discarded R.kit H H S.identity r
  let live (t i:ℕ):Prop:=i∈Caddy.entries H (catalogue R S t)
  have fin (i:ℕ)(_:k.logRead i≠0):∀ᶠt:ℕ in atTop,¬(¬live t i):=by
    filter_upwards [eventually_gt_atTop i] with t ht
    apply not_not.mpr
    unfold live Caddy.entries
    simp only [mem_map_equiv,Equiv.symm_symm,mem_product,Finset.mem_univ,true_and]
    exact mem_image.mpr ⟨i,mem_range.mpr ht,rfl⟩
  have tails:=Caddy.limits (A:=X) B (fun t i=>¬live t i) k.logRead (Abacus.charted B h.low) fin ep
  have pay:hardCost R.kit m≤Time.forecastK R.alloy.B.a m R.kit.scout (U).beta:=by
    have z:0≤Time.forecastK R.alloy.B.a m R.kit.scout (U).beta:=
      mul_nonneg (by exact le_trans zero_le_one (le_max_left ..)) (Real.exp_nonneg _)
    linarith only [WilsonVacuumPreResetStation.hard R S,z]
  filter_upwards [tails] with t ht
  intro g K E w
  have kg:Meadow.Budget B (X).reg g (Opera.earlyFee (p:=R.kit.expense) R.alloy.B N m (U).beta):=by
    change Meadow.Budget _ _ (portion R S r (catalogue R S t)) _
    rw [funext (selected R S r _)]
    convert Acquire.budget_cut (live t) (Abacus.charted B h.low) using 1
    funext i
    by_cases st:live t i <;> simp only [←show i∈Caddy.entries H (catalogue R S t) ↔ live t i from Iff.rfl]
  have eg:(d).logRead-g=e.logRead+(fun i=>@ite _ (¬live t i) (Classical.propDecidable _) (k.logRead i) 0):=by
    have full:(d).logRead=k.logRead+e.logRead:=h.recorded
    rw [full];funext i
    simp only [Pi.sub_apply,Pi.add_apply]
    rw [show g i=if live t i then k.logRead i else 0 from selected R S r _ i]
    by_cases st:live t i <;> simp [st,add_comm]
  have he:Meadow.Budget B (X).reg ((d).logRead-g) ((2*gStep (U).beta)^(r+1)+ε):=by
    rw [eg];exact Abacus.pay_bundle B (Abacus.charted B h.high) ht
  let a q:=if q∈catalogue R S t then Height.lower H S.identity Chi.canonical (lit R.kit H H S.identity r) α q else 0
  have rest:(d).logRead-g=Song.choir (fun i=>Song.opus H S.identity Chi.canonical α i-a i) ∘ Song.pennant H:=by
    funext i W;change Song.Rim _*_-Song.Rim _*_=Song.Rim _*(_-_);rw [mul_sub];rfl
  have lawful {D:ℕ → Pot G (R.family.side m per)}{b:ℝ}
      (price:Meadow.Budget B (X).reg D b)
      (moves:∀s z,Nonempty (((X).read (Abacus.revise d D)).Moves s z)):
      Local X B (Abacus.revise d D) b w:=by
    obtain ⟨u,hu,rows⟩:=price
    have hB:=VacuumListing.relax B h.fullSize le_rfl pay
    have F:=hB.family
    exact ⟨fun i=>(rows i).1,⟨F.sym,F.symtest,F.meas,F.meas_test,F.reads,F.reads_test,F.permit⟩,
      moves,⟨u,fun i=>(rows i).2,hu⟩,hB.expensive⟩
  refine ⟨lawful kg (fun s z=>Beam.moves H B Chi.canonical S.identity s z a),lawful he ?_,rfl,rfl,rfl⟩
  rw [rest];exact fun s z=>Beam.moves H B Chi.canonical S.identity s z (fun i=>Song.opus H S.identity Chi.canonical α i-a i)

end YM.Integration.WilsonVacuumPreResetCatalogue
