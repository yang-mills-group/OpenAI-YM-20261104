import YM.Integration.WilsonRootedPhysicalHousing

/-! Uniform cover truncation of the genuine physical pre-reset roster. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedPhysicalShortLog
open Function Filter Finset Set Lattice Wilson RG RG.Shoot Pressure
open Push Push.AbsoluteSums Push.AbsoluteSums.Animals Gas Ursell Trees Shoot Precision SectorMeasure Oriented
open AnalyticBridge VerifiedReset Collection Quotes PhysicalNext PhysicalNext.Repeat Legato
open ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.Blaze Blaze.March Captain
open Opera Height Beam Song Greenbelt Next.Scheduling Extra.Iteration UVNext
open PriceCompiler Org Input Supply Pressure.Testing Time Roost Match Refrain WilsonStartup
open RG01Estimate RG01Estimate.CensusStep WilsonLimitConstruction.FundedCensusVacuum
open WilsonVacuumPreResetCatalogue WilsonRootedPhysicalHousing
open scoped Topology BigOperators Classical

variable {G : Gauge} (R : Run G) {m N per : ℕ} (S : Station R N per m)
local notation "H" => S.guide
local notation "B" => R.alloy.B.a.budget m
local notation "L₀" => ledger R.kit H
local notation "d" => vacuum R.kit H H S.identity
local notation "α" => R.alloy.B.kin.alpha N m
local notation "U" => R.family.path.rep N per (m+1)

def tariff (cap period level : ℕ) := turnFee (WilsonRootedPhysicalPathCover.regularPoint (R.alloy.B.a.budget level))*
  WilsonRootedPhysicalCatalogue.gross R cap period level

lemma long (salary : WilsonOriginalHighSelection.Salary G R.kit) (hm : m<N) {r : ℕ}
    (h : CensusStep.Account R.kit H H S.identity r) (D : ℕ) :
    Meadow.Budget B (L₀).reg (fun i=>if D+1≤coverNumber (B).B ((L₀).reg i).support
      then (kept R.kit H H S.identity r).logRead i else 0)
      (Real.exp (-(1:ℝ)*(D+1))*tariff R N per m) := by
  obtain ⟨f,rows,quote⟩:=WilsonRootedPhysicalCatalogue.orbit R S salary hm r
  let len i:=coverNumber (B).B ((L₀).reg i).support
  have boost : Quotes.early B (L₀).reg (fun i=> f i*Real.exp (1*(len i:ℝ))) (tariff R N per m) :=by
    intro x
    convert quote x using 1
    funext i
    dsimp only
    split_ifs
    · rw [mul_assoc,←Real.exp_add]
      congr 2
      dsimp [len]
      ring
    · rfl
    rfl
  have ht:=Meadow.arch_tail (k:=D+1) (σ:=1) (L₀).reg B len boost (by norm_num) (fun i=>(rows i).1)
  refine ⟨fun i=>if D+1≤len i then f i else 0,?_,?_⟩
  · simpa only [Nat.cast_add,Nat.cast_one] using ht
  · intro i
    by_cases active : D+1≤len i
    · simp only [show D+1≤coverNumber (B).B ((L₀).reg i).support from active,active,if_true]
      exact ⟨h.low.smooth i,rows i⟩
    · simp only [show ¬D+1≤coverNumber (B).B ((L₀).reg i).support from active,active,if_false]
      exact ⟨CouplingShape.reg_const _,by simpa only [abs_zero] using!
        (CouplingShape.sup_const (G:=G) (p:=B) (o:=((L₀).reg i).site) (X:=((L₀).reg i).support) 0)⟩

private lemma placed (π : Finset (Magazine H)) (i : ℕ) : i∈Caddy.entries H π ↔ (pennant H i).2∈π :=by
  unfold Caddy.entries
  simp only [mem_map_equiv,Equiv.symm_symm,mem_product,Finset.mem_univ,true_and]

lemma spatialPart (salary : WilsonOriginalHighSelection.Salary G R.kit) (hm : m<N) {r : ℕ}
    (h : CensusStep.Account R.kit H H S.identity r) (D t : ℕ) :
    Meadow.Budget B (L₀).reg (portion R S r (catalogue R S t)-portion R S r (WilsonRootedPhysicalHousing.spatial R S t D))
      (Real.exp (-(1:ℝ)*(D+1))*tariff R N per m) :=by
  let live (i:ℕ):Prop:=i∈Caddy.entries H (catalogue R S t)
  have hx (i) : i∈Caddy.entries H (WilsonRootedPhysicalHousing.spatial R S t D) ↔ live i ∧ coverNumber (B).B ((L₀).reg i).support≤D:=by
    rw [placed R S,WilsonRootedPhysicalHousing.charge R S i]
    unfold live WilsonRootedPhysicalHousing.spatial
    rw [placed R S,Finset.mem_filter]
  convert Acquire.budget_cut live (long R S salary hm h D) using 1
  funext i
  simp only [Pi.sub_apply,WilsonVacuumPreResetCatalogue.selected]
  by_cases a : i∈Caddy.entries H (catalogue R S t)
  · have ha : live i:=a
    by_cases b:coverNumber (B).B ((L₀).reg i).support≤D
    · have c:=(hx i).mpr ⟨ha,b⟩
      have nb : ¬D+1≤coverNumber (B).B ((L₀).reg i).support:=by omega
      simp only [a,c,ha,nb,if_pos,if_false,sub_self]
    · have c: i∉Caddy.entries H (WilsonRootedPhysicalHousing.spatial R S t D):=fun h=>b ((hx i).mp h).2
      have nb:D+1≤coverNumber (B).B ((L₀).reg i).support:=by omega
      simp only [a,c,ha,nb,if_false,if_true,sub_zero]
  · have ha : ¬live i:=a
    have c: i∉Caddy.entries H (WilsonRootedPhysicalHousing.spatial R S t D):=fun h=>ha ((hx i).mp h).1
    simp only [a,c,ha,if_false,sub_self]

/-- One cutoff on the real support, keeping the genuine old hard family on both admitted sources. -/
theorem original (salary : WilsonOriginalHighSelection.Salary G R.kit) (hm : m<N) {r : ℕ}
    (h : CensusStep.Account R.kit H H S.identity r) (D : ℕ) {η : ℝ} (eη : 0<η) :
    ∀ᶠt:ℕ in atTop,let g:=portion R S r (WilsonRootedPhysicalHousing.spatial R S t D)
    let b:=Opera.earlyFee (p:=R.kit.expense) R.alloy.B N m (U).beta
    let w:=Time.forecastK R.alloy.B.a m R.kit.scout (U).beta
    Local L₀ B (Abacus.revise d g) b w ∧
    Local L₀ B (Abacus.revise d ((d).logRead-g))
      (((2*gStep (U).beta)^(r+1)+η)+Real.exp (-(1:ℝ)*(D+1))*tariff R N per m) w ∧
    Nonempty (Abacus.Rack L₀ (WilsonRootedPhysicalHousing.radius B D) g) :=by
  filter_upwards [WilsonVacuumPreResetCatalogue.paid R S eη h] with t bill
  intro g b w
  obtain ⟨_,old,_⟩:=bill
  have kg : Meadow.Budget B (L₀).reg g b:=by
    change Meadow.Budget _ _ (portion R S r _) _
    rw [funext (WilsonVacuumPreResetCatalogue.selected R S r _)]
    convert Acquire.budget_cut (fun i=>i∈Caddy.entries H (WilsonRootedPhysicalHousing.spatial R S t D))
      (Abacus.charted B h.low) using 1
    funext i
    by_cases a:i∈Caddy.entries H (WilsonRootedPhysicalHousing.spatial R S t D) <;> simp [a]
  have eg:=Abacus.pay_bundle B (Abacus.charted B old) (spatialPart R S salary hm h D t)
  change Meadow.Budget B (L₀).reg (((d).logRead-portion R S r (catalogue R S t))+
    (portion R S r (catalogue R S t)-g)) _ at eg
  rw [sub_add_sub_cancel] at eg
  let q (i:Magazine H):=if i∈WilsonRootedPhysicalHousing.spatial R S t D then Height.lower H S.identity Chi.canonical
    (lit R.kit H H S.identity r) α i else 0
  have rest : (d).logRead-g=Song.choir (fun i=>Song.opus H S.identity Chi.canonical α i-q i) ∘ pennant H:=by
    funext i W
    change Song.Rim _*_-Song.Rim _*_=Song.Rim _*(_-_)
    rw [mul_sub];rfl
  have build {f:ℕ→Pot G (R.family.side m per)} {c:ℝ} (pay:Meadow.Budget B (L₀).reg f c)
      (moves:∀s z,Nonempty (((L₀).read (Abacus.revise d f)).Moves s z)) :
      Local L₀ B (Abacus.revise d f) c w:=by
    obtain ⟨u,hu,rows⟩:=pay
    have F:=old.family
    exact ⟨fun i=>(rows i).1,⟨F.sym,F.symtest,F.meas,F.meas_test,F.reads,F.reads_test,F.permit⟩,
      moves,⟨u,fun i=>(rows i).2,hu⟩,old.expensive⟩
  refine ⟨build kg (fun s z=>Beam.moves H B Chi.canonical S.identity s z q),build eg ?_,⟨WilsonRootedPhysicalHousing.rack R S r D t⟩⟩
  rw [rest]
  exact fun s z=>Beam.moves H B Chi.canonical S.identity s z (fun i=>Song.opus H S.identity Chi.canonical α i-q i)

end YM.Integration.WilsonRootedPhysicalShortLog
