import YM.Integration.WilsonReceivedChronologicalFixedRoseWholeSalary
import YM.Integration.WilsonOriginalObservedRoseVaneCaliber

/-! A finite audit record for the original dated face. Its four written bills and its
two hired endpoint budgets use the same filed source, physical K and old N quiet. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalFixedRoseFittedDebit
open Function Filter Finset Lattice Wilson RG Pert.Asymptotics PhysicalNext.Repeat.Legato
open WilsonReceivedCanonicalVersePortfolio (wallet)
open WilsonThermometerPositionTunedSlope (Columns)
open WilsonOlderFreshSoftSocketMeasuredCash (packet)
open WilsonReceivedChronologicalLastFlat (wage)
open WilsonMeasuredPublicEntrancePanel (Panel)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonOriginalObservedRoseCorrectedWords (votes)
open WilsonReceivedChronologicalFixedRoseFigureTerms (Account)
open WilsonOriginalObservedRoseVanePurse (ages)
open WilsonOriginalObservedRoseMeshHeight (height)
open WilsonAddressedHomeDose (ceiling)
open scoped Topology BigOperators Classical
variable {G:Gauge}{n:ℕ}

structure Plan (n:ℕ) where
  powers : Fin n→ℕ
  width : ℕ
  pole : ℕ
  appointment : ℕ
  switchOrder : ℕ
  middleOrder : ℕ
  cutoffOrder : ℕ
  topOrder : ℕ
  switchPole : ℕ
  terminalPole : ℕ
  count : ℕ
  terminalOrder : ℕ
  tuition : ℝ
  captureRoof : ℝ
  support : ℝ
  interiorRate : ℝ
  boundaryRate : ℝ
  terminalRoof : ℝ

def Plan.Affords (P:Plan n)(t bank mesh size:ℕ):Prop:=
  0≤P.tuition ∧ t+2≤P.cutoffOrder ∧ t+2+2*P.pole*n≤P.appointment ∧
    t+2+2*P.pole*n≤P.switchOrder ∧ t+2+2*P.pole*n≤P.middleOrder ∧
      t+2+bank+(mesh*size+1)≤P.terminalOrder

def face (s:Finset (Fin n)):(Stock.census (Fin n)).Mode:=⟨s,mem_univ _⟩

variable (R:Run G)(d:Fin n→ℕ)(P:Plan n)
local notation "H" => R.family.path.levels.clock.hatBeta
local notation "g" => regulatorRun R.family

def due (K:ℕ)(s:Finset (Fin n)):ℝ:=wallet R d (fun _=>P.tuition*(H K)^P.pole) s

def low (K N per v:ℕ)(s:Finset (Fin n)):ℝ:=due R d P K s*
  (WilsonOriginalOneArmClearCash.wage (face s) P.appointment P.boundaryRate*(g N per v)^P.appointment)

def high (K N per v:ℕ)(s:Finset (Fin n)):ℝ:=due R d P K s*
  (wage (face s) P.appointment 1 P.boundaryRate*(g N per v)^P.appointment)

def written {f K N per request tag:ℕ}{fk:f≤K}{kn:K≤N}
    (panel:Panel R d N per f K fk kn request P.pole tag P.tuition)(file:Filed R d K)
    (v c:ℕ)(s:Finset (Fin n))(incumbent independent basal firstStep:ℂ):Account where
  incumbent:=incumbent
  independent:=independent
  basal:=basal
  firstStep:=firstStep
  cutoff:=(∏i∈s,ceiling (R:=R) (d i) (panel.M i))*((H f)^P.cutoffOrder)⁻¹
  interior:=due R d P K s*((4*((2*P.width:ℕ):ℝ)/Real.log 3)*
    wage (face s) P.appointment 1 P.interiorRate*(g N per v)^P.middleOrder)
  crossing:=due R d P K s*(WilsonOriginalTwoFlatIRSocketRose.charge R d P.powers P.appointment P.captureRoof
    P.support P.switchPole (face s)*(g N per c)^P.switchOrder)
  terminal:=((∑b:Columns R (fun i:s=>d i.val),‖packet R d s
    (votes R d (N:=N) (per:=per) file panel.names panel.turn) N per K b‖)*
    WilsonOlderFreshSoftSocketCensus.fee R d s)*((g N per v)^P.terminalOrder*
      WilsonOriginalTwoFlatIRSocketPower.ceiling n P.topOrder (∑i,d i) P.terminalPole P.count P.terminalRoof)

theorem original (R:Run G)(simple:G.Simple)(p:Plan 3)(t bank mesh:ℕ)(affords:p.Affords t bank mesh 14)
    (M:Fin 3→ℝ)(one:∀i,1≤M i)(C:Finset (Fin 3)→ℝ)(cp:∀s,0≤C s):
    ∀ᶠv:ℕ in atTop,∀s:Finset (Fin 3),∀{c f K N per:ℕ},0<v→v≤c→c≤f→∀(fk:f≤K)(kn:K≤N),
    R.family.S.scale K-R.family.S.scale (v-1)≤(p.width:ℝ)*(1+Real.log (R.family.path.levels.clock.hatBeta v)) →
    ∀{request tag:ℕ}(panel:Panel R ages N per f K fk kn request p.pole tag p.tuition)(file:Filed R ages K),
    panel.M=M → ∀r:ℝ,0≤r → r≤1 →
    let h:=height ages s
    let z:=(regulatorRun R.family N per v)⁻¹
    let w:=votes R ages (N:=N) (per:=per) file panel.names panel.turn
    r^h*(∑b:Columns R (fun i:s=>ages i.val),‖packet R ages s w N per K b‖)≤C s*z^bank*z^(mesh*h+1) →
    ∀a b x y:ℂ,let entry:=written R ages p panel file v c s a b x y
    r^h*((entry.cutoff+entry.interior+entry.crossing+low R ages p K N per v s+high R ages p K N per v s)+entry.terminal)≤
      (regulatorRun R.family N per v)^t:=by
  rcases affords with ⟨tuition,cut,ore,sw,mo,te⟩
  apply Filter.eventually_all.mpr
  intro s
  have hs:(∑i∈s,ages i)=height ages s:=by
    exact (Finset.sum_coe_sort s ages).symm
  have room:t+1+1+bank+(mesh*(∑i∈s,ages i)+1)≤p.terminalOrder:=by
    rw [hs]
    exact (Nat.add_le_add_left (Nat.add_le_add_right (Nat.mul_le_mul_left mesh
      (WilsonOriginalObservedRoseVaneCaliber.height_le s)) 1) _).trans te
  filter_upwards [WilsonReceivedChronologicalFixedRoseWholeSalary.original R simple ages p.powers (face s) M one
    p.width p.pole p.appointment p.switchOrder p.middleOrder p.cutoffOrder p.topOrder p.switchPole p.terminalPole p.count
    bank mesh p.terminalOrder t p.tuition p.captureRoof p.support p.interiorRate p.boundaryRate p.terminalRoof (C s)
    tuition (cp s) cut ore sw mo room] with v grant
  intro c f K N per vp vc cf fk kn span request tag panel file elected r rp small h z w cash a b x y entry
  have result:=grant (per:=per) vp vc cf fk kn span panel file elected r rp small
  dsimp only [face] at result
  rw [hs] at result
  exact result cash

end YM.Integration.WilsonReceivedChronologicalFixedRoseFittedDebit
