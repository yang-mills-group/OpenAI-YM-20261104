import YM.Integration.WilsonIndependentSpoutMasterCash
import YM.Integration.WilsonIndependentSpoutMasterBufferedWindow
import YM.Integration.WilsonIndependentMatchedPhysicalReportedCash

/-! The funded physical old vacuum, the buffered normalized vacuum and the fresh normalized opening at one reporting coupling. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutMasterObserved
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonIndependentMatchedPhysicalReportedSample (value)
open WilsonIndependentMatchedPhysicalSector (stamp)
open WilsonIndependentMatchedPhysicalReturn (ordinary)
open WilsonIndependentMatchedBufferedVacuum (stopped)
open WilsonIndependentSpoutScalarLedger (ground)
open WilsonIndependentSpoutMasterReport (report)
open WilsonPositionProgramTrialHomeFaces (Outcome)
open WilsonPositionProgramTrialAccrued (home)
open WilsonPositionProgramNormalizedMaster (fee)
open WilsonIndependentFittedRosterCash (numerical reserve)
open WilsonIndependentFittedMixedCash (embed)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open scoped Classical BigOperators Topology
variable {G:Gauge}{n e k u₀ u:ℕ}

def observed (L:Levels G)(O:ChartRatio G)(N m host q:ℕ)(g:ℝ)(Y:Era G ℝ):ℂ:=
  cash q g (embed (report L O N m host (ground Y)))

theorem cash_sub (q:ℕ)(g:ℝ)(F H:Cost):cash q g (embed (F-H))=cash q g (embed F)-cash q g (embed H):=by
  simp only [WilsonPhysicalMarkedDefect.RawBank.cash,map_sub,mul_sub,Finset.sum_sub_distrib]

theorem source (L:Levels G)(O:ChartRatio G)(N m host q:ℕ)(g:ℝ)(X Y:Era G ℝ):
    observed L O N m host q g X-observed L O N m host q g Y=
      (value L O N m host q g Fin.elim0 (X-Y):ℂ):=by
  have one Z:observed L O N m host q g Z=(value L O N m host q g Fin.elim0 Z:ℂ):=
    WilsonIndependentMatchedPhysicalReportedSample.original L O N m host q g Fin.elim0 Z
  rw [one,one,map_sub,Complex.ofReal_sub]

theorem three (x y z w:ℂ){A B C:ℝ}(a:‖x-y‖ ≤ A)(b:‖y-z‖ ≤ B)(c:‖z-w‖ ≤ C):‖x-w‖ ≤ A+B+C:=by
  rw [show x-w=(x-y)+(y-z)+(z-w) by abel]
  exact (norm_add_le ..).trans (add_le_add ((norm_add_le ..).trans (add_le_add a b)) c)

variable (R:Run G)(d D:Fin (n+1)→ℕ)(cut:∀i,d i<D i)
local notation "Q" => deck (G:=G) d D cut
local notation "L" => R.family.path.levels
local notation "O" => R.metals.O
local notation "credit" => Credit.leanC

def cutoff (C W T:Credit)(v m K q:ℕ)(g Z:ℝ)(B:Fin (n+1)→ℝ)(b:Herit Q):ℝ:=
 (numerical q g b+((Fintype.card (Fin (n+1)):ℝ)+1)*|g|^(q+1)*reserve q b)*
 ((∑i∈range (q+1),WilsonIndependentSpoutMasterReportedBasis.price R C W T v m i Z B)*trailC (L).S m K)

theorem original (simple:G.Simple)(own:∀i,Rails (Q i).h k u₀ e)(b out:ℕ)
    (width:u+b ≤ u₀)(stage:(n+1)*k ≤ out)(spread:1 ≤ (b:ℝ)-((∑s,(Q s).h:ℕ):ℝ)-((n+1:ℕ):ℝ)/4):
    ∃(pri:Fin (n+1)→Credit)(mid last:(Fin (n+1)→Bool)→Credit),∀(j:ℕ)(C W T D':Credit),
    WilsonIndependentSpoutMasterCutoff.Earned R d D cut j e u C W →
    WilsonIndependentSpoutMasterClockFees.Paid R j e T → WilsonIndependentSpoutMasterAppointments.Grants R d D cut j →
    WilsonIndependentSpoutMasterUpperClocks.Paid R j e D' → ∀(v m K:ℕ)(B cap:Fin (n+1)→ℝ)(Z:ℝ),
    j ≤ v → v ≤ m → m ≤ K → Compar (L).S (zz L) v m ≤ Z →
    ∀(q:ℕ)(ε:ℝ),q ≤ e → 0<ε → ∀ᶠ U:ℕ in atTop,K ≤ U ∧ ∀(N M:ℕ)(V:Realm G (e+1) credit)
      (X:∀i,CutsP (hol G) (Q i).ans (Q i).path (own i) credit credit credit credit),
    U ≤ N → U ≤ M → stamp V X m K N → V.draws=L → V.paid=O → V.anchor ≤ v →
    SpringD V out u b credit → (∀l ≤ out,Dormitory V l u credit) → (∀i,On (Q i).h (X i).pt) →
    let selected:=fun i=>home (Q i) (X i)
    (∀i,fee selected e i ≤ cap i) → Outcome Q V.draws V.paid selected m K N M v e u B Z ε →
    ∀(F:Wilt Q)(y:ℝ)(o:CellR),Bough Q F y Z B → ∀g:ℝ,|g|≤1 →
    let old:=cruises L O N (capP Q) K v (ordinary L X F m K y o)
    let fresh:=stopped L O Q F selected m K K v y o
    let price:=T.buy (Compar R.family.S (zz L) v m)
    ‖observed L O N m v q g old-observed L O K m v q g fresh‖ ≤
      WilsonIndependentMatchedPhysicalReportedCash.price V X u b out v m K q pri mid last Z g price B+
      WilsonIndependentMatchedPhysicalReportedClock.bill q price ε+ε+cutoff R d D cut C W T v m K q g Z B selected:=by
  obtain ⟨pri,mid,last,actual⟩:=WilsonIndependentMatchedPhysicalReportedCash.released (hol G) Q own u b out width stage spread
  refine ⟨pri,mid,last,?_⟩
  intro j C W T D' sale clocks fields earlier v m K B cap Z beginAt vm mk optic q ε depth eps
  filter_upwards [WilsonIndependentSpoutMasterBufferedWindow.paid R d D cut sale earlier v m K B cap Z beginAt vm mk optic q depth ε eps] with U working
  refine ⟨working.1,?_⟩
  intro N M V X live twin filed levels ratio active spring dorm lawful selected salaries moved F y o fit g small
  let buffered:=stopped L O Q F selected m K M v y o
  have first:=actual R clocks V X v m K N M B Z ε filed levels ratio beginAt active vm mk (working.1.trans live)
    spring dorm lawful eps.le moved F y o fit q g depth small Fin.elim0
  rw [levels,ratio] at first
  have entered:=working.2 N M selected F y o live twin salaries fit g small
  have structural:=WilsonIndependentSpoutMasterCash.original R d D cut simple sale clocks fields v m K M selected F B Z y o
    beginAt vm mk (working.1.trans twin) optic fit q depth g small
  apply three _ (observed L O N m v q g buffered) (observed L O M m v q g buffered) _
  · rw [source,Complex.norm_real]
    exact first
  · unfold observed
    rw [←cash_sub]
    exact entered
  · unfold observed
    rw [←cash_sub]
    exact structural
end YM.Integration.WilsonIndependentSpoutMasterObserved
end
