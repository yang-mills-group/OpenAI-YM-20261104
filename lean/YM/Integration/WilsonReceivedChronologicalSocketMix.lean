import YM.Integration.WilsonReceivedChronologicalSocket
import YM.Integration.WilsonReceivedChronologicalMixture

/-! Reuse every independently commissioned K socket in its own paid chronological rows. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalSocketMix
open Function Finset Filter MeasureTheory Lattice Wilson RG Labels Source Marker Multi
open QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Mentor QuadraticLocal.Affinity Org AllOrder XSpace
open PhysicalNext.Repeat.Legato WilsonThermometerDeclaredSeeds OriginalMarkedSourceComet
open MergeProof.Accent Pert.Asymptotics
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open WilsonReceivedCanonicalVersePortfolio (Selection)
open WilsonReceivedCanonicalVersePosterior (word smooth)
open WilsonOriginalMicroscopicEntranceGridRow (pin)
open WilsonReceivedChronologicalBasis (fare)
open WilsonReceivedChronologicalSocket (extend input lit)
open WilsonReceivedChronologicalMixture (mix)
open WilsonOriginalJointTrialHearing (fee read)
open WilsonOriginalCensusCanonicalRows (row probe)
open Extra.Histories OPE.Therm
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(d:Fin 3→ℕ){h:Fin 3→ℕ}
variable (κ:(j:Fin 3)→Knob (h j))(pt:Fin 3→Chamber)
variable {N per f n:ℕ}
local notation "X" j:max => Config G (R.family.side j per)
local notation "J" => Stock.census (Fin 3)
local notation "K" => f+n
local notation "fk" => Nat.le_add_right f n
variable (o:Fin 3→Site (R.family.side f per))(v:∀a:Fin 3,R.family.label (d a))(c:Fin 3→ℂ)
local notation "g" => regulatorRun R.family N per K
local notation "Y" => R.family.path.rep N per K
local notation "home" => pin R fk o

def plant (s:(J).Mode)(q:Selection R d s.val)(U:X K):Poly J:=
  fun t=>(Y).eval U • word R d κ pt (g) (home) t.val (fun j=>extend R d s.val q j) U

local notation "plant₀" => plant R d κ pt (N:=N) (n:=n) o
variable (past:∀s:(J).Mode,Selection R d s.val→∀j:ℕ,Config G (R.family.side j per)→Poly (Stock.census (Fin 3)))
local notation "weights" => fare R d v c N per K

def branch {day:ℕ}(before:∀j:ℕ,Config G (R.family.side j per)→Poly (Stock.census (Fin 3)))
    (top:Config G (R.family.side day per)→Poly (Stock.census (Fin 3))):
    ∀j:ℕ,Config G (R.family.side j per)→Poly (Stock.census (Fin 3)):=Function.update before day top

def stock {day:ℕ}(seed:∀s:(J).Mode,Selection R d s.val→X day→Poly J)
    (old:∀s:(J).Mode,Selection R d s.val→∀j:ℕ,X j→Poly J)
    (s:(J).Mode)(q:Selection R d s.val):∀j:ℕ,X j→Poly J:=branch R (old s q) (seed s q)

theorem commissioned (s:(J).Mode)(q:Selection R d s.val)(hd:∀j,0<d j)(σ:ℝ)(U:X K):
    input R d s q hd (home) σ (Y) (g) U=(plant₀) s q U:=by
  let z:=extend R d s.val q
  let M:=row R d z hd (home) σ
  let F:Fin 3→ℂ:=fun j=>WilsonReceivedCanonicalVerseBasis.restored R d κ pt (g) j (z j) ((home) j) U
  have source:Spill.Foundry.uncut M (g) lit U=∑j,WardBin.Lambda.fuse j (F j):=by
    unfold Spill.Foundry.uncut
    rw [tsum_fintype]
    apply sum_congr rfl
    intro j _
    change Poly.send ((J).fire j) ((M j).nominal (g) lit U)=_
    rw [WilsonOriginalCensusCanonicalRows.nominal R d z hd (home) σ κ pt]
    simp only [probe,WilsonReceivedChronologicalSocket.lit,one_mul]
    rfl
  apply Marker.Poly.ext
  intro t
  change ((((Y).eval U:ℝ):ℂ) • Poly.pass (Spill.Foundry.uncut M (g) lit U)).part t=_
  rw [source,Poly.part_smul,WardBin.Lambda.passion,WardBin.Lambda.expend]
  change ((Y).eval U:ℂ)*(∏j∈t.val,F j)=(_ :ℝ) • _
  rw [←prod_coe_sort,Complex.real_smul]
  rfl

theorem whole (active:K≤N)(hd:∀j,0<d j):
    WilsonReceivedChronologicalPlant.rows R d (N:=N) (n:=n) o v c (mix R (weights) past)=
      mix R (weights) (stock R d (plant R d κ pt (N:=N) (n:=n) o) past):=by
  funext j W s
  by_cases date:j=K
  · subst j
    rw [WilsonReceivedChronologicalPlant.rows,Function.update_self]
    change (WilsonReceivedChronologicalPlant.top R d (N:=N) (n:=n) o v c W).part s=∑q:Selection R d s.val,(weights) s q*((stock R d (plant R d κ pt (N:=N) (n:=n) o) past) s q K W).part s
    rw [WilsonReceivedChronologicalBasis.top R d κ pt o v c active s W]
    apply sum_congr rfl
    intro q _
    rw [stock,branch,Function.update_self,←commissioned R d κ pt o s q hd 1,
      WilsonReceivedChronologicalSocket.ordinary R d s q hd (home) 1 (Y) (g) κ pt W]
  · unfold WilsonReceivedChronologicalPlant.rows mix stock branch
    simp only [Function.update_of_ne date]

theorem eligible (active:K≤N)(s:(J).Mode)(q:Selection R d s.val):
    Integrable ((plant₀) s q) (prior G _):=by
  apply integrable_pi_iff.mpr
  intro t
  let A:=word R d κ pt (g) (home) t.val (fun j=>extend R d s.val q j)
  have smoothA:Continuous A:=smooth R d κ pt (g) (home) t.val _
  obtain ⟨M,cost⟩:=isCompact_univ.exists_bound_of_continuousOn smoothA.continuousOn
  have paid:=actualTransport_weighted_integrable R.family R.makes active smoothA.aestronglyMeasurable
    (fun U=>cost U (Set.mem_univ U)) (le_rfl:K≤K)
  simpa only [plant,actualTransport_base R.family R.makes active] using paid

theorem income (active:K≤N){j:ℕ}
    (older:∀s q,j≠K→Integrable (past s q j) (prior G _)):
    ∀s q,Integrable ((stock R d (plant R d κ pt (N:=N) (n:=n) o) past) s q j) (prior G _):=by
  intro s q
  by_cases eq:j=K
  · subst j
    rw [stock,branch,Function.update_self]
    exact eligible R d κ pt o active s q
  · rw [stock,branch,Function.update_of_ne eq]
    exact older s q eq

theorem original (active:K≤N)(hd:∀j,0<d j){b i:ℕ}(bi:b ≤ i)(W:X b)(s:(J).Mode)
    (older:∀ (j:ℕ), b ≤ j → j < K → ∀ s q, Integrable (past s q j) (prior G _))(activei:i + 1 ≤ K):
    WilsonOriginalJointTrialHearing.fee R N per W (WilsonReceivedChronologicalPlant.rows R d (N:=N) (n:=n) o v c (mix R (weights) past)) i s=
      ∑q:Selection R d s.val,(weights) s q*WilsonOriginalJointTrialHearing.fee R N per W ((stock R d (plant R d κ pt (N:=N) (n:=n) o) past) s q) i s:=by
  rw [whole R d κ pt o v c past active hd]
  exact WilsonReceivedChronologicalMixture.original R (weights) (stock R d (plant R d κ pt (N:=N) (n:=n) o) past) bi W s
    (income R d κ pt o past active fun t q h=>older _ (by omega) (by omega) t q)
    (income R d κ pt o past active fun t q h=>older _ bi (by omega) t q)
end YM.Integration.WilsonReceivedChronologicalSocketMix
end
