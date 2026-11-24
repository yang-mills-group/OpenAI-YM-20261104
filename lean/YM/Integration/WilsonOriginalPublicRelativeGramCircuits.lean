import YM.Integration.WilsonOriginalPublicRelativeGramGrid
import YM.Integration.WilsonOriginalPublicNodalNodes

/-! The two Wilson insertions at each public reference or comparison pin use the
same positions and the same enrolled doses as the finite regulated hearing. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramCircuits
open Finset Function Lattice Wilson RG Source Labels Marker QuadraticLocal.Affinity PhysicalNext.Repeat.Legato
open Pert.Asymptotics RegulatorIR.FVAAlt2 XSpace XSpace.Normalize XSpace.Rose Cells
open WilsonOriginalBlissMixedGram (grades columns)
open WilsonOriginalPublicRelativeGramPins (physical cutoff)
open WilsonOriginalPublicRelativeGramPosted (Dated issued submitted)
open WilsonOriginalPublicNodalEntry (dose Issued)
open WilsonOriginalPublicNodalNodes (primitive)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(W:Initialize G){I L:Type}[Fintype I][Fintype L]
  (a:Axis)(d:I→ℕ)(site:ℕ)(addresses:L→Fin 2→ Cover)(μ:L→ℂ)
  (Y:Bool→(ℕ×ℕ)→(i:I)→R.family.label (d i))(sale:Dated (L:=L) R W d)
  (t:Bool){N per K u:ℕ}(i j:I)

local notation "z₀" => ((N,per):ℕ×ℕ)
local notation "g₀" => regulatorRun R.family N per K

def word (m:L)(U:Config G (R.family.side N per)):ℂ:=
  ∏k:Fin 2, R.family.O N per (columns R a (d i) (d j) (Y false z₀ i) (Y t z₀ j) k)
    (Cells.location R.family.S site N per (addresses m k)) U

local notation "line" => word R a d site addresses Y t (N:=N) (per:=per) i j

omit [Fintype I] [Fintype L] in
theorem expectation (m:L):R.family.omega N per (line m)=physical R a d site addresses Y t z₀ i j m:=rfl

variable (inFields:∀k,R.family.label ((grades (d i) (d j)) k))(lanes:Fin 2→ℂ)
  (wallet:Wallet (WilsonOriginalAlternativeFiniteSource.disks (V:=Fin 2)))
  (mode:(Stock.census (Fin 2)).Mode)
  (fk:site≤K)(high:K≤N)(ear:u≤K)
local notation "root" m:max k:max => (R.family.S.toDepth fk per).embed (wrap (R.family.side site per) (addresses m k))
local notation "nodes" => sale.nodes z₀
local notation "chart" => dose R (grades (d i) (d j)) (N:=N) (K:=K) (per:=per) inFields lanes wallet

omit [Fintype I] in
include inFields lanes wallet ear fk high in
theorem priced (full:mode.val=univ)
    (position:∀m,∀k:mode.val,wrap (R.family.side K per) ((nodes m).layout k)=root m k)
    (file:chart=issued R W d sale t z₀ i j)
    (sameClock:sale.g z₀=g₀)(sameMass:sale.mass z₀=μ)
    (fee:L→ℝ)(bought:∀m,Issued R (grades (d i) (d j)) (fun k=>root m k) inFields lanes wallet mode high ear (line m) (fee m))
    (A B:ℝ)
    (phase:∀m,‖WilsonOriginalTwoFlatGridScaling.gap R N per u (ear.trans high) (line m)‖≤A)
    (rent:∀m,fee m≤B):
    ‖cutoff R a d site addresses μ Y t z₀ i j-submitted R W d sale t z₀ i j‖≤
      (∑m,‖μ m‖)*(A+B)+‖∑m,μ m*primitive R W (grades (d i) (d j)) (N:=N) (per:=per) inFields lanes wallet mode nodes ear sale.q m‖:=by
  have quote:=WilsonOriginalPublicNodalNodes.priced R W (grades (d i) (d j)) inFields lanes wallet mode nodes μ
    (fun m k=>root m k) position high ear line fee bought sale.q A B phase rent
  rw [file,full] at quote
  simpa only [cutoff,← expectation,sameMass,sameClock,submitted] using quote

end YM.Integration.WilsonOriginalPublicRelativeGramCircuits
