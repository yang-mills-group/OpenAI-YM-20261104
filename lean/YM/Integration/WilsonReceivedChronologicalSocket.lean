import YM.Integration.WilsonReceivedChronologicalBasis
import YM.Integration.WilsonOriginalCensusCanonicalRows

/-! The exact ordinary input of each original K socket in the finite public portfolio. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalSocket
open Finset Lattice Wilson RG Marker Multi QuadraticLocal Org AllOrder
open QuadraticLocal.Affinity QuadraticLocal.Earn QuadraticLocal.Mentor
open WilsonThermometerDeclaredSeeds XSpace PhysicalNext.Repeat.Legato
open WilsonOriginalCensusCanonicalRows (row probe)
open WilsonOriginalMixedBlockRows (room)
open WilsonReceivedCanonicalVersePortfolio (Selection)
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider OriginalMarkedSourceComet
open scoped Classical BigOperators
variable {G:Gauge}{V:Type}[Fintype V][DecidableEq V](R:Run G)(d:V→ℕ){h:V→ℕ}
local notation "J" => Stock.census V

/-- A proper face can be commissioned inside a complete named socket. -/
def extend (S:Finset V)(q:Selection R d S)(j:V):Choice R d j:=
  if hj:j∈S then q ⟨j,hj⟩ else Sum.inl ()

def lit:Wallet (room V):=fun _=>⟨1,by simp [room,WilsonRegisteredPairUnaryWallet.disk]⟩

def input (s:(J).Mode)(q:Selection R d s.val)(hd:∀j,0<d j){n:Side}
    (o:V→Site n)(σ:ℝ)(Y:RG.Rep G n)(g:ℝ)(U:Config G n):Poly (J):=
  ((Y.eval U:ℝ):ℂ) • Poly.pass (Spill.Foundry.uncut (row R d (extend R d s.val q) hd o σ) g lit U)

theorem ordinary (s:(J).Mode)(q:Selection R d s.val)(hd:∀j,0<d j){n:Side}
    (o:V→Site n)(σ:ℝ)(Y:RG.Rep G n)(g:ℝ)
    (κ:(j:V)→Knob (h j))(pt:V→Chamber)(U:Config G n):
    (input R d s q hd o σ Y g U).part s=(Y.eval U:ℂ)*
      WilsonReceivedCanonicalVersePosterior.word R d κ pt g o s.val q U:=by
  let z:=extend R d s.val q
  let M:=row R d z hd o σ
  let f:V→ℂ:=fun j=>WilsonReceivedCanonicalVerseBasis.restored R d κ pt g j (z j) (o j) U
  have source:Spill.Foundry.uncut M g lit U=∑j,WardBin.Lambda.fuse j (f j):=by
    unfold Spill.Foundry.uncut
    rw [tsum_fintype]
    apply sum_congr rfl
    intro j _
    change Poly.send ((J).fire j) ((M j).nominal g lit U)=_
    rw [WilsonOriginalCensusCanonicalRows.nominal R d z hd o σ κ pt]
    simp only [probe,lit,one_mul]
    rfl
  change ((((Y.eval U:ℝ):ℂ) • Poly.pass (Spill.Foundry.uncut M g lit U)).part s)=_
  rw [source,Poly.part_smul,WardBin.Lambda.passion,WardBin.Lambda.expend]
  change (Y.eval U:ℂ)*(∏j∈s.val,f j)=_
  rw [←prod_coe_sort]
  congr 1
  apply Fintype.prod_congr
  intro j
  simp only [f,z,extend,dif_pos j.property]
end YM.Integration.WilsonReceivedChronologicalSocket
end
