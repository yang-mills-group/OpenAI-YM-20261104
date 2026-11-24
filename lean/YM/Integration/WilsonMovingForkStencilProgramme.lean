import YM.Integration.WilsonMovingForkRegisteredMaterial
import YM.Integration.WilsonMovingForkPrintedFile
import YM.Integration.WilsonReceivedCanonicalVersePosterior

/-! The finite measured K basis issues one complete ordinary row per stencil.
The coefficients are taken after the true inverse on the previously filed matrices. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkStencilProgramme
open Function Finset Lattice Wilson RG Source Labels Marker Trace.Pilot OPE
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open PhysicalNext.Repeat.Legato Pert.Asymptotics WilsonOriginalMixedBlockRows
open WilsonMovingForkPrintedFile (Board parent allSlots)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMovingForkMixedSeed (doses units product)
open WilsonReceivedCanonicalVersePortfolio (Selection weight)
open WilsonReceivedCanonicalVersePosterior (word)
open scoped Classical BigOperators

variable {G:Gauge}{R:Run G}{n K:ℕ}{d h:Fin n→ℕ}

abbrev Basis (R:Run G)(d:Fin n→ℕ):Type:=Selection R d univ

abbrev Programme (R:Run G)(d:Fin n→ℕ)(K:ℕ):Type _:=
  ∀(_N per:ℕ),((i:Fin n)→R.family.label (d i)) → (ξ:Fin n→Site (R.family.side K per)) →
  Basis R d → (i:ℕ) → (ik:i<K) → Board G (parent R ik.le per ξ)

variable (table:Programme R d K)(κ:(i:Fin n)→Knob (h i))(pt:Fin n→Chamber)
  (N per:ℕ)(w:(i:Fin n)→R.family.label (d i))(ξ:Fin n→Site (R.family.side K per))

def coefficient (b:Basis R d):ℂ:=weight R d N per K (units R d K w) univ b

def piece (b:Basis R d)(i:ℕ)(U:Config G (R.family.side i per)):ℂ:=
  if ik:i<K then
    let H:=table N per w ξ b i ik
    (WilsonOriginalTwoFlatIRMounted.value H.binder H.load H.copies (regulatorRun R.family N per i) H.wallet U).part (allSlots n)
  else if same:i=K then word R d κ pt (regulatorRun R.family N per K) ξ univ b (same ▸ U) else 0

def row (i:ℕ)(U:Config G (R.family.side i per)):ℂ:=
  ∑b:Basis R d,coefficient (R:=R) (d:=d) (K:=K) N per w b*piece table κ pt N per w ξ b i U

theorem cutoff (live:K≤N):
    row table κ pt N per w ξ K=product R d (N:=N) ξ w:=by
  funext U
  rw [WilsonMovingForkMixedSeed.product,← Finset.prod_coe_sort (univ:Finset (Fin n))]
  simp only [row,piece,lt_irrefl,↓reduceDIte]
  exact (WilsonReceivedCanonicalVerseBasis.faces R d κ pt N per K live (units R d K w) ξ univ U).symm

def issued (old:Filed R d K):Filed R d K:=
  {old with
    row:=row table κ pt
    seed:=fun N per live w ξ=>cutoff table κ pt N per w ξ live.le}

theorem original (old:Filed R d K):
    (issued table κ pt old).A=old.A ∧
    (∀N per (_live:K<N) w ξ,(issued table κ pt old).row N per w ξ K=product R d (N:=N) ξ w) ∧
    ∀b:Basis R d,∀i:ℕ,∀ik:i<K,∀U,
      piece table κ pt N per w ξ b i U=
        let H:=table N per w ξ b i ik
        (WilsonOriginalTwoFlatIRMounted.value H.binder H.load H.copies (regulatorRun R.family N per i) H.wallet U).part (allSlots n):=by
  refine ⟨rfl,fun N per (live:K<N) w ξ=>cutoff table κ pt N per w ξ live.le,?_⟩
  intro b i ik U
  simp [piece,ik]

end YM.Integration.WilsonMovingForkStencilProgramme
end
