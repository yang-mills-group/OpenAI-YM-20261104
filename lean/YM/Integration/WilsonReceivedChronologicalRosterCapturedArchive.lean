import YM.Integration.WilsonReceivedChronologicalRosterCatalogue

/-! The dated archive on all original positions whose physical parent has reached the purchased site. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalRosterCapturedArchive
open Function Finset Filter Lattice Wilson RG Marker
open PhysicalNext.Repeat.Legato
open WilsonOriginalMixedBlockRows WilsonMovingForkPrintedFile
open WilsonMovingForkStencilProgramme (Basis)
open WilsonMovingForkStencilCatalogue (Catalogue)
open WilsonMovingForkDepositedPrint (Sheet)
open WilsonMovingForkStencilLine (Received)
open WilsonReceivedChronologicalRosterCatalogue (Ages)
open WilsonReceivedChronologicalMaterialCapture (placed)
open WilsonReceivedChronologicalFixedRoseVariation (cells)
open Analysis Table Spec Extraction Next.UVStress StressFlux.Matching Cells WilsonCenteredPhysicalPanel WilsonCenteredCompactBooking
open scoped Classical

variable {G:Gauge}{n K first f:ℕ}(R:Run G)(d:Fin n→ℕ)(fine:f≤K)
  (active:first+1≤K)

abbrev Occupied (per:ℕ) := {z : Sites R (f,per) n //
  ∀i, parent R active per (placed R fine z) i = 0}

abbrev Ledger:=
  ∀(N per:ℕ)(z:Occupied (n:=n) R fine active per)(_q:Basis R d)(i:ℕ)(hi:i<K),
    Option (Sheet R N i (parent R hi.le per (placed R fine z.val)))

private def move {N per i:ℕ}{ξ ψ:Fin n→Site (R.family.side K per)}(ik:i<K)(same:ξ=ψ)
    (record:Option (Sheet R N i (parent R ik.le per ξ))):
    Option (Sheet R N i (parent R ik.le per ψ)):=same ▸ record

def catalogue (ledger:Ledger R d fine active):Catalogue R d K:=fun N per ξ q i ik=>
  if h:∃z:Occupied (n:=n) R fine active per,placed R fine z.val=ξ then
    move R ik h.choose_spec (ledger N per h.choose q i ik)
  else none

private theorem file {N per:ℕ}(ledger:Ledger R d fine active)(y z:Occupied (n:=n) R fine active per)(q:Basis R d)
    (i:ℕ)(ik:i<K)(same:placed R fine y.val=placed R fine z.val):
    move R ik same (ledger N per y q i ik)=ledger N per z q i ik:=by
  have eq:y=z:=by
    apply Subtype.ext
    funext v
    exact (R.family.S.toDepth fine per).embed_injective (congrFun same v)
  subst z
  rfl

theorem seated (ledger:Ledger R d fine active)(N per:ℕ)(z:Occupied (n:=n) R fine active per)(q:Basis R d)
    (i:ℕ)(ik:i<K):
    catalogue R d fine active ledger N per (placed R fine z.val) q i ik=ledger N per z q i ik:=by
  have trueAt:∃y:Occupied (n:=n) R fine active per,placed R fine y.val=placed R fine z.val:=⟨z,rfl⟩
  unfold catalogue
  rw [dif_pos trueAt]
  exact file R d fine active ledger trueAt.choose z q i ik trueAt.choose_spec

private theorem before (a : Ages first K) : a.val + 1 < K := by
  have h := mem_Ico.mp a.property
  omega

variable (room : (N per : ℕ) → K ≤ N → Prop)
  (issued : ∀ {N per : ℕ} {valid : K ≤ N}, room N per valid → (y : Occupied (n:=n) R fine active per) →
    Basis R d → (a : Ages first K) →
    Sheet R N (a.val + 1) (parent R (before a).le per (placed R fine y.val)))

def ledger : Ledger R d fine active := fun N per y q i _ =>
  match i with
  | 0 => none
  | a + 1 =>
    if valid : K ≤ N then
      if openAt : room N per valid then
        if active : a ∈ Ico first (K-1) then some (issued openAt y q ⟨a,active⟩) else none
      else none
    else none

def Posted (book : Catalogue R d K) {N per : ℕ} {valid : K ≤ N} (admit : room N per valid) : Prop :=
  ∀ (y : Occupied (n:=n) R fine active per) (q : Basis R d) (a : Ages first K),
    book N per (placed R fine y.val) q (a.val + 1) (before a) = some (issued admit y q a)

theorem stored :
    ∃ book : Catalogue R d K, ∀ (N per : ℕ) (valid : K ≤ N) (admit : room N per valid),
      Posted R d fine active room issued book admit := by
  refine ⟨catalogue R d fine active (ledger R d fine active room issued), ?_⟩
  intro N per valid admit y q a
  rw [seated]
  simp only [ledger, dif_pos valid, dif_pos admit, dif_pos a.property]


end YM.Integration.WilsonReceivedChronologicalRosterCapturedArchive
end
