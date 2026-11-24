import YM.Integration.WilsonMovingForkPositionIntegrals

/-! The finite physical pivot reads the complete ordinary assembly, together
with its own reflected two-point matrix, on its actually elected probes. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkPointRows
open Filter Function Set Finset MeasureTheory Lattice Wilson RG Source Extraction Table Spec RG17 Climb
open Trace.Pilot PhysMS PhysicalNext.Repeat.Legato Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register
open FVA2.O FVA2.O.Project FVA2.Scale FVA2.O.Score FVA2.O.Enh MS MS.Land MS.Fleet MS.Theater MS.Rake
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot WilsonMacroscopicRichTwoDatePivot
open WilsonMacroscopicRichSignedAmplitude WilsonMacroscopicRichPositionRows WilsonMacroscopicRichMovingPlane
open WilsonMSDictionaryVector WilsonPublicForkIndependentPlacement WilsonPublicForkIndependentFields
open WilsonPublicForkTestProduct WilsonMacroscopicRichTestGeometry WilsonMovingForkKernelIntegrals
open WilsonMovingForkPositionIntegrals
open WilsonPublicOutputSmooth (exterior)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    (J:ℝ→PhysMS.tower S){n:ℕ}(d:Fin n → ℕ){h:ℕ}(Z:WilsonPrescription G)
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))(ν:ℝ)
    {simple:G.Simple}{σ:Prescription (Press.portDeck G)}{branch:Bool}(ms:Main.Match Z simple M σ branch)
local notation "C" => R.family

private def probe (B:Profiles R h)(w:B.probes.index→Atom (R:=R) h)(j:B.probes.index):Free (C) h:=
  (Bel (C).book).project h (w j)

include ν ms in
theorem original (B:Profiles R h)(w:B.probes.index→Atom (R:=R) h)
    (issued:∀j,B.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell (C).book.grid h (w j))
    (q:ℕ)(g s r t:ℝ)(tp:0<t)(ψ:Test n)(v:∀i,Free (C) (d i))
    (e₀ e₁:ℝ)(ep:0≤e₀)(gp:0≤e₁):
    let X:=exterior F J Z B w issued tp
    let φ:=fun j=>profile (B.probes.shell j) (w j) (issued j) (test B j)
    let pub:=homogeneous F J Z r
    let basis:=WilsonMSDictionaryVector.basis (C) h
    let T:=∑j,Read.Value (φ j)
    let U:=fun j=>appeared F (d:=d) (fun i=>pub (d i) (v i)) (X j) r ψ
    let V:=fun j=>full (C) d h Z q g s v (probe B w j) ψ (φ j)
    let A:=fun k j=>(X j).charge F h (pub h (basis k))
    let G₁:=fun k j=>gram (C) h Z q g s (probe B w j) (φ j) k
    (∀j,∀x∈tsupport ψ,∀z∈tsupport (φ j),placed r t x (relative z)∈conf (n+1))→
    (∀j,∀p∈space ψ (φ j),forest p.1 (squeeze (-s) (relative p.2))∈conf (n+1))→
    (∀j,∀p∈space ψ (φ j),‖S.useAt S (placed r t p.1 (relative p.2)) (nearTags F J d h Z (r:=r) (t:=t) v (probe B w j))-
      fullAt (C) d h Z q g s v (probe B w j) p‖≤e₀)→
    (∀k j,∀z∈tsupport (φ j),‖S.useAt S (t • z) (twoTags F J h Z r t (probe B w j) k)-
      gramAt (C) h Z q g s (probe B w j) k z‖≤e₁)→
    ‖U-V‖≤Read.Value ψ*T*e₀ ∧ ∀k,‖A k-G₁ k‖≤T*e₁:=by
  intro X φ pub basis T U V A G₁ safe fit paid got
  have nonneg(j):0≤Read.Value (φ j):=integral_nonneg fun j=>norm_nonneg _
  have total:0≤T:=Finset.sum_nonneg fun j _=>nonneg j
  have single(j):Read.Value (φ j)≤T:=Finset.single_le_sum (fun k _=>nonneg k) (Finset.mem_univ j)
  have pp:0≤Read.Value ψ:=integral_nonneg fun j=>norm_nonneg _
  constructor
  · apply (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg pp total) ep)).mpr
    intro j
    exact (whole_row F J d h Z M ν ms q g s r t tp ψ (φ j) (safe j) (fit j) v (probe B w j) (paid j)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (single j) pp) ep)
  · intro k
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg total gp)).mpr
    intro j
    have eq:(X j).charge F h (pub h (basis k))=(φ j).applyTo (fun z=>S.useAt S (t • z) (twoTags F J h Z r t (probe B w j) k)):=by
      rw [WilsonPublicOutputSmooth.charge F J Z B w issued tp]
      change WilsonMatrixTicketLanesSmearedRows.observation F J Z _ (test B j) t h (pub h (basis k))=_
      rw [WilsonMacroscopicRichPositionRows.output F J Z _ (w j) (issued j) _ tp]
      apply congrArg (φ j).applyTo;funext z
      let H:=twoTags F J h Z r t (probe B w j) k
      change S.read (t • z) _=S.read (t • z) (fun i:Fin 2=>⟨(H i).1,S.representative _ (H i).2⟩)
      apply congrArg (S.read (t • z));funext i;fin_cases i <;> rfl
    change ‖(X j).charge F h (pub h (basis k))-G₁ k j‖≤T*e₁
    rw [eq]
    exact (gram_row F J h Z M ν ms q g s r t tp ψ (φ j) (fit j) (probe B w j) k (got k j)).trans
      (mul_le_mul_of_nonneg_right (single j) gp)

end YM.Integration.WilsonMovingForkPointRows
