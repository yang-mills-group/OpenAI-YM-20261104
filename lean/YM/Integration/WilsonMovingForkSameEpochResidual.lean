import YM.Integration.WilsonMovingForkPointRows
import YM.Integration.WilsonMovingForkSameEpochIntegrals
import YM.Integration.WilsonMovingForkConvolvedResidual

/-! Convolve the positioned full row and every genuine reflected pair at a
single aperture before estimating the independently fitted exterior. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkSameEpochResidual
open Filter Function Set Finset MeasureTheory Lattice Wilson RG Source Extraction Table Spec RG17 Climb
open Trace.Pilot PhysMS PhysicalNext.Repeat.Legato Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register
open FVA2.O FVA2.O.Project FVA2.Scale FVA2.O.Score FVA2.O.Enh MS MS.Land MS.Fleet MS.Theater MS.Rake
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot WilsonMacroscopicRichTwoDatePivot
open WilsonMacroscopicRichSignedAmplitude WilsonMacroscopicRichPositionRows WilsonMacroscopicRichMovingPlane
open WilsonMSDictionaryVector WilsonPublicForkIndependentPlacement WilsonPublicForkIndependentFields
open WilsonPublicForkTestProduct WilsonMacroscopicRichTestGeometry WilsonMovingForkKernelIntegrals
open WilsonMovingForkPositionIntegrals
open WilsonPublicOutputSmooth (exterior)
open private probe from YM.Integration.WilsonMovingForkPointRows
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    (J:ℝ→PhysMS.tower S){n:ℕ}(d:Fin n → ℕ){h:ℕ}(Z:WilsonPrescription G)
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))(ν:ℝ)
    {simple:G.Simple}{σ:Prescription (Press.portDeck G)}{branch:Bool}(ms:Main.Match Z simple M σ branch)
local notation "C" => R.family

include ν ms in
theorem original (B:Profiles R h)(w:B.probes.index→Atom (R:=R) h)
    (issued:∀j,B.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell (C).book.grid h (w j))
    (q:ℕ)(g s r t:ℝ)(tp:0<t)(ψ:Test n)(v:∀i,Free (C) (d i))
    {I:Type}[Fintype I](exteriorBasis:I → Free (C) h)(fit:B.probes.index → I → ℂ)
    (c:Dframe.Toon G h → ℂ)(e:ℝ)(fees:Dframe.Toon G h → ℝ)(home tail:ℝ)
    (ep:0≤e)(fp:∀k,0≤fees k)(hp:0≤home)(rp:0≤tail):
    let X:=exterior F J Z B w issued tp
    let φ:=fun j=>profile (B.probes.shell j) (w j) (issued j) (test B j)
    let pub:=homogeneous F J Z r
    let basis:=WilsonMSDictionaryVector.basis (C) h
    let T:=∑j,Read.Value (φ j)
    let Y:=fun j=>appeared F (d:=d) (fun i=>pub (d i) (v i)) (X j) r ψ
    let A:=fun k j=>(X j).charge F h (pub h (basis k))
    (∀j,∀x∈tsupport ψ,∀z∈tsupport (φ j),placed r t x (relative z)∈conf (n+1))→
    (∀j,∀p∈space ψ (φ j),forest p.1 (squeeze (-s) (relative p.2))∈conf (n+1))→
    (∀j,∀p∈space ψ (φ j),‖S.useAt S (placed r t p.1 (relative p.2))
      (nearTags F J d h Z (r:=r) (t:=t) v (probe B w j))-
        ∑i,fit j i*fullAt (C) d h Z q g s v (exteriorBasis i) p‖≤e)→
    (∀k j,∀z∈tsupport (φ j),‖S.useAt S (t • z) (twoTags F J h Z r t (probe B w j) k)-
      ∑i,fit j i*gramAt (C) h Z q g s (exteriorBasis i) k z‖≤fees k)→
    (∀j,∑i,‖fit j i‖≤home)→
    (∀j i,‖full (C) d h Z q g s v (exteriorBasis i) ψ (φ j)-
      ∑k,c k*gram (C) h Z q g s (exteriorBasis i) (φ j) k‖≤tail)→
    ‖Y-∑k,c k • A k‖≤(Read.Value ψ*T*e+∑k,‖c k‖*(T*fees k))+home*tail:=by
  intro X φ pub basis T Y A safe clear whole two fitBudget remainder
  have nonneg(j):0≤Read.Value (φ j):=integral_nonneg fun _=>norm_nonneg _
  have gross:0≤T:=Finset.sum_nonneg fun j _=>nonneg j
  have single(j):Read.Value (φ j)≤T:=Finset.single_le_sum (f:=fun j=>Read.Value (φ j)) (fun i _=>nonneg i) (mem_univ j)
  have pp:0≤Read.Value ψ:=integral_nonneg fun _=>norm_nonneg _
  apply (pi_norm_le_iff_of_nonneg (add_nonneg (add_nonneg (mul_nonneg (mul_nonneg pp gross) ep)
    (Finset.sum_nonneg fun k _=>mul_nonneg (norm_nonneg _) (mul_nonneg gross (fp k)))) (mul_nonneg hp rp))).mpr
  intro j
  let fullJ:=fun i=>full (C) d h Z q g s v (exteriorBasis i) ψ (φ j)
  let headJ:=fun i k=>gram (C) h Z q g s (exteriorBasis i) (φ j) k
  have wholeJ:‖Y j-∑i,fit j i*fullJ i‖≤Read.Value ψ*T*e:=
    (WilsonMovingForkSameEpochIntegrals.whole_row F J d h Z M ν ms q g s r t tp ψ (φ j) (safe j) (clear j)
      v (probe B w j) exteriorBasis (fit j) (whole j)).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (single j) pp) ep)
  have col(k):‖A k j-∑i,fit j i*headJ i k‖≤T*fees k:=by
    have eq:(X j).charge F h (pub h (basis k))=(φ j).applyTo (fun z=>S.useAt S (t • z) (twoTags F J h Z r t (probe B w j) k)):=by
      rw [WilsonPublicOutputSmooth.charge F J Z B w issued tp]
      change WilsonMatrixTicketLanesSmearedRows.observation F J Z _ (test B j) t h (pub h (basis k))=_
      rw [WilsonMacroscopicRichPositionRows.output F J Z _ (w j) (issued j) _ tp]
      apply congrArg (φ j).applyTo;funext z
      let H:=twoTags F J h Z r t (probe B w j) k
      change S.read (t • z) _=S.read (t • z) (fun i:Fin 2=>⟨(H i).1,S.representative _ (H i).2⟩)
      apply congrArg (S.read (t • z));funext i;fin_cases i <;> rfl
    change ‖(X j).charge F h (pub h (basis k))-_‖≤_
    rw [eq]
    exact (WilsonMovingForkSameEpochIntegrals.gram_row F J h Z M ν ms q g s r t tp ψ (φ j) (clear j)
      (probe B w j) exteriorBasis (fit j) k (two k j)).trans (mul_le_mul_of_nonneg_right (single j) (fp k))
  have fee:=WilsonMovingForkConvolvedResidual.finite c (fit j) (Y j) (fun k=>A k j) fullJ headJ
    (Read.Value ψ*T*e) (fun k=>T*fees k) wholeJ col
  have last:(∑i,‖fit j i‖*‖fullJ i-∑k,c k*headJ i k‖)≤home*tail:=calc
    _≤∑i,‖fit j i‖*tail:=sum_le_sum fun i _=>mul_le_mul_of_nonneg_left (remainder j i) (norm_nonneg _)
    _≤home*tail:=by rw [←Finset.sum_mul];exact mul_le_mul_of_nonneg_right (fitBudget j) rp
  simpa only [Pi.sub_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using fee.trans (add_le_add (le_refl _) last)

end YM.Integration.WilsonMovingForkSameEpochResidual
end
