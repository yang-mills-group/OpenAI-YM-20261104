import YM.PertExtension.HueDepth
import YM.PertExtension.BarePrescription

/-! Vertex leading after replacing same-mark Wick covariance by the defining
infinite-volume top-symbol reference. Here engineering compensation is an
exact truncated-jet identity; no on-shell identities applied prematurely.
-/
set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section
namespace YM.PertExtension.LatticePT.Vertex
open Function Set Filter Finset RG Wilson Lattice Labels Source Drops Hue MvPolynomial
open Next.Rank Next.Rank.Beamer Next.Rank.Configuration Heat.Top Heat.HueTag Bid Heat Next.Rank.LiftMark Normal Next.Rank
open scoped Topology ContDiff BigOperators
variable {G : Gauge}{d e:ℕ}{F: Labels.Frame G d}(S:SectionData F)(H : Hol G)(h:S.Sound H)(p:pop S)
local notation "B" => topMatrix S H h p
local notation "R" => (rendered S p)
local notation "Q∞" => (covarianceSymbol G)
abbrev K:=Panel RG.Slot G

lemma basis_fixed (i:F.Index): Hue.Fixed ((B).basis i):=( ((R).fixed i).slice _).relabel ((R).columns _)
lemma basis_real(i:F.Index): Hue.Clear ((B).basis i):=( ((R).real i).slice _).relabel ((R).columns _)
lemma matrix_real(i:F.Index): star ((B).joint (milk Q∞ ((B).basis i))) = (B).joint (milk Q∞ ((B).basis i)):=coordinates_real _ ((basis_fixed S H h p i).heat) ((basis_real S H h p i).heat)
lemma bar_map (x:F.Coeff): (B).matrix Q∞ (star x) = star ((B).matrix Q∞ x):=by
  change _ = star (∑ i:F.Index, x i • (B).joint (milk Q∞ ((B).basis i)))
  classical
  ext1 j -- sum congr
  change _ = star ((B).matrix Q∞ x j)
  change _ = (starRingEnd ℂ) ((∑ i:F.Index,x i • ((B).joint (milk Q∞ ((B).basis i)))) j)
  rw [Finset.sum_apply,map_sum]
  change (∑ i:F.Index, (star x) i • (B).joint (milk Q∞ ((B).basis i))) j= _;rw [Finset.sum_apply]
  apply Finset.sum_congr rfl fun i hi=>?_; change (star (x i))*((B).joint (((milk Q∞)) ((B).basis i)) j)= (starRingEnd ℂ) (_ * _)
  rw [map_mul, show ∀ i:ℂ,(starRingEnd ℂ) i=star i from fun i=>rfl]
  exact congr_arg (fun z=> star (x i) * z) (congr_fun (matrix_real S H h p i) j).symm
lemma starbasis (i:F.Index): star (topBasisComplex S H h p i) = topBasisComplex S H h p i := by
   let T:=(B).conversion Q∞; let v:F.Coeff:=Pi.single i 1
   change star (T.symm v)= T.symm v
   apply T.injective
   have he : T (star (T.symm v)) = star (T (T.symm v)):=bar_map ..
   rw [he,LinearEquiv.apply_symm_apply]
   classical
   ext1 j; change star ((Pi.single i 1:F.Coeff) j)=(Pi.single i 1:F.Coeff) j; by_cases h:j=i <;> simp [h]

lemma true_coefficients (i j:F.Index): (↑(topBasis S H h p i j):ℂ)=(B).inverse Q∞ (Pi.single i 1) j := by
    exact Complex.conj_eq_iff_re.mp (congr_fun (starbasis S H h p i) j)

def combination (i : F.Index): poly (K (G:=G)):= ∑ j:F.Index, (↑(topBasis S H h p i j):ℂ) • (B).basis j
abbrev normalized (i : F.Index): poly (K (G:=G)):= milk Q∞ (combination S H h p i)
theorem restores (i:F.Index): joint F (normalized S H h p i) = Pi.single i 1:=by
  unfold normalized combination
  classical
  simp only [true_coefficients,map_sum,map_smul]
  exact ((B).conversion Q∞).apply_symm_apply ..
theorem priced (i:F.Index){D:ℕ}(hd:d≤D) : let L:=raiseLabel G hd (F.basis i)
     Rise.trim (exchange (features D Heat.Ray.address 1) (normalized S H h p i)) Configuration.bear d = (rename Sum.inl) (thawKey L):= by
    intro L
    have ht: Hue.Fixed (normalized S H h p i):=Hue.Fixed.heat ?hh
    case hh =>
       unfold Hue.Fixed combination
       intro u x; rw [map_sum,map_sum]; exact Finset.sum_congr rfl fun j hj=>by rw [map_smul,map_smul,(basis_fixed S H h p j) u x]
    have he:=Heat.Ray.deep_joint (F:=F) _ hd ht
    convert he using 3 -- restrict equality at label
    unfold L; congr 1
    rw [restores,← F.coords_basis, F.coords.symm_apply_apply]
end YM.PertExtension.LatticePT.Vertex
