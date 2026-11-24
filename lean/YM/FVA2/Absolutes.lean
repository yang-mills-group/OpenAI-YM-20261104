import YM.FVA2.PullGhost
import YM.FVA2.TreeWick

/-!
# Finite-regulator `PhysicalSum` source input (b=true) from the rooted QME

Affirms action and grain match before substitution of coupling.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Inversion
open Function Set Finset Filter Lattice MS MS.Koszul MS.Swirl MS.Native MS.Orbit MS.Orbit.Cog
open MS.Orbit.LogReal MS.Bare MS.Cylinder MS.Cylinder.Taylor MS.Puff MS.Puff.Mom MS.Book
open MS.Book.Convolve MS.Swirl.Near MS.Cylinder.Lab MS.Native.Wilsonian
open PertExtension PertExtension.Orb
open Matrix FVA2.Ends ArrayMap Substitute Lag
open scoped Classical Topology ContDiff
variable {G:Gauge} {n:Side} (h:Even n.val)
local notation "Z!"=> Z G (Vert n)
local notation "W"=> baseProp G n
local notation "Y"=> baseFix G n
local notation "σ"=> Letter.p
local notation "Gx"=> RootX G n
local notation "u"=> DM G n
local notation "A"=> Words G n
local notation "I"=> Choice.allLetters G n
local notation "C"=> enterF G n
local notation "L"=> ( C ∘L transP )
local notation "K"=> ( C ∘L plane )
local notation "D"=> tallyY (G:=G) (n:=n)
local notation "MM"=> χ G n
local notation "E_"=> rootP G n
local notation "J0"=> Jbar G n

def Bplane (G:Gauge)(n:Side): Matrix (Choice.allLetters G n) (Choice.allLetters G n) ℂ:= ghostU transP plane LinearMap.id
def BackRoot : Matrix A I ℂ := ghostU L K D
local notation "X"=> Bplane G n
local notation "S"=> BackRoot (n:=n) (G:=G)
local notation "P"=> moveL E_ E_ J0 0
set_option quotPrecheck false
local notation "H"=> (show Matrix I I ℂ from Letter.grain W Y)

lemma pays_plane : TieField X σ σ := pinnedU _ _ _ -- /
lemma pays_full : TieField S σ σ:= pinnedU _ _ _
include h
lemma grain_plane : X*H*Xᵀ=H:= by
    have hf : (1-u*Y)*W*(1-u*Y)ᵀ=W:= by
       rw [protects h,transpose_sub,transpose_one,warm h];
       apply Matrix.transpose_injective; rw [transpose_mul,transpose_sub,transpose_one,warm h,gauge_sym,protects h]
    unfold Bplane ghostU; simp_rw [alignL, coordinate_id,into_one,into_zero];
    rw [orthoP h, scale_transP h, commute_grain, hf, Matrix.one_mul,warm h,masks h]
omit h in
lemma factorV : S=P * X := by
    unfold BackRoot Bplane ghostU; rw [alignL,alignL,compL,coordinate_id,into_one, into_zero];
    have ht (B:RootX G n→L[ℝ] RootX G n): intoC (coordinate (C∘L B).toLinearMap)= E_ * intoC (coordinate B.toLinearMap):= by change intoC (coordinate ( (incl G n) ∘ₗ B.toLinearMap ))=_; rw [coordinate_mul,into_mul]
    rw [ht,ht]; unfold Jbar; simp
lemma grain_full : S*H*Sᵀ= (show Matrix A A ℂ from Letter.grain (MasterC G n) (MasterL G n)):= by
    rw [factorV,Matrix.transpose_mul,Matrix.mul_assoc P X,
       ← Matrix.mul_assoc (P* _), Matrix.mul_assoc P,grain_plane h,commute_grain,cut_prop h,cut_fix h] -- inspect

lemma Root_pathE (i:Z G (OEdge n))(j:Z G (Vert n)) : ink (tangentVec («P»:=Vert n)) ((2:ℝ)⁻¹ • Align (full n) L K D (priv i) (priv j))=ink (tangentVec («P»:=Vert n)) ((1:ℝ) • Align (root n) transP plane LinearMap.id (priv i) (priv j)):= by
   apply inkit
   filter_upwards [path_plane (priv j) (priv i) h] with a ha
   change (2:ℝ)⁻¹ * chartPair (incl G n (plane (priv i))) ((full n).flow (incl G n (transP a)) (D (priv j))) = 1 * chartPair (plane (priv i)) ((root n).flow (transP a) (priv j)); rw [ha]; ring
lemma Root_prior : ξ[S] (pay true • (full n).actionBody (priorFull G n))= ξ[X] ((root n).actionBody (priorRoot G n)):= by
    have hφ : pay true=(((2:ℝ)⁻¹:ℝ):ℂ) := by unfold pay; simp only; push_cast; rfl
    rw [hφ, BackRoot,pay_action _ _ _ _ _ (prior_full_prop G n).smooth]
    rw [Bplane, show (root n).actionBody (priorRoot G n) = (↑(1:ℝ):ℂ) • (root n).actionBody (priorRoot G n) by simp, pay_action _ _ _ _ _ (prior_root_prop G n).smooth]
    have hv : (1:ℝ) • (priorRoot G n ∘ (transP (G:=G)))=(2:ℝ)⁻¹ • (priorFull G n ∘ L) := by funext k; rw [one_smul]; exact prior_one (transP k)
    rw [hv]; simp_rw [Root_pathE h]
lemma Root_haar : ξ[S] (pay true • ( HaarBody (Site n) G (Edge (Site n))))= ξ[X] (HaarBody (Vert n) G (OEdge n)) := by
    have hφ : pay true=(((2:ℝ)⁻¹:ℝ):ℂ) := by unfold pay; simp only; push_cast; rfl
    unfold BackRoot Bplane HaarBody; rw [map_smul, ghost_ink L K D _ measure_germ, hφ,← ink_smul,
       ghost_ink (transP (G:=G)) plane _ _ measure_germ ];
    · have ht : Tendsto transP (𝓝 0) (𝓝 (0:RootX G n)):= by simpa using (transP (G:=G) (n:=n)).continuous.tendsto (0:RootX G n)
      exact inkit _ (ht.eventually (even_haar h))
    exact (show ContDiffAt ℝ ω _ (L 0) from by rw [map_zero]; exact measure_germ).comp 0 (L).contDiff.contDiffAt
local notation "AX"=> (full n).total (priorFull G n)
lemma Root_energy (i:ℕ) : ξ[S] (pay true • AX i)= ξ[X] (fullRoot G n i) := by
    unfold fullRoot total; rw [Pi.add_apply,Pi.add_apply,smul_add,map_add,map_add]
    simp only [rankLevel,← map_smul (mask _)]
    rw [in_rank,in_rank,in_rank,in_rank,Root_prior h,Root_haar h]

abbrev landL (F : Dot G Cover): Raw (Words G n) ℂ:= ξ[χ G n] (pay true • docket n F)
lemma land_charge (i:ℕ): ξ[S] (landL (core G i))=ξ[X] (fullRoot G n i) := by
    unfold landL; rw [map_smul, ← show AX i=ξ[MM] ( docket n (core G i)) from (congr_fun (read_total (G:=G) (n:=n)) i).symm]; exact Root_energy h i
omit h
-- action and marks typed in `PhysicalSum` in the full torus alphabet. read via QME
local notation "χ!"=> ξ[MMᵀ * Fourier G n]
lemma land_bulk (F: Dot G Cover) : Near.SendB G n true F= χ! (landL F) := by
    unfold landL; rw [comp_change,← Matrix.mul_assoc,leftM,one_mul]; exact volume_F ..
abbrev landV (x:Cover)(F:Dot G Cover): Raw (Words G n) ℂ:= ξ[χ G n] (enters n (Lab.Shift x F))
lemma land_marks (x y:Cover)(F: Dot G Cover) : Near.Mark_T G n x y F= χ! (landV (x+y) F) := by unfold landV; rw [comp_change,← Matrix.mul_assoc,leftM,one_mul,labels_marks]
lemma view_to (F : Raw (Words G n) ℂ) (hf:F∈Mini _): View (Master G n true) (χ! F)= View (Letter.grain (MasterC G n) (MasterL G n)) F := by
  rw [ view_change _ (show Matrix _ _ ℂ from Master G n true) F hf, shape_Θ]
include h
lemma view_root (F: Raw A ℂ) (hf:F∈Mini _) : View (Master G n true) (χ! F)= View H (ξ[S] F):= by rw [view_to _ hf, view_change _ H F hf,grain_full h]
lemma view_down (F:Raw I ℂ) (hf:F∈Mini _): View H F= View H (ξ[X] F):= by rw [view_change _ H F hf,grain_plane h]

end YM.FVA2.Inversion
