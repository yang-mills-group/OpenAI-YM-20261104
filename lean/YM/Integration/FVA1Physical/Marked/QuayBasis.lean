import YM.Integration.FVA1Physical.Round2.MotionMoments
import YM.Integration.FVA1Physical.Round2.QuayLibrary

/-! Exact physical tensor identity for the centered analytic library at every
inherited level, including all failed masks. In the canonical orientation the
total coefficient mass of each independent unit-l¹ field test is at most one. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Marked.Quay
open Function Finset Lattice RG YM.Wilson Source Labels Extra.Histories Marker
open LocalLTE.Sail PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Org RG.Supply
open MergeProof.Accent Bandage.Harmonics Next.Foundations UVNext.CouplingReset
open Integration.FVA1Physical.Round2 Integration.FVA1Physical.Round2.Quay
open scoped Classical BigOperators
variable {G : Gauge} {D : ℕ} {I : Type} [Fintype I] [DecidableEq I] (B : Census I) (h : I → Fin (D+1)) (s : B.Mode)
abbrev Pure := BasisChoice (G:=G) B h s

def pureVoice (a : Pure (G:=G) B h s) : voiceBall (fun j=>(h j).val) G :=
  ⟨fun j=>Size.axis ((frames G).level (h j).val) (if p:j∈s.val then a ⟨j,p⟩ else 0),
    fun _=>(Size.size_axis _ _).le⟩

def weights (v : voiceBall (fun i=>(h i).val) G) := basisWeight B h s (fun _=>Motion.nil) v.val

omit [Fintype I] in
theorem weight_one (v : voiceBall (fun i=>(h i).val) G) : ∑ a,‖weights B h s v a‖ ≤ 1 := by
  calc
    _ = ∏ j : ↥s.val,((frames G).level (h j).val).coeffSize (v.val j) := by
      simp only [weights,basisWeight,Motion.patch_id,norm_prod,Frame.coeffSize,Fintype.prod_sum]
    _ ≤ ∏ _ : ↥s.val,(1:ℝ) := Finset.prod_le_prod (fun _ _=>Work.G08.size_nonneg ..) fun j _=>v.property j
    _ = 1 := by simp

variable {X : Metals G} {D₀ : Rolls X.p} {A : Alloy X D₀} (P : Bolt A) (ref : ℕ → ℕ)
    (fields : ∀ d N n,TransferData ((frames G).level d) (Issue.trail P) N n)
local notation "H" => Issue.trail P

theorem vista_tensor (ok : YM.Family.Makes (YM.Family.mk H (hol G) (frames G) (localSection G) ref fields))
    (v : voiceBall (fun i=>(h i).val) G) {N n i : ℕ} (hi : i≤N) (U : Config G ((H).S.side i n)) :
    (vista (P:=P) (N:=N) (n:=n) B (fun j=>(h j).val) v.val i hi U).part s =
      ∑ a, weights B h s v a * (vista (P:=P) (N:=N) (n:=n) B (fun j=>(h j).val) (pureVoice B h s a).val i hi U).part s := by
  let E : StencilFamily G := ⟨H,ref,fields,ok⟩
  let β : ℂ := ((H).rep N n i).eval U
  have nz : β ≠ 0 := Complex.ofReal_ne_zero.mpr (SectorNext.Vacuum.strictly H P.choice N n i hi U).ne'
  have align (w : voiceBall (fun i=>(h i).val) G) :
      (vista (P:=P) (N:=N) (n:=n) B (fun j=>(h j).val) w.val i hi U).part s =
        β * (momentTable B (centeredBatch P N n (fun j=>(h j).val) w.val) i hi U).part s := by
    have h0 := congrArg (fun z : Marker.Poly B=>z.part s) (vista_moments P N n (fun j=>(h j).val) w.val B i hi U)
    change β⁻¹ * _ = _ at h0
    rw [←h0,←mul_assoc,mul_inv_cancel₀ nz,one_mul]
    rfl
  rw [align v]
  simp_rw [align]
  have core := mixed_basis_moment B h s (fun _=>Motion.nil) v.val E (fun _ _=>0) hi U
  change (momentTable B (centeredBatch P N n (fun j=>(h j).val) v.val) i hi U).part s =
    ∑ a,weights B h s v a * (momentTable B (centeredBatch P N n (fun j=>(h j).val) (pureVoice B h s a).val) i hi U).part s at core
  rw [core,mul_sum]; apply sum_congr rfl; intro a _; ring

end YM.Integration.FVA1Physical.Marked.Quay
