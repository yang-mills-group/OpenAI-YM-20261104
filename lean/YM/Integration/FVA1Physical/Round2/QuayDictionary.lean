import YM.LocalLTE.Quay.Teller
import YM.Integration.FVA1Physical.Round2.MotionBasis
import YM.Integration.FVA1Physical.Wilson.BatchHistory

/-! The all-history physical Quay purchase uses exactly the native
conditional moments of the centered C18 product batch. This identity holds
on every configuration, including failed masks and nonflat boundaries. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Quay
open Function Lattice RG YM.Wilson Tree Precision Source Labels Extra.Histories Marker
open LocalLTE.Sail PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Org RG.Supply
open MergeProof.Accent Bandage.Harmonics Next.Foundations
open scoped Classical BigOperators
variable {G : Gauge} {X : Metals G} {D : Rolls X.p} {A : Alloy X D} (P : Bolt A)
    {I : Type} (N n : ℕ) (h : I→ℕ) (v : ∀ i, ((frames G).level (h i)).Coeff)
local notation "H" => Issue.trail P
def centeredBatch : Batch H N n I := ⟨h,v,fun _=>Motion.nil,fun _ _=>0⟩

theorem raw_eq_batch (j : I) :
    rawN (P:=P) (N:=N) (n:=n) h v j = (centeredBatch P N n h v).wavelengths j := by
  funext U
  change _=primProbe H N n (v j) Motion.nil (fun _=>0) U
  rw [primProbe_rebase,Motion.patch_id]
  change (localSection G (h j)).places (((frames G).level (h j)).scaled ((H).rep N n N).p.threshold⁻¹ (v j)) 0 U =
    (localSection G (h j)).places (((frames G).level (h j)).scaled ((H).levels.clock.threshold N)⁻¹ (v j)) 0 U
  rw [(P.choice.represents N n N le_rfl).vac]
  rfl

variable [DecidableEq I] [Fintype I] (B : Census I) (i : ℕ) (hi : i≤N)

theorem vista_moments (U : Config G ((H).S.side i n)) :
    ((((H).rep N n i).eval U:ℂ)⁻¹) • Bandage.Harmonics.vista (P:=P) (N:=N) (n:=n) B h v i hi U =
      momentTable B (centeredBatch P N n h v) i hi U := by
  have birth : rawN (P:=P) (N:=N) (n:=n) h v=(centeredBatch P N n h v).wavelengths :=
    funext (raw_eq_batch P N n h v)
  dsimp only [Bandage.Harmonics.vista]
  rw [birth]
  exact physical_moment_table P.choice B (centeredBatch P N n h v) i hi U

end YM.Integration.FVA1Physical.Round2.Quay
