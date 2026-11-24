import YM.Integration.WilsonMarkedInheritedGaussianKernel
import YM.Integration.WilsonMovingGaussianCoordinates
import YM.AllOrder.Kinetic.Lily

/-! Restore the actual Gaussian fluctuation to the full fine angular field,
including its independently computed held mean and the zero trunk links. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMarkedInheritedGaussianPlacement
open Function Filter Finset Matrix Lattice Wilson Exterior Precision RG Next.Free UVExtension.Free
open Stationary Tree Work.F08 FormalBulk08 Flat Reef Jets AllOrder.Ker AllOrder.Kinetic.Port
open Primitives.TwoWave Primitives.TwoWave.RealSlice Push.Uniform
open WilsonMarkedInheritedGaussianKernel
open scoped Topology Classical Matrix BigOperators

variable {G:Gauge} {c f:Side} {S:StepData c f}

def restored (F:Forest S.ratio) (a:Rays (Pine G S F)) : rule (Coarse G) f :=
  (exteriorL G f).symm ((Reef.offer G F a) ∘ WilsonMovingGaussianCoordinates.link G f)

theorem restored_continuous (F:Forest S.ratio) : Continuous (restored (G:=G) F) := by
  apply (exteriorL G f).symm.continuous.comp
  exact continuous_pi fun i=>(continuous_apply (WilsonMovingGaussianCoordinates.link G f i)).comp
    (Reef.offer G F).continuous

theorem length (F:Forest S.ratio) (a:Rays (Pine G S F)) : ‖restored F a‖≤‖a‖ := by
  have first:‖Reef.offer G F a‖≤‖a‖:=by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg a)).2 fun i=>?_
    by_cases h:Flat.lives F i
    · exact (congrArg norm (Flat.bring_alive F a ⟨i,h⟩)).le.trans (norm_le_pi_norm a ⟨i,h⟩)
    · rw [Reef.offer_as, Flat.bring_dead F a h,norm_zero]
      exact norm_nonneg _
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg a)).2 fun i=>?_
  exact (norm_le_pi_norm (Reef.offer G F a) (WilsonMovingGaussianCoordinates.link G f (outsider G f i))).trans first

theorem mean {I J:Type} [Fintype I] [Fintype J] (A:Matrix I J ℝ) (b:ℝ) (hb:0≤b)
    (h:∀v w,|A v w|≤b) (y:J→ℝ) : ‖A*ᵥ y‖≤(Fintype.card J:ℝ)*b*‖y‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity : 0≤(Fintype.card J:ℝ)*b*‖y‖)).2 fun v=>?_
  change ‖∑w:J,A v w*y w‖≤_
  calc _ ≤ ∑w:J,‖A v w*y w‖:=norm_sum_le ..
       _ ≤ ∑_:J,b*‖y‖:=sum_le_sum fun w _=>by
         rw [norm_mul];exact mul_le_mul (h v w) (norm_le_pi_norm y w) (norm_nonneg _) hb
       _ = _:=by simp [mul_assoc]

variable {K:KernelChoices} {j t:ℕ} (P:Flight j t) (L:Lodge P.patch)

def field (n:Side) (y:Rays (wire G n))
    (x:Rays (Pine G (Flat.primary P.patch K n) (Reef.floor K P L n))) : rule (Coarse G) (n*P.L) :=
  restored (Reef.floor K P L n) (Reef.pMean G K P n (Reef.floor K P L n)*ᵥ y + x)

theorem continuous (n:Side) (y:Rays (wire G n)) : Continuous (field (K:=K) P L n y) :=
  (restored_continuous _).comp (continuous_const.add continuous_id)

theorem bounded (b:ℝ) (hb:0≤b) (n:Side)
    (bound:∀u v,|Reef.pMean G K P n (Reef.floor K P L n) u v|≤b)
    (y:Rays (wire G n)) (x:Rays (Pine G (Flat.primary P.patch K n) (Reef.floor K P L n))) :
    1+‖field P L n y x‖≤(1+(Fintype.card (wire G n):ℝ)*b*‖y‖)*(1+‖x‖) := by
  have h₁:=mean _ b hb bound y
  have h₂:‖field P L n y x‖≤(Fintype.card (wire G n):ℝ)*b*‖y‖+‖x‖:=
    (length _ _).trans ((norm_add_le ..).trans (add_le_add_left h₁ _))
  nlinarith only [h₂, mul_nonneg
    (show 0≤(Fintype.card (wire G n):ℝ)*b*‖y‖ by positivity) (norm_nonneg x)]

theorem size (G:Gauge) (K:KernelChoices) (n:Side) :
    Fintype.card (Pine G (Flat.primary P.patch K n) (Reef.floor K P L n)) =
      n.val^4*Fintype.card (Lodge.selected G P.patch L) := by
  rw [Fintype.card_congr (L.splitting (G:=G) (S:=Flat.primary P.patch K n))]
  exact (Fintype.card_prod _ _).trans (by rw [site_card])

theorem coarseSize (G:Gauge) (n:Side) :
    Fintype.card (wire G n)=n.val^4*Fintype.card (Loc G 1) := by
  exact (Fintype.card_prod _ _).trans (by rw [site_card])

end YM.Integration.WilsonMarkedInheritedGaussianPlacement
end
