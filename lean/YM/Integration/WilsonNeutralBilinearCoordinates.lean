import YM.Integration.WilsonNeutralBilinearTransfer
/-! On the actual dimension-four primary, every nonunit has weight four
and exactly two curvature slots. Consequently the source-unit conversions
at both dated endpoints reduce to one exact scalar on the whole quotient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNeutralBilinearCoordinates
open FormalBulk08 Matrix Laurent Precision Exterior PowerSeries Lattice RG Wilson Tree Stationary
open Push.Uniform Bloch Reef Jets Orb Wick Flat Next.Free UVExtension.Free
open Function Filter Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove
open Planned.PrimaryIntegral295 Source Source.Drops Labels PhysicalNext.Repeat.Legato Next.Foundations
open WilsonRunFormalMarkedStep WilsonNeutralNormalizedForestStep
open scoped Topology BigOperators Matrix Classical

variable {G:Gauge}
def undifferentiated {h:ℕ}(F:Frame G h)(i:F.Index):Letter F:=
  ⟨(i,⟨0,(Dawn.paper_is _).mpr (by simp [Chapel.upper])⟩),
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa [Chapel.upper] using F.bound i⟩⟩

private theorem twice (w:Labels.Key G→₀ℕ):
    2*(w.sum fun _ n=>n) ≤ Labels.height w:=by
  simp only [Labels.height,Finsupp.weight_apply,Finsupp.sum,Finset.mul_sum]
  apply Finset.sum_le_sum;intro k _
  change 2*w k ≤ w k * Labels.generation k
  rw [mul_comm 2]; exact Nat.mul_le_mul_left _ (by unfold Labels.generation;omega)

theorem classification (simple:G.Simple)(F:Frame G 4)(i:F.Index)(active:i≠0):
    F.grades i=(4,2):=by
  have nz : (F.basis i).val ≠0:=fun zero=> F.basis.ne_zero i (Subtype.ext zero)
  obtain ⟨v,hv⟩ := MvPolynomial.exists_coeff_ne_zero nz
  have hg:=(Labels.pure_grade _ _).mp (F.pure i) hv
  rw [Labels.weight_slot] at hg
  have size : Labels.height v=(F.grades i).1:=congrArg Prod.fst hg
  have slots : (v.sum fun _ n=>n)=(F.grades i).2:=congrArg Prod.snd hg
  have tariff: 2*(F.grades i).2≤ (F.grades i).1:=by rw [←size,←slots];exact twice v
  have even:(F.grades i).2%2=0:=WilsonNeutralBilinearTransfer.even_slots simple (by decide) F
    (undifferentiated F i)
  have bound:=F.bound i
  have pos:=F.factors_pos i active
  exact Prod.ext (by dsimp;omega) (by dsimp;omega)

theorem coordinates (simple:G.Simple)(F:Frame G 4)(t:ℝ)(x:F.Coeff):
    F.core (F.scaled t x)=((t:ℂ)^2) • F.core x:=by
  funext i
  by_cases zero:i=0
  · subst i;simp [Frame.core]
  · have h:=classification simple F i zero
    simp [Frame.core,Frame.scaled,Function.update,zero,h]

private theorem decompose (F:Frame G 4)(x:F.Coeff):
    x=F.core x+x 0 • F.e0:=by
  funext i;by_cases zero:i=0 <;> simp [Frame.core,Frame.e0,Function.update,zero]

private theorem dropped (F:Frame G 4)(M:F.Coeff→ₗ[ℂ]F.Coeff)(x:F.Coeff)
    (unit:F.core (M F.e0)=0): F.core (M (F.core x))=F.core (M x):=by
  conv_rhs => rw [decompose F x]
  rw [map_add,map_smul,map_add,map_smul,unit,smul_zero,add_zero]

theorem endpoints (simple:G.Simple)(F:Frame G 4)(M:F.Coeff→ₗ[ℂ]F.Coeff)
    (t u:ℝ)(x:F.Coeff)(unit:F.core (M F.e0)=0):
    F.core (F.scaled t (M (F.scaled u x)))=(((t*u:ℝ):ℂ)^2) • F.core (M x):=by
  rw [coordinates simple,← dropped F M (F.scaled u x) unit,coordinates simple,
    map_smul,map_smul,dropped F M x unit,smul_smul,Complex.ofReal_mul,mul_pow]

end YM.Integration.WilsonNeutralBilinearCoordinates
end
