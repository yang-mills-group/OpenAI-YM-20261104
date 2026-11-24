import YM.FormalBulk08.Avenue.Fossa
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Avenue
open Filter Set Metric MeasureTheory Function Lattice Laurent Bloch Exterior Precision RG Next.Free
open Stationary
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix
variable {n:Side}
open MSbar.Tree.Resolvent
variable {j:ℕ}{k:ℝ}
open Flat UVExtension.Free
variable {G:Gauge}
open Reef Mesa Gorge

variable {D l:ℕ}
open Kemp Pose Dawn Spigot Orb Wick Series Jets MeasureTheory Lotus Shore Lava Rift
variable {u:ℕ}
open Tree PowerSeries
section
variable (P:Flight j u)(R:Lodge P.patch){K: KernelChoices}(h:P.patch.Branches K G)(n:Side)(hi:4≤u)
include hi
lemma wink (r:(primary P.patch K n).Choices)(w x:Pap (wire G (n*P.patch.L)))(ρ:ChartRatio G)(H:LocalRatio ρ)(hw:PowerSeries.coeff 0 w=crunch (kernelP G K.penalty P.wing _))(hx: Matters (coeff 0 x)):
    let F:= Reef.floor K P R n; let S:= primary P.patch K n; let Z:=(dropRoot G S F)ᵀ*pMean G K P n F
    hearth (bandR G P.land K.penalty n) (coeff 0 (tossed P ρ h R n r w x))=mixRows Z (hearth (bandR G P.wing K.penalty (n*P.patch.L)) (coeff 0 x)):= by
    intro F S Z; rw [flagPoint P R h n r w x ρ H hi hw]
    let Q:=puppet P h R n; let Y:= pMean G K P n F; let D:=(dropRoot G S F)ᵀ;let C:=D*Q*Dᵀ;let X:= bandR G P.land K.penalty n
    let A:= bandR G P.wing K.penalty (n*P.patch.L); change hearth X (mixRows Z (hearth C _))=mixRows Z _
    have hQ : Q.IsSymm := by ext x i; exact (ferry P h R n).saddle.ok _ _
    have hv: C.IsSymm:= by change _ᵀ= _; simp only [C,Matrix.transpose_mul,Matrix.transpose_transpose, Matrix.mul_assoc,show Qᵀ=Q from hQ]
    have hX : (Z*X*Zᵀ).IsSymm := by change _ᵀ= _; simp only [Matrix.transpose_mul,Matrix.transpose_transpose, show Xᵀ=X from crest_real _ K.penalty_pos,Matrix.mul_assoc]
    rw [hearth_mix X, hearth_fire _ _ _ hX hv]; apply congr_arg (mixRows Z)
    obtain ⟨p,hp⟩:= imprints K.penalty_pos P.wing P.legal hx
    rw [hp,hearth_mix (C+Z*X*Zᵀ),hearth_mix A];
    let E:= Reef.force G (n*P.patch.L)
    have he : E*A*Eᵀ=E*(D*(Q+Y*X*Yᵀ)*Dᵀ)*Eᵀ:= splits P R h n hi
    have ht : E*A*Eᵀ= E*(C+Z*X*Zᵀ)*Eᵀ := by rw [he]; simp only [C,Z,Y,D,Q,X,Matrix.mul_add,Matrix.add_mul,Matrix.transpose_mul,Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [←ht]

end
end YM.FormalBulk08.Avenue
