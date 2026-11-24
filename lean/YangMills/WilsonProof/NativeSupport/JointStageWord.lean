import YangMills.WilsonProof.NativeSupport.JointRecordedDate
import YangMills.WilsonProof.NativeSupport.JointMarkedPath

/-! Evaluation on the original product of local transition factors, with
all spectator coordinates free. The ultraviolet factor occurs once. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.Dated
open Function Finset Lattice RG Wilson Marker MeasureTheory RGComparison.Core16 YM.Pressure Push.BetaTransport
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato Packet
open scoped Classical BigOperators
variable {G:Gauge} {R:Run G} {I:Type} [Fintype I] [DecidableEq I] {t N j per:ℕ}
def params {n:Side} (E:Finset I) (z:ℂ):Names I t N n → ℂ:=
  Sum.elim (fun i=>if i∈E then 1 else 0) (fun p=>if p.1.2 then z else 1)
def micro {n:Side} (F:I → Config G n → ℝ) (E:Finset I) (h:ℝ) (X:Config G n):ℝ:=
  ∏ i:I,(1+(if i∈E then 1 else 0)*h*F i X)
def exposed {A:Levels G} {i:ℕ} (F:I → Config G (A.S.side N per) → ℝ) (E:Finset I) (h:ℝ)
    (X:Config G (A.S.side i per)):ℝ:=if eq:i=N then micro F E h (eq ▸ X) else 1

local notation "A₀" => R.alloy.B.a
local notation "s₀" => R.alloy.B.a.S.side j per
local notation "s₁" => R.alloy.B.a.S.side (j+1) per
local notation "sᵁ" => R.alloy.B.a.S.side N per
local notation "S" => R.alloy.B.a.clock.op j per
local notation "V₀" => Names I t N (R.alloy.B.a.S.side N per)
local notation "P₀" => {_i:I // j+1=N}
local notation "J₀" => Sources I j N (R.alloy.B.a.S.side j per)
variable (T:Slices R.alloy.B.a per) (tj:t ≤ j) (jn:j<N)
variable (F:I → Config G (R.alloy.B.a.S.side N per) → ℝ) (E:Finset I)
variable (δ h c z:ℝ) (σ:Bond (R.alloy.B.a.S.side j per) → ℝ)

theorem stage_word (hp:0 < h) (cp:0 < c) (k:(S).Choices) (X:Config G s₁) (Z:Config G s₀):
    stageWeight (R:=R) T tj jn F σ δ c (params E (z:ℂ)) h k X Z =
      ((exposed (A:=A₀) F E h X * JointPhysical.sample S k univ
        (fun b u=>Real.exp (-(δ*u))*(1+z*h*σ b*u)) X Z:ℝ):ℂ) := by
  let w (i:J₀):ℂ:=1+params E (z:ℂ) (address T tj jn i)*(JointPhysical.sample S k (attached T tj jn (address T tj jn i))
    (probe δ h c σ (address T tj jn i)) X Z:ℂ)*value F h c i X
  change (∏ i:J₀,w i)=_
  rw [Fintype.prod_sum_type,Complex.ofReal_mul]
  congr 1
  · by_cases eq:j+1=N
    · subst N
      let e:{_i:I // j+1=j+1} ≃ I:=⟨Subtype.val,fun x=>⟨x,rfl⟩,fun _=>rfl,fun _=>rfl⟩
      rw [exposed,dif_pos rfl,micro,Complex.ofReal_prod]
      apply Fintype.prod_equiv e;intro i
      dsimp only [w]
      rw [physical_blank T tj jn i,JointPhysical.sample,prod_empty,Complex.ofReal_one,mul_one]
      change 1+(if i.val∈E then (1:ℂ) else 0)*(h*F i.val X:ℝ)=_
      by_cases mem:i.val∈E <;> simp [e,mem]
    · letI:IsEmpty P₀:=⟨fun i=>eq i.property⟩
      rw [exposed,dif_neg eq]
      simp only [Finset.univ_eq_empty,prod_empty,Complex.ofReal_one]
  · rw [Fintype.prod_prod_type_right,JointPhysical.sample,Complex.ofReal_prod]
    apply prod_congr rfl;intro b _
    rw [Fintype.prod_bool]
    let e:=linkEnergy S (Z b*((S).prediction X k b)⁻¹)
    have tested:=probe_on_cell (I:=I) T tj jn c h δ σ b k X Z
    dsimp only at tested
    dsimp only [w]
    rw [tested.1,tested.2]
    change (1+(z:ℂ)*(directionTest c (σ b) e:ℝ)*(h*c:ℝ))*
      (1+1*(thermalTest h δ e:ℝ)*(h:ℝ))=_
    push_cast
    norm_cast
    calc
      _ = (1+h*thermalTest h δ e)*(1+z*(h*c)*directionTest c (σ b) e) := by ring
      _ = _ := tested_pair hp cp δ (σ b) e z

end YM.Integration.InletSusceptibility.Dated
namespace YM.Integration.InletSusceptibility.JointMoments
open Function Finset Lattice RG Wilson Tree RGComparison.Core16 Push.BetaTransport YM.Pressure
open WilsonUniformUnmarkedInletEnergySites
open scoped Classical BigOperators
variable {n c f:Side} {S:StepData c f} {T:Forest S.ratio}
theorem inside (d:Descent n c) (q:sites n d):q∈WilsonUniformUnmarkedInletEnergySites.interior d ↔
    0<lag d q ∧ lag d q<d.depth := by
  exact mem_filter.trans (and_iff_right (mem_univ _))

theorem middle_tail (d:Descent n f):(interior (Descent.push S T d)).toRight=interior d := by
  ext q
  have order:(0<lag d q+1 ∧ lag d q+1<d.depth+1) ↔ 0<lag d q ∧ lag d q<d.depth := by
    have h:=dates d q;omega
  exact mem_toRight.trans ((inside (Descent.push S T d) (Sum.inr q)).trans (order.trans (inside d q).symm))

theorem middle_head (d:Descent n f):(interior (Descent.push S T d)).toLeft=if 0<d.depth then univ else ∅ := by
  ext b
  apply mem_toLeft.trans
  apply (inside (Descent.push S T d) (Sum.inl b)).trans
  change (0<1 ∧ 1<d.depth+1) ↔ b∈(if 0<d.depth then (univ:Finset (Bond c)) else ∅)
  split <;> simp only [mem_univ,iff_true,notMem_empty,iff_false] <;> omega

end YM.Integration.InletSusceptibility.JointMoments
