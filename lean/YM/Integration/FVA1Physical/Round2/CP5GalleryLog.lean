import YM.QuadraticLocal.Lamps
import YM.Comparison.RG02.Cumulants.Partition

/-! Separate the normalized connected reading on the *same* reclosed
gallery into its regular rows and its exact signed forced-gas ratio.
The latter disappears identically on a globally healthy field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.CP5
open Finset Lattice RG YM.Wilson Marker QuadraticLocal QuadraticLocal.Fusion.Attached
open Extra.Trajectories Comparison.RG02.Cumulants
open scoped Classical BigOperators
variable {I T ι:Type*} [DecidableEq I] [Fintype I] {G:Gauge} {n:Side}
variable {J:Census I} {o:I→Site n} {P:Rep G n} (A:Gallery T ι o P J)

omit [Fintype I] in
theorem gallery_gas_one (t:T) (U:Config G n) (h:flags P.p.threshold U=∅) :
    A.gas t U=1 := by
  unfold Gallery.gas
  rw [tsum_eq_single ∅]
  · have empty:P.activities.admissible P.p U ∅:=by simp [Activities.admissible,h]
    simp [Fusion.Attached.packet,empty]
  intro s hs
  have dead:¬P.activities.admissible P.p U s:=by
    intro ha
    obtain ⟨i,hi⟩:=Finset.nonempty_iff_ne_empty.mpr hs
    obtain ⟨x,hx⟩:=(P.activities.forced i).inventory_ne
    have flagged:x∈flags P.p.threshold U:=by
      rw [←ha.2]
      exact mem_biUnion.mpr ⟨i,hi,hx⟩
    simp only [h,notMem_empty] at flagged
  simp [Fusion.Attached.packet,dead]

theorem gallery_connected_split {w:I→ℝ} {e a b:ℝ} (paid:A.Pays w e a b)
    (he:0≤e) (hw:∀ j,0<w j) (t:T) (U:Config G n) (nz:P.eval U≠0) :
    connected (((P.eval U:ℝ):ℂ)⁻¹ • A.density t U)=
      A.E.log t U+connected (((P.activities.gas P.p U:ℝ):ℂ)⁻¹ • A.gas t U) := by
  let E:ℂ:=(Real.exp (P.exponent U):ℝ)
  let H:ℂ:=(P.activities.gas P.p U:ℝ)
  have ep:E≠0:=Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  have vac:(P.eval U:ℂ)=E*H:=by rw [Rep.eval,Complex.ofReal_mul]
  have live:H≠0:=by
    intro hz
    exact (show (P.eval U:ℂ)≠0 by exact_mod_cast nz) (vac.trans (by rw [hz,mul_zero]))
  have quiet:(A.E.log t U).part J.quiet=0:=Lamps.quiet_of_hasSum t U (paid.budget.sums he hw t U)
  have mass:(A.gas t U).part J.quiet=H:=Hard.packet_of_quiet A.K t U (Hard.packet_summing _ paid.wages he hw t U)
  have solo:(H⁻¹ • A.gas t U).part J.quiet=1:=by rw [Poly.part_smul,mass,inv_mul_cancel₀ live]
  have scalar:(E*H)⁻¹*E=H⁻¹:=by field_simp
  change connected ((P.eval U:ℂ)⁻¹ • (E • (Poly.pass (A.E.log t U)*A.gas t U)))=_
  rw [vac,smul_smul,scalar,←mul_smul_comm,connected_mul (Poly.pass_part _ quiet) solo,connected_pass quiet]

theorem healthy_gallery_read {w:I→ℝ} {e a b:ℝ} (paid:A.Pays w e a b)
    (he:0≤e) (hw:∀ j,0<w j) (t:T) (U:Config G n) (h:flags P.p.threshold U=∅) :
    connected (((P.eval U:ℝ):ℂ)⁻¹ • A.density t U)=A.E.log t U := by
  have gas:=P.activities.gas_one (p:=P.p) h
  have live:P.eval U≠0:=by rw [Rep.eval,gas,mul_one]; exact Real.exp_ne_zero _
  rw [gallery_connected_split A paid he hw t U live,gas,gallery_gas_one A t U h]
  have zero:connected (1:Poly J)=0:=by
    rw [←pass_zero,connected_pass]
    rfl
  simp only [Complex.ofReal_one,inv_one,one_smul,zero,add_zero]
end YM.Integration.FVA1Physical.Round2.CP5
