import YM.Integration.WilsonReportingUnitOrbit
import YM.RG05Readout.Petals.Bullet

/-! The original joint harpoon on the literal reporting primary palette.
Every true frame coordinate is summed on the same terminal field. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportingTerminalPrimaryStencil
open Function Finset Lattice Wilson RG Source Labels Extra.Histories RG05Readout
open Address Native Records Flatten Pulse Petals PhysicalNext.Repeat.Legato
open WilsonReportingUnitOrbit
open scoped Classical BigOperators
variable {G:Gauge} {C:Family G} {N per d:ℕ}

def upper (x:C.label d) : Palette C d :=
  chunk (primary d) ((C.factory d N per).terminal.symm x)

private theorem absent (x:C.label d) (z:Site (C.side N per)) (j:Mark C d) (h:j.1≠primary d) :
    Pulse.key C N per d (upper (N:=N) (per:=per) x) j z=0 := by
  unfold Pulse.key
  have zero:val (upper (N:=N) (per:=per) x) j=0:=by
    change (chunk (primary d) ((C.factory d N per).terminal.symm x)) j.1 j.2=0
    rw [chunk_miss _ h];rfl
  rw [zero,zero_smul]

private def observed (C:Family G) (d:ℕ) (o:Site (C.side N per)) :
    C.label d →ₗ[ℂ] Goods G (C.side N per) :=
  (C.linearO N per d o).mk' (fun x=>C.O N per x o)

theorem site (made:C.Makes) (x:C.label d) (z:Site (C.side N per)) :
    ∑j:Mark C d,Pulse.key C N per d (upper (N:=N) (per:=per) x) j z =
      (C.S.a N:ℂ)^d • C.O N per x z := by
  let t:=primary d
  rw [Fintype.sum_sigma,Finset.sum_eq_single t]
  · let T:=(C.factory d N per).terminal
    let M:=observed C d z
    simp_rw [pulses_key _ made]
    change (∑ i:(C.labels.level d).Index,(C.S.a N:ℂ)^d • M (T ((upper (N:=N) (per:=per) x) t i • Size.axis (C.labels.level d) i)))=
      (C.S.a N:ℂ)^d • M x
    rw [← Finset.smul_sum,← map_sum,← map_sum,Size.sum_axes]
    change (C.S.a N:ℂ)^d • M (T ((upper (N:=N) (per:=per) x) t))=_
    rw [upper,chunk_self,LinearEquiv.apply_symm_apply]
  · intro j _ miss
    exact Finset.sum_eq_zero fun i _=>absent x z ⟨j,i⟩ miss
  · simp

variable {I:Type} [Fintype I] [DecidableEq I] (s:I→ℕ) (x:(i:I)→C.label (s i))

theorem joint (made:C.Makes) (o:I→Site (C.side N per)) (Φ:Wave I) (U:Config G (C.side N per)) :
    harpoon (C:=C) (N:=N) (p:=per) s (fun i=>upper (N:=N) (per:=per) (x i)) o Φ U =
      (perform s (fun i=>primary (s i)) Φ).val 0 *
        ∏i,((C.S.a N:ℂ)^(s i)*C.O N per (x i) (o i) U) := by
  let H (i:I) (j:Mark C (s i)):=Pulse.key C N per (s i) (upper (N:=N) (per:=per) (x i)) j (o i) U
  let P:ℂ:=(perform s (fun i=>primary (s i)) Φ).val 0
  change (∑a:(i:I)→Mark C (s i),(perform s (fun i=>(a i).1) Φ).val 0 * ∏i,H i (a i))=_
  calc
    _ = ∑a:(i:I)→Mark C (s i),P * ∏i,H i (a i):=by
      apply Finset.sum_congr rfl
      intro a _
      by_cases live:∀i,(a i).1=primary (s i)
      · rw [show (fun i=>(a i).1)=(fun i=>primary (s i)) from funext live]
      · obtain ⟨i,miss⟩:=not_forall.mp live
        have z:H i (a i)=0:=congrFun (absent (x i) (o i) (a i) miss) U
        rw [Finset.prod_eq_zero (Finset.mem_univ i) z,mul_zero,mul_zero]
    _ = P * ∏i,(∑j:Mark C (s i),H i j):=by rw [Fintype.prod_sum,Finset.mul_sum]
    _ = _:=by
      apply congrArg (P*·)
      apply Finset.prod_congr rfl
      intro i _
      have hit:=congrFun (site made (x i) (o i)) U
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at hit
      exact hit

end YM.Integration.WilsonReportingTerminalPrimaryStencil
