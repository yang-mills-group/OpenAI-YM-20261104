import YM.SchemeConversionRG11.Coupling.Meter

/-! Center *variation* from zero-order subtraction in moving diagnostic arrays; no
   interchange of power-series order and sequence. -/

set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.Coupling

open Function Filter Maxwell Issue Series Tape Pert.Position
open scoped Topology ContDiff BigOperators

variable {G : Gauge} {F : Labels.Frames G} {n : ℕ} {I : Type*} {l : Filter I}

private theorem metering (A : Issue F 6) : meter A = liftJet (fun p : ℂ × ℂ ↦ readout G (p.1-p.2))
    (both (connected A) (record (fun _ ↦ connected A 0))) := by
  funext i
  let h := trunc_represents (connected A) i
  have hc := record_represents (n:=i) (contDiffAt_const (c:=connected A 0) (x:=(0:ℝ)))
  have he : ContDiff ℝ ω (fun p : ℂ × ℂ ↦ readout G (p.1-p.2)) := by
    have hp : ContDiff ℝ ω (readout G) := by simpa only [sub_zero] using reading (G:=G) 0
    exact hp.comp (contDiff_fst.sub contDiff_snd)
  exact (h.lift (reading (G:=G) (connected A 0)).contDiffAt).unique
    ((h.pair hc).lift he.contDiffAt) i le_rfl

theorem powering {M : I → Issue F 6} {A : Issue F 6} (hA : Limits n l M A) :
    Converges n l (fun i ↦ meter (M i)) (meter A) := by
  have hL : Converges n l (fun i ↦ locker (M i)) (locker A) := by
    intro j hj
    apply tendsto_pi_nhds.mpr; intro i
    let a := cabinet F i
    let u := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin a.r ↦ E F 6) ℂ a.p)
    exact u.continuous.continuousAt.tendsto.comp (hA a.r a.f j hj)
  have ht := ContDiff.contDiffAt (x := locker A 0) tree_smooth
  have h : Converges n l (fun i ↦ connected (M i)) (connected A) := hL.lift ht
  have hv : Converges n l (fun i ↦ record (fun _ ↦ connected (M i) 0)) (record (fun _ ↦ connected A 0)) := by
    intro k hk
    let g := (record_cont (p:=k) (v:=connected A 0) (f:=fun u (_:ℝ) ↦ u) contDiffAt_fst)
    exact g.tendsto.comp (h _ (Nat.zero_le _))
  have he : ContDiff ℝ ω (fun p : ℂ × ℂ ↦ readout G (p.1-p.2)) := by
    have hp : ContDiff ℝ ω (readout G) := by simpa only [sub_zero] using reading (G:=G) 0
    exact hp.comp (contDiff_fst.sub contDiff_snd)
  simp_rw [metering]
  exact (h.both hv).lift he.contDiffAt
end YM.SchemeConversionRG11.Coupling
