import YM.Integration.WilsonOriginalBlissGramSum

/-! All amplitudes on one finite list may be chosen *after* the regulators.
The Gram cost uses the physical self-readings of the filed continuum fields
on one fixed compact half-space test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalBlissSimultaneousGram
open Filter Finset Lattice Wilson RG Source Labels Cells
open PhysicalNext.Repeat.Legato Extraction Extraction.Banks RG17 Spec Table
open WilsonPositionOriginalDiagnosticMeasuredGram WilsonPositionOriginalDiagnosticPastSource
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Spec.Final R.family f S)
  {H:(Climb.Bel R.family.book).Hierarchy}{l:Ultrafilter (ℕ×ℕ)}
  (arch:Trace.Terrace.Arch R.family)(bliss:Trace.Pilot.Bliss F l arch H)
  (J:ℝ→PhysMS.tower S)(level:ℝ→ℕ)
  (shift:∀d,ℝ→R.family.label d ≃ₗ[ℂ] R.family.label d)
local notation "L"=>WilsonOriginalBlissObserved.layout F bliss J level shift
local notation "C"=>R.family

def field (d:ℕ)(r:ℝ)(χ:Test 1)(z:ℕ×ℕ) :
    S.Field d →ₗ[ℂ] (Config G (R.family.side z.1 z.2) → ℂ) :=
  let top:= ((R.family.S.a (level r)^d:ℝ):ℂ) •
    ((RG12.atK C F.room.cutoff d (level r) z).toLinearMap.comp
      ((shift d r).toLinearMap.comp (WilsonOriginalBlissFieldLift.column arch level shift d r)))
  (sample R χ z.1 z.2).comp ((sectionMap R d z.1 z.2).comp top)

theorem literal (a:Axis)(d:ℕ)(r:ℝ)(χ:Test 1)(ok:∀x∈tsupport χ,Points.allAbove a 0 x)
    (z:ℕ×ℕ)(v:S.Field d):
    field R F arch level shift d r χ z v =
      smear R F L d a χ ok r (WilsonOriginalBlissFieldLift.column arch level shift d r v) z.1 z.2:=
  single R d z.1 z.2 a χ ok _

def gram (a:Axis)(d:ℕ)(χ:Test 1)(ok:∀x∈tsupport χ,Points.allAbove a 0 x)(v:S.Field d):ℂ:=
  S.integralOn (fun _:Fin 2=>d) (two R d a (S.representative d v)) (doubled R d a χ ok)

include bliss J in
theorem measured (a:Axis)(d:ℕ)(r:ℝ)(χ:Test 1)(ok:∀x∈tsupport χ,Points.allAbove a 0 x)
    (ref:R.family.ref d≤level r)(v:S.Field d):
    Tendsto (fun z:ℕ×ℕ=>let X:=field R F arch level shift d r χ z v
      Cells.form (R.family.beta z.1 z.2) (plane C z.1 z.2 a) X X)
      (l:Filter (ℕ×ℕ)) (𝓝 (gram R a d χ ok v)):=by
  have paid:=WilsonPositionOriginalDiagnosticMeasuredGram.original R F L d a χ ok r
    (WilsonOriginalBlissFieldLift.column arch level shift d r v) ref (l:Filter (ℕ×ℕ)) le_rfl
  simpa only [literal R F arch bliss J level shift a d r χ ok,
    WilsonOriginalBlissFieldLift.located F arch bliss J level shift d r v,gram] using paid

include bliss J in
theorem original {ι:Type*}[Fintype ι](a:Axis)(d:ℕ)(r:ℝ)(χ:Test 1)(ok:∀x∈tsupport χ,Points.allAbove a 0 x)
    (ref:R.family.ref d≤level r)(v:ι→S.Field d){η:ℝ}(hp:0<η):
    ∀ᶠ z:ℕ×ℕ in (l:Filter (ℕ×ℕ)),∀c:ι→ℂ,
      let X:=field R F arch level shift d r χ z (∑i,c i • v i)
      ‖Cells.form (R.family.beta z.1 z.2) (plane C z.1 z.2 a) X X‖ ≤
        (∑i,‖c i‖*Real.sqrt (‖gram R a d χ ok (v i)‖+η))^2:=by
  classical
  let T (z:ℕ×ℕ):=field R F arch level shift d r χ z
  have all:∀ᶠ z:ℕ×ℕ in (l:Filter (ℕ×ℕ)),∀i:ι,
      ‖Cells.form (R.family.beta z.1 z.2) (plane C z.1 z.2 a) (T z (v i)) (T z (v i))‖ ≤
         ‖gram R a d χ ok (v i)‖+η:=by
    refine eventually_all.mpr fun i=>?_
    exact (measured R F arch bliss J level shift a d r χ ok ref (v i)).norm.eventually
      (eventually_le_nhds (lt_add_of_pos_right _ hp))
  have supports:=(rows R f d a χ ok).filter_mono (show (l:Filter (ℕ×ℕ))≤f.fuse from (L).certified)
  filter_upwards [all,supports] with z limit room
  intro c
  have head (i:ι):Interior (plane C z.1 z.2 a).sector (T z (v i)):=room _
  have glass:0<R.family.beta z.1 z.2:=Overlay.beta_positive R.makes.wilson (m:=z.1) (N:=z.1) (p:=z.2) le_rfl
  have cost:=WilsonOriginalBlissGramSum.priced univ c
    (Slice.reflected_positive (plane C z.1 z.2 a) _ glass.le) (fun i _=>head i)
  have total:T z (∑i,c i • v i)=WilsonOriginalBlissGramSum.combine univ c (fun i=>T z (v i)):=by
    funext U;simp [WilsonOriginalBlissGramSum.combine,Finset.sum_apply]
  dsimp only
  change ‖Cells.form _ _ (T z _) (T z _)‖ ≤ _
  rw [total]
  refine cost.trans ((sq_le_sq₀ (sum_nonneg fun i _=>mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
    (sum_nonneg fun i _=>mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))).mpr ?_)
  exact sum_le_sum fun i _=>mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (limit i)) (norm_nonneg _)

end YM.Integration.WilsonOriginalBlissSimultaneousGram
