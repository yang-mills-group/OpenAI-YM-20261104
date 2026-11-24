import YM.Integration.OPETreeRemainder
import YM.Integration.PhysicalMSOPECandidate
import YM.UVNext.FREE_STRESS_CERTIFICATE.Size

/-! At output horizon zero the full physical reader packet has its
independently computed Wick coefficient in the running field norm. The
identification allows arbitrary source fields and compact separated shapes. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.OPEScalarOutput
open Function Filter Set FVA2 Pert.Position Maxwell Maxwell.Free Maxwell.Wick
open MSbar.OPE Next.Rank.Normal OPE OPE.Orbits Spec PhysMS Trace.Pilot
open scoped Topology BigOperators Classical

variable {G : Gauge} {n i : ℕ}

theorem send_vacuum (x : Points n) (m : ℕ) (r : ℂ) (p : poly (Mark G n)) :
    MvPolynomial.constantCoeff (send x m r p) = MvPolynomial.constantCoeff p := by
  have he := congrArg (fun f : poly (Mark G n) →ₐ[ℂ] ℂ => f p)
    (reads_map (delivery (G := G) x r m) (0 : Slot G → ℂ))
  rw [reads_nil] at he
  simpa [send, AlgHom.comp_apply] using he

theorem glued_vacuum (x : conf n) (p : Fin n → WickPol G) :
    MvPolynomial.constantCoeff (glued x.property p 0) = Wick.moment G x.val p := by
  calc
    _ = MvPolynomial.constantCoeff (send x.val 0 1 (tube x.property p)) := by
      change MvPolynomial.coeff 0 (tier scaleW 0 _) = MvPolynomial.coeff 0 _
      simp [tier, MvPolynomial.coeff_weightedHomogeneousComponent]
    _ = MvPolynomial.constantCoeff (tube x.property p) := send_vacuum .. 
    _ = _ := by
      rw [Wick_reads x.property p,blend_components]
      simp [tube,pot,post]

variable (V : Warehouse G) {B : MS.Land.Booked (ColorCode.wings G)}
    (M : MS.Land.MS_Data G B) (μ : ℝ)

theorem output (hG : G.Simple) (x : conf n) (v : Fin n → E V.F i) :
    OPETreeRemainder.output V.F x v 0 =
      Fountain.phys V M μ 0 x.val i v • (Maxwell.freeTable V.F).unit 0 := by
  let z := OPETreeRemainder.output V.F x v 0
  obtain ⟨a,ha⟩ := UVNext.FreeStress.below V.F hG (show 0 < 4 by decide) z
  have hpoly : address V.F 0 z = a • (1 : WickPol G) := by
    rw [ha, ← Fountain.common_L V, map_smul, Extra.FD.writes_unit]
  have hc : MvPolynomial.constantCoeff (address V.F 0 z) = a := by
    rw [hpoly, Algebra.smul_def, mul_one, MvPolynomial.algebraMap_eq,
      MvPolynomial.constantCoeff_C]
  have hz := OPETreeRemainder.output_polynomial (F := V.F) x v 0
  change address V.F 0 z = _ at hz
  rw [hz,glued_vacuum] at hc
  change z = _
  rw [ha, ← hc, Fountain.vintage V M μ x.val x.property, PositionX.visible_eq]
  rfl

variable {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (hJ : Leading F J) (hG : G.Simple) (X : Climb.Scaling S)
    (hR : Foundation F R) (hC : C.Makes) (hV : ∀ d, Bid.pop (C.localSection d))

include hJ hG X in
theorem packet : ∀ᶠ r in trail, ∀ (n i : ℕ) (v : Fin n → E C.labels i) (x : Fin n → E4),
    PhysicalMSOPECandidate.actualOutput (D := 0) F R J v r x =
      Short.scalar F R x (tags (Frame.born J r v)) 0 • (Climb.Bel C.book).unit 0 := by
  filter_upwards [hJ.unit 0] with r hu n i v x
  let u := Frame.born (d := fun _ : Fin n => i) J r v
  have hs : Short.scalar F R x (tags u) 0 • S.unit 0 = R.fresh 0 x 0 u :=
    Short.scalarizes F R X hG x (tags u) 0
  rw [PhysicalMSOPECandidate.actualOutput, Reader.packet, Fin.sum_univ_one]
  change (J r 0).symm (F.sector.derivatives.rise (show 0 ≤ 0 by rfl) (R.fresh 0 x 0 u)) = _
  rw [F.sector.derivatives.arrival F.room.kernel.laws.toSymmetric F.phase.transport.injection,
    ← hs, map_smul, ← hu, LinearEquiv.symm_apply_apply]

include hJ hG X hR in
theorem leading (v : Fin n → E C.labels i) (K : Set (Points n)) (hK : IsCompact K)
    (hsep : K ⊆ conf n) :
    TendstoUniformlyOn (fun r x => PhysicalMSOPECandidate.actualOutput (D := 0)
      F R J v r (r • x).ofLp) (fun x => Fountain.phys (Atoll.share C hC hV) M μ 0 x i v •
        (Climb.Bel C.book).unit 0) trail K := by
  let L := ContinuousLinearMap.toSpanSingleton ℂ ((Climb.Bel C.book).unit 0)
  have hs := OPEMSReport.physical_scalar_leading (M := M) (μ := μ) (F := F) (J := J)
    (H := hJ) (hC := hC) (hV := hV) (R := R) (hR := hR) (hG := hG) (X := X) v K hK hsep
  have ht := L.uniformContinuous.comp_tendstoUniformlyOn hs
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp ht ε hε,packet F R J hJ hG X] with r hr hw x hx
  rw [hw n i v (r • x).ofLp]
  exact hr x hx

end YM.Integration.OPEScalarOutput
end
