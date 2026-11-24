import YM.Integration.WilsonPhysicalExteriorSolvedGrade

/-! Strictly lower engineering fees vanish for the coherent change of
the original presold Wilson prescription. The same prescription is used
for both scales, and the original MS data buys the two signed receivers. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorCoherentGrades
open Filter Function Finset Matrix PowerSeries Lattice
open MS MS.Dial MS.Land MS.Menus MS.Rake MS.Tide MS.Tone
open FVA2 FVAAlt2 Lobby PhysicalNext.Repeat.Legato Precision RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Lodge
open Pert Pert.Position Pert.Scale Extra.FD OPE.Levy RG11.Fields
open WilsonPhysicalExteriorFieldGram WilsonPhysicalExteriorGradeReadout WilsonPhysicalExteriorPairedLimit
open WilsonPhysicalExteriorRunningRows MSCutoffGerms
open scoped Classical Topology
variable {G:Gauge}{B:MS.Local.Physical.Deck G}{O:Booked B}
variable {R:Run G} {Q:Prescription B} {M:MS_Data G O}

theorem controlled {T:Trial ℕ (Fin 2)} {p q:E4} (V:Warehouse G) (hp:p≠q)
    (reads:Read R M Q T (Fountain.metric (couple p q))) (μ s:ℝ) :
    ∀ h:ℕ,∀ v:Plaid B h,∀ a:Glyph B h,a.size<h→∀ y:ℝ,
      coordinates Q h (y+s) y (y+s) (Land.read v) a=0 := by
  intro h
  induction h using Nat.strong_induction_on with
  | h d ih =>
    cases d with
    | zero => intro v a ha;omega
    | succ n =>
      have prior (b a:Glyph B n) (k:ℕ) : Moderate atTop T.profile.θ
          (fun i=>coeff k (step Q T n μ (μ+s) i b a)) := by
        by_cases le:a.size≤b.size
        · let c:Glyph B b.size:=MSFeeCoordinates.restrict a le
          have eq (i:ℕ):step Q T n μ (μ+s) i b a=
              pay Q (μ-T.profile.θ i) (μ+s-T.profile.θ i) (spacing T i) (owner b) c := by
            change (if h':a.size≤b.size then _ else _)=_
            rw [dif_pos le];rfl
          simp_rw [eq]
          by_cases same:a.size=b.size
          · exact WilsonPhysicalExteriorGradeCoefficient.regular reads.1 Q s μ (owner b) c k same
          have low:=ih b.size (Nat.lt_succ_of_le (MSFeeCoordinates.remaining b)) (owner b).item c
            (show c.size<b.size from lt_of_le_of_ne le same)
          have van (i:ℕ): pay Q (μ-T.profile.θ i) (μ+s-T.profile.θ i) (spacing T i) (owner b) c=0 := by
            rw [WilsonPhysicalExteriorFieldGram.pay,show μ+s-T.profile.θ i=(μ-T.profile.θ i)+s by ring]
            exact mul_eq_zero_of_right _ (low (μ-T.profile.θ i))
          simp_rw [van];exact convergent reads.1 tendsto_const_nhds
        · have van (i:ℕ): step Q T n μ (μ+s) i b a=0 := by
            change (if h':a.size≤b.size then _ else _)=_
            rw [dif_neg le]
          simp_rw [van];exact convergent reads.1 tendsto_const_nhds
      have priced:=WilsonPhysicalExteriorSolvedGrade.measured V hp reads n μ s prior
      intro v a ha y
      let w:Glyph B n:=MSFeeCoordinates.restrict a (Nat.le_of_lt_succ ha)
      have aligned (i:ℕ):lower Q T n μ (μ+s) i v w=
          pay Q (μ-T.profile.θ i) (μ+s-T.profile.θ i) (spacing T i) (owner (Land.read v)) a := by
        change padded Q _ _ _ _ (MSFeeCoordinates.extend _ w)=_
        rw [show MSFeeCoordinates.extend (Nat.le_succ n) w=a from
          MSFeeCoordinates.extend_restrict (Nat.le_succ n) a (Nat.le_of_lt_succ ha)]
        change (if h':a.size≤n+1 then _ else _)=_
        rw [dif_pos (MSFeeCoordinates.remaining a)];rfl
      apply PowerSeries.ext;intro k
      have paid:=priced v w k
      simp_rw [aligned] at paid
      rw [map_zero]
      exact WilsonPhysicalExteriorGradeCoefficient.excluded reads.1 Q s μ (owner (Land.read v)) a k ha paid y

/-- Arbitrary coherent bare clocks on the purchased original prescription.
The two-site detector is selected a single time, before the clock shift. -/
theorem original (R:Run G) (M:MS_Data G O) (Q:Prescription B)
    (hG:G.Simple) (paid:TaylorOKPl M (Lobby.Table (basisR R) B) Q) :
    ∀ h:ℕ,∀ v:Plaid B h,∀ a:Glyph B h,a.size<h→∀ y z:ℝ,
      coordinates Q h z y z (Land.read v) a=0 := by
  obtain ⟨p,hp⟩:=exists_ne (0:E4)
  let V:Warehouse G:=⟨R.family.labels,R.family.params,R.family.localSection,R.makes.sections,
    fun d=>Next.Foundations.valuation G d⟩
  let x:=Fountain.metric (couple p 0)
  have hx:Injective x:=Theater.out.injective.comp (couple_ok hp)
  obtain ⟨T,hr⟩:=WilsonPhysicalExteriorPairedLimit.actual R M Q hG paid x hx
  intro h v a ha y z
  have old:=controlled V hp hr 0 (z-y) h v a ha y
  rwa [show y+(z-y)=z by ring] at old

end YM.Integration.WilsonPhysicalExteriorCoherentGrades
end
