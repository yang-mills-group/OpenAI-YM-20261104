import YM.Integration.WilsonOriginalPublicFigureCharges

/-! The full measured and prescribed inputs are compared through the same
public course. All errors are tested after the complete finite sums. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 600000
namespace YM.Integration.WilsonOriginalPublicFigureSettlement
open Finset Lattice Wilson RG XSpace RegulatorIR.FVAAlt2 PertExtension PertExtension.Orb
open PhysicalNext.Repeat.Legato Precision Labels PowerSeries Filter
open WilsonPositionProgramInversionMaterial (Axes axis ceiling)
open WilsonPositionProgramSeriesRead (Terms weight)
open WilsonOriginalPublicFigureCharges (charge)
open WilsonOriginalPublicFigureCatalogue (filed)
open WilsonOriginalPublicFiniteInversion (observed terminal)
open RegulatorIR RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.Calibration
open scoped Classical ENNReal BigOperators PowerSeries Topology
variable {G:Gauge}(C:Run G){I:Type}[Fintype I][LinearOrder I](d:I→ℕ)
def measured (q:ℕ)(P:Period)(z:I → Cover)(T:P.Tree)(v:(i:I) → (C.family.labels.level (d i)).Coeff):ℂ:=
  coeff (q+WilsonOriginalPublicFigurePole.roof C d) (Bare.normalized T G
    (WilsonOriginalPublicFigurePole.material C d v z P T))
def nominal (q:ℕ)(P:Period)(z:I → Cover)(T:P.Tree)(ζ:Axes C d → PowerSeries ℂ):ℂ:=
  coeff (q+ceiling C d) (Bare.normalized T G (WilsonPositionProgramInversionMaterial.finite C P d z T ζ))
def evaluate (q:ℕ)(field:Terms C d q → ℂ)(ζ:Axes C d → PowerSeries ℂ):ℂ:=
  ∑u,weight C d q ζ u*field u

theorem same (q:ℕ)(P:Period)(z:I → Cover)(T:P.Tree)(D:ChartRatio G)(law:LocalRatio D)
    (v:(i:I) → (C.family.labels.level (d i)).Coeff):
    measured C d q P z T v=nominal C d q P z T (filed C d v):=by
  rw [measured,nominal,WilsonOriginalPublicFigurePole.filed,WilsonOriginalPublicFigureCatalogue.read C d v P z T D law]
  simp only [PowerSeries.coeff_X_pow_mul]

theorem entered (q:ℕ)(P:Period)(z:I → Cover)(tree:P.Tree)(field stopped:Terms C d q → ℂ)(δ:ℝ)(positive:0<δ)
    (payout:∀ζ,‖nominal C d q P z tree ζ-evaluate C d q stopped ζ‖ₑ ≤ ENNReal.ofReal δ*charge C d q ζ)
    (ear:∀w:Terms C d q → ℂ,‖(∑u,w u*field u)-∑u,w u*stopped u‖ ≤ δ*∑u,‖w u‖)
    (ζ:Axes C d → PowerSeries ℂ):
    ‖nominal C d q P z tree ζ-evaluate C d q field ζ‖ₑ ≤ 2*ENNReal.ofReal δ*charge C d q ζ:=by
  let A:=nominal C d q P z tree ζ
  let B:=evaluate C d q stopped ζ
  let E:=evaluate C d q field ζ
  have hit:=ear (weight C d q ζ)
  change ‖E-B‖ ≤ _ at hit
  rw [norm_sub_rev] at hit
  have step:‖B-E‖ₑ ≤ ENNReal.ofReal δ*charge C d q ζ:=by
    simpa only [charge,ofReal_norm,ENNReal.ofReal_mul positive.le,ENNReal.ofReal_sum_of_nonneg
      (fun u _=>norm_nonneg (weight C d q ζ u))] using ENNReal.ofReal_le_ofReal hit
  change ‖A-E‖ₑ ≤ _
  rw [show A-E=A-B+(B-E) by ring,two_mul,add_mul]
  exact (enorm_add_le ..).trans (add_le_add (payout ζ) step)

variable {simple:G.Simple}{axis:Axis}{ε:ℝ}
    (first:WilsonPositionProgramArithmetic.course simple axis ε C.kit)
    (income:WilsonPositionProgramStageInvoice.Requested C.kit)(slow:WilsonWindowReportingPace.Slow C.kit)
    (branch:∀P:RG.Patch,P.Branches C.family.path.levels.clock.kernel G)(p:ℕ)(color:G.ColorIndex)
open XSpace.Cirrus FVA2 FVA2.Register MS MS.Land OPE OPE.Owl
open WilsonPositionProgramReporterBand
open WilsonOriginalMicroscopicGuardedPageSchool (Indexed)
open WilsonOriginalPublicTrialInput (vector)
variable (Z:WilsonPrescription G){M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {T:Prescription (Press.portDeck G)}{dial:Bool}(matchMS:Main.Match Z simple M T dial)
variable (grades stations:Fin 3→ℕ)(K target:ℕ)(η:ℝ)(M₀:Fin 3→ℝ)
    (raw:∀a:Fin 3,ℕ×ℕ → C.family.label (grades a))(ahead:∀a,stations a ≤ K)
    (registered:Indexed C grades stations target η M₀ raw)
local notation "Λ" => RG16.Lambda C.family.path.levels
local notation "Y" => Oracle.books C.family.path.levels.clock.kernel
include first income slow matchMS in
theorem original {AUX:Type}(Q:Prescription (Press.portDeck G))
    (calibration:TaylorOKPl M (YM.FVAAlt2.Lobby.Table (Lodge.basisR C) (Press.portDeck G)) Q)
    (floor:ℕ){d₀:ℕ}(hd:0<d₀)(ratio:Z.run.ratio=(3:ℕ)^d₀)
    (pace:∀m,((C.family.S.block m).val:ℝ) ≤ Real.log (Λ m))
    {n:ℕ}(nonempty:0<n)(room:Set (Points n))(compact:IsCompact room)(apart:room⊆conf n):
    ∃ stage, ∃ B:Band C Z.run stage,(∀t,floor ≤ B.index t) ∧
      let m:=fun u:ℕ×AUX=>B.lower u.1
      let j:=fun u:ℕ×AUX=>B.span u.1
      let w:=fun u:ℕ×AUX=>B.powers u.1
      let S:=WilsonPositionProgramInfraredCircuit.circuit C Z.run m j w (fun u=>B.blocks u.1)
      ∀(z:ℕ×AUX → Fin n → Cover)(c:ℕ×AUX → Four ℝ),
        (∀u,c u∈(Z.run.step (B.index u.1)).Box) → (∀u,(Z.run.step (B.index u.1)).rel (z u) (c u)∈room) →
      ∃F:Tent j, Notebook S Y G branch color (Rocket.native j) F p ∧
      (∀ {l : ℕ} (child : Fin l → Fin n), Function.Injective child →
        ∀ (d : ℕ) (v : Fin l→Dframe.Toon G d) (μ : ℝ) (k : ℕ), k≤p →
        ∃ E : ℝ, 0<E ∧ ∀ᶠ t in atTop, ∀ y : AUX, ∀ cap (P : Handoff.Directory Z (B.index t) cap),
          Handoff.Directory.budget G l d + k ≤ cap →
          let e := fun x : ℕ×AUX => (Z.run.step (B.index x.1)).spacing
          let θ := fun x => μ+Real.log (e x)
          ‖PowerSeries.coeff k (Rocket.adjust S Y branch F (Lodge.basisR C)
            (WilsonPositionProgramSubmittedCoefficient.final j) (Dframe.flash ∘ v) (fun x => (z x) ∘ child) Q θ e (t,y)) -
            WilsonPositionProgramPoint.entry Z (T:=T) P d μ ((z (t,y)) ∘ child) (Dframe.fill v) k‖ ≤
            E*(e (t,y))^Tide.mildG) ∧
      ∀(I:Type)[Fintype I][LinearOrder I](names:I → Fin 3)(child:I → Fin n)
        (trees:∀t,(Z.run.step (B.index t)).p.Tree)(q:ℕ), q ≤ p →
      ∀strength:ℕ, ∀ᶠ t in atTop, ∀ menu:Finset AUX, ∀ᶠ inversion in atTop, ∀y∈menu,∀N per:ℕ,K<N →
        let grades₀:=grades ∘ names
        let v:=(fun i:I=>vector C grades stations K target η M₀ raw ahead registered N per (names i))
        let χ:=filed C grades₀ v
        let clock:=ENNReal.ofReal ((Z.run.step (B.index t)).spacing^strength)
        let fare:=WilsonOriginalPublicFigureCharges.bill C grades stations K η M₀ names q
        let field:=observed C Z.run m j w (fun a=>B.blocks a.1) branch F (fun x=>z x ∘ child) grades₀ (t,y) q inversion
        let start:=measured C grades₀ q (Z.run.step (B.index t)).p (z (t,y) ∘ child) (trees t) v
        ‖start-evaluate C grades₀ q field χ‖ₑ ≤ 2*clock*fare ∧
        ∀ζ:Axes C grades₀ → PowerSeries ℂ,
          let known:=nominal C grades₀ q (Z.run.step (B.index t)).p (z (t,y) ∘ child) (trees t) ζ
          ‖start-known-evaluate C grades₀ q field (fun a=>χ a-ζ a)‖ₑ ≤
            2*clock*(fare+charge C grades₀ q ζ):=by
  obtain ⟨stage,B,late,issued⟩:=WilsonOriginalPublicFigureHearing.original (AUX:=AUX) C first income slow branch p color
    Z matchMS grades stations K target η M₀ raw ahead registered Q calibration floor hd ratio pace nonempty room compact apart
  refine ⟨stage,B,late,?_⟩
  intro m j w S z c box support
  obtain ⟨F,file,_,shared,calibrated⟩:=issued z c box support
  refine ⟨F,file,calibrated,?_⟩
  intro I _ _ names child trees q hq strength
  let d:=grades ∘ names
  filter_upwards [shared I child d trees q hq strength] with t incomeAt
  intro menu
  let δ:=(Z.run.step (B.index t)).spacing^strength
  have positive:0<δ:=pow_pos (Z.run.step (B.index t)).positive _
  let heard(y:AUX)(per:ℕ):Terms C d q → ℂ:=observed C Z.run m j w (fun a=>B.blocks a.1) branch F
    (fun a=>z a ∘ child) d (t,y) q per
  let stop(y:AUX):Terms C d q → ℂ:=terminal C Z.run m j w (fun a=>B.blocks a.1) branch F
    (fun a=>z a ∘ child) d (t,y) q
  have menuPrice:∀ᶠ per in atTop,∀y∈menu,∀u:Terms C d q → ℂ,
      ‖(∑a,u a*heard y per a)-∑a,u a*stop y a‖ ≤ δ*∑a,‖u a‖:=
    (eventually_all_finset menu).2 fun y _=>WilsonOriginalPublicFiniteInversion.original C Z.run
      m j w (fun a=>B.blocks a.1) branch F (fun a=>z a ∘ child) d (t,y) q δ positive
  filter_upwards [menuPrice] with inversion returns
  intro y live N per actual grades₀ v χ clock fare field start
  let P:=(Z.run.step (B.index t)).p
  let pos:=z (t,y) ∘ child
  have paidHere (ζ:Axes C d → PowerSeries ℂ):
      ‖nominal C d q P pos (trees t) ζ-evaluate C d q field ζ‖ₑ ≤ 2*clock*charge C d q ζ:=
    entered C d q P pos (trees t) field (stop y) δ positive
      (fun enter=>incomeAt y (Bare.chart G) (Bare.chart_ratio G) enter) (returns y live) ζ
  have native:charge C d q χ ≤ fare:=
    WilsonOriginalPublicFigureCharges.funded C grades stations K target η M₀ raw ahead registered names N per actual q
  constructor
  · change ‖measured C d q P pos (trees t) v-evaluate C d q field χ‖ₑ ≤ _
    rw [same C d q P pos (trees t) (Bare.chart G) (Bare.chart_ratio G)]
    exact (paidHere χ).trans (by gcongr)
  · intro ζ known
    change ‖(measured C d q P pos (trees t) v-nominal C d q P pos (trees t) ζ)-_‖ₑ ≤ _
    rw [measured,nominal,WilsonOriginalPublicFigureCatalogue.original C d v P pos (trees t) (Bare.chart G) (Bare.chart_ratio G)]
    refine (paidHere (fun a=>χ a-ζ a)).trans ?_
    gcongr
    exact (WilsonOriginalPublicFigureCharges.difference C d q χ ζ).trans (add_le_add native le_rfl)

end YM.Integration.WilsonOriginalPublicFigureSettlement
end
