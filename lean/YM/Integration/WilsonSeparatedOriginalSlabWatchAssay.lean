import YM.Integration.WilsonSeparatedOriginalSlabWatchTarget
import YM.Integration.WilsonMacroscopicRichWatchExtract

/-! One earlier coefficient and a common nonempty cutoff population for all true macroscopic detectors of the same signed near field. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabWatchAssay
open Function Set Filter MeasureTheory Analysis Wilson Lattice RG Source Extra.Histories Extraction Spec Cells OPE OPE.Orbits RG17 PhysMS
open Next.UVStress RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Pulse WilsonCloseCaptureCalendar WilsonReportingUnitOrbit WilsonSeparatedOriginalSlabWatchSupport WilsonSeparatedOriginalSlabWatchContrast WilsonSeparatedOriginalSlabWatchMean
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}{F:Final C f S}{I:Type}[Fintype I][DecidableEq I]

def difference (L:Layout F)(W:Watch C)(s:I→ℕ)(r:ℝ)(w:(i:I)→C.label (s i))(Y:(p:ℕ×ℕ)→(i:I)→Emblems C (s i))(k m:ℕ)(Ψ:Wave I)(g:Body)(d:ℕ)(z:ℕ×ℕ→C.label d)(p:ℕ×ℕ):ℂ:=
    moment (C.beta p.1 p.2) (fun U=>(full L s r w Y k m Ψ g p U-C.O p.1 p.2 (z p) 0 U)*W.plot p.1 p.2 U)

theorem original (L:Layout F)(made:C.Makes)(E:Services C f S)(s:I→ℕ){l:Filter (ℕ×ℕ)}[l.NeBot](lens:l≤L.lens)
    (k m:ℕ){r cap:ℝ}(rp:0<r)(w:(i:I)→C.label (s i))(a:(i:I)→S.Field (s i))(sold:∀i,master L (s i) r (w i)=a i)
    (opened:∀i,C.ref (s i)≤L.level r)(Y:(p:ℕ×ℕ)→(i:I)→Emblems C (s i))(Ψ:Wave I)(g:Body)
    (A:Set (Cloud I))(compact:IsCompact A)(enc:tsupport Ψ.val⊆A)(bounded:∀y∈A,∀i,‖y i‖≤cap)
    (d:ℕ)(z:ℕ×ℕ→C.label d)(base:C.label d)(price:ℝ)(cash:∀ᶠp in l,‖z p-base‖≤price):
    ∃l':Filter (ℕ×ℕ),l'≤l ∧ l'.NeBot ∧ ∃raw:C.label d,Tendsto z l' (𝓝 raw) ∧ ‖raw-base‖≤price ∧
    ∀W:Watch C,band W k r A⊆conf _ →
    let expected:=WilsonSeparatedOriginalSlabWatchTarget.reading W s r a m (wave (C.S.a k/r) Ψ g)-W.tester S d (S.project d raw)
    let observed:=difference L W s r w Y k m Ψ g d z
    Tendsto observed l' (𝓝 expected) ∧ ∀(bill:ℕ×ℕ→ℝ)(fee:ℝ),Tendsto bill l' (𝓝 fee)→(∀ᶠp in l',‖observed p‖≤bill p)→‖expected‖≤fee:=by
  obtain ⟨l',narrow,proper,raw,limit,near,_⟩:=WilsonMacroscopicRichWatchExtract.original F d (lens.trans L.certified) z base price cash
  letI:=proper
  have boundedRaw:∀ᶠp in l',‖z p‖≤price+‖base‖:=by
    filter_upwards [cash.filter_mono narrow] with p hp;exact (norm_le_norm_sub_add (z p) base).trans (add_le_add hp le_rfl)
  have projected:=((S.project d).toContinuousLinearMap.continuous.tendsto raw).comp limit
  refine ⟨l',narrow,proper,raw,limit,near,?_⟩;intro W sep
  have obs:=WilsonSeparatedOriginalSlabWatchContrast.tested L made E W s (narrow.trans (lens.trans L.certified)) (narrow.trans lens) k m rp w opened Y Ψ g A compact enc bounded sep d z (price+‖base‖) boundedRaw (S.project d raw) projected
  rw [WilsonSeparatedOriginalSlabWatchTarget.registered L W s rp w a sold k m Ψ g A enc sep] at obs
  refine ⟨obs,?_⟩;intro bill fee market invoice;exact le_of_tendsto_of_tendsto obs.norm market invoice

end YM.Integration.WilsonSeparatedOriginalSlabWatchAssay
