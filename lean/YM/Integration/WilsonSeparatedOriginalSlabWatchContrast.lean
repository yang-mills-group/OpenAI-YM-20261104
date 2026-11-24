import YM.Integration.WilsonSeparatedOriginalSlabWatchLaw
import YM.Integration.WilsonSeparatedOriginalReplicaRegularity
import YM.Integration.WilsonMacroscopicRichSingleWatch

/-! Direct signed comparison of the filed collective and the assigned counterterm inside the same physical macroscopic detector. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabWatchContrast
open Function Set Filter MeasureTheory Analysis Wilson Lattice RG Source Extra.Histories Extraction Spec Cells OPE OPE.Orbits RG17
open Next.UVStress RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Pulse RG05Readout.Records WilsonReportingUnitOrbit WilsonReportHarvestReadmittedSource WilsonSeparatedOriginalSlabWatchSupport WilsonSeparatedOriginalSlabWatchLaw
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}{F:Final C f S}{I:Type}[Fintype I][DecidableEq I]

def full (L:Layout F)(s:I→ℕ)(r:ℝ)(w:(i:I)→C.label (s i))(Y:(p:ℕ×ℕ)→(i:I)→Emblems C (s i))(k m:ℕ)(Ψ:Wave I)(g:Body)(p:ℕ×ℕ):C(Config G (C.side p.1 p.2),ℂ):=
  if h:k≤p.1 then
    let v:=fun i=>Many.point (Y p i) (filed L (s i) r (w i) (Y p i) m p.1 p.2) m p.1
    ⟨constellation s v r Ψ h m g, WilsonSeparatedOriginalReplicaRegularity.physical s v h Ψ r m g⟩
  else 0

theorem heard (L:Layout F)(W:Watch C)(s:I→ℕ)(r:ℝ)(w:(i:I)→C.label (s i))(Y:(p:ℕ×ℕ)→(i:I)→Emblems C (s i))(k m:ℕ)(Ψ:Wave I)(g:Body)(p:ℕ×ℕ):
    WilsonMacroscopicRichWatchLaw.meter C W (full L s r w Y k m Ψ g p)=actual L W s r w Y k m Ψ g p:=by
  by_cases h:k≤p.1
  · rw [WilsonMacroscopicRichWatchLaw.same,full,dif_pos h,actual,dif_pos h];rfl
  · rw [full,dif_neg h,map_zero,actual,dif_neg h]

theorem tested (L:Layout F)(made:C.Makes)(E:Services C f S)(W:Watch C)(s:I→ℕ){l:Filter (ℕ×ℕ)}[l.NeBot](law:l≤f.fuse)(lens:l≤L.lens)
    (k m:ℕ){r cap:ℝ}(rp:0<r)(w:(i:I)→C.label (s i))(openRef:∀i,C.ref (s i)≤L.level r)(Y:(p:ℕ×ℕ)→(i:I)→Emblems C (s i))(Ψ:Wave I)(g:Body)
    (A:Set (Cloud I))(hA:IsCompact A)(enc:tsupport Ψ.val⊆A)(bounded:∀y∈A,∀i,‖y i‖≤cap)(sep:band W k r A⊆conf _)
    (d:ℕ)(z:ℕ×ℕ→C.label d)(M:ℝ)(raw:∀ᶠ p in l,‖z p‖≤M)(a:S.Field d)(projected:Tendsto (fun p=>S.project d (z p)) l (𝓝 a)):
    Tendsto (fun p:ℕ×ℕ=>moment (C.beta p.1 p.2) (fun U=>(full L s r w Y k m Ψ g p U-C.O p.1 p.2 (z p) 0 U)*W.plot p.1 p.2 U)) l
      (𝓝 (reading L W s r w k m Ψ g-W.tester S d a)):=by
  have hi:=WilsonSeparatedOriginalSlabWatchLaw.tested L made E W s law lens k m rp w openRef Y Ψ g A hA enc bounded sep
  have lo:=WilsonMacroscopicRichSingleWatch.moving F W d law z M raw a projected
  apply (hi.sub lo).congr;intro p
  let X:C(Config G (C.side p.1 p.2),ℂ):=⟨C.O p.1 p.2 (z p) 0,C.continuousO p.1 p.2 d (z p) 0⟩
  let Y₀:=full L s r w Y k m Ψ g p
  change actual L W s r w Y k m Ψ g p-moment (C.beta p.1 p.2) (fun U=>X U*W.plot p.1 p.2 U)=moment (C.beta p.1 p.2) (fun U=>(Y₀-X) U*W.plot p.1 p.2 U)
  rw [←WilsonMacroscopicRichWatchLaw.same,←heard,←WilsonMacroscopicRichWatchLaw.same,←map_sub]

end YM.Integration.WilsonSeparatedOriginalSlabWatchContrast
