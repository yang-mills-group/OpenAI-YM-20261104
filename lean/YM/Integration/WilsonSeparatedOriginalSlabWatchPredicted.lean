import YM.Integration.WilsonSeparatedOriginalSlabWatchArchive
import YM.Integration.WilsonSeparatedOriginalSlabWatchAssay

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabWatchPredicted
open Filter Function Set MeasureTheory Analysis Wilson Lattice RG Source Extra.Histories Extraction Spec Cells OPE OPE.Orbits RG17 PhysMS
open Next.UVStress RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Pulse WilsonCloseCaptureCalendar
open WilsonSeparatedOriginalSlabWatchSupport WilsonSeparatedOriginalSlabWatchMean WilsonSeparatedOriginalSlabWatchMass WilsonSeparatedOriginalSlabWatchNormalization
open WilsonSeparatedOriginalSlabWatchInvoice
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}{I:Type}[Fintype I][DecidableEq I]

theorem original (F:Final C f S)(R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J:ℝ→tower S)(leading:Leading F J)(foundation:Foundation F R)(L:Layout F)(made:C.Makes)(E:Services C f S)
    (W:Watch C)(s:I→ℕ)(v:(i:I)→(Climb.Bel C.book).Field (s i))(h:ℕ){M η ε:ℝ}(bound:0≤M)(eta:0<η)(gain:0<ε)
    (A:Set (Cloud I))(closed:IsCompact A)(Ψ:Wave I)(inside:tsupport Ψ.val⊆A)
    (separated:∀y∈A,∀i j:I,i≠j→η≤‖y i-y j‖)(housed:∀y∈A,∀i,‖y i‖≤M):
    ∃X:ℝ,0<X ∧ ∀ᶠ r in Trace.Pilot.trail,∀(k:ℕ),C.S.a k≤r→∀(m:ℕ)(g:Body)
      (w:(i:I)→C.label (s i)),(∀i,master L (s i) r (w i)=Frame.born J r v i)→(∀i,C.ref (s i)≤L.level r)→
      ∀(Y:(p:ℕ×ℕ)→(i:I)→Emblems C (s i)){l:Filter (ℕ×ℕ)},l.NeBot→l≤L.lens→
      let φ:=wave (C.S.a k/r) Ψ g;let a:=Frame.born J r v;let c:=calibrated F R s h r a m φ
      let row:=WilsonSeparatedOriginalSlabWatchAssay.difference L W s r w Y k m Ψ g h (fun _=>S.representative h c)
      Tendsto row l (𝓝 (WilsonSeparatedOriginalSlabWatchTarget.reading W s r a m φ-W.tester S h c)) ∧
      ∀ξ:ℝ,0<ξ→∀ᶠp in l,‖row p‖≤‖factor C s m‖*(volume.real (plot A)*(charge g*X))*r^((h:ℝ)+1-ε)+ξ:=by
  obtain ⟨X,pos,days⟩:=WilsonSeparatedOriginalSlabWatchInvoice.original F R J leading foundation W s v h bound eta gain A closed Ψ inside separated housed
  refine ⟨X,pos,?_⟩
  filter_upwards [days,(room W M).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with r paid outside rp k thin m g w sold opened Y l proper accepts
  have posr:0<r:=rp
  have license:band W k r A⊆conf _:=WilsonSeparatedOriginalSlabWatchSupport.separated W k posr thin A (fun y hy i j same=>by
    by_contra ne;have p:=separated y hy i j ne;rw [same,sub_self,norm_zero] at p;exact (not_le_of_gt eta) p) housed outside
  let φ:=wave (C.S.a k/r) Ψ g;let a:=Frame.born J r v;let c:=calibrated F R s h r a m φ
  have projection:Tendsto (fun _:ℕ×ℕ=>S.project h (S.representative h c)) l (𝓝 c):=by simp only [S.rep];exact tendsto_const_nhds
  have actual:=WilsonSeparatedOriginalSlabWatchContrast.tested L made E W s (accepts.trans L.certified) accepts k m posr w opened Y Ψ g A closed inside housed license h (fun _=>S.representative h c) ‖S.representative h c‖ (Eventually.of_forall (fun _=>le_rfl)) c projection
  rw [WilsonSeparatedOriginalSlabWatchTarget.registered L W s posr w a sold k m Ψ g A inside license] at actual
  refine ⟨actual,?_⟩;intro ξ fp
  exact (tendsto_order.mp actual.norm).2 _ (((paid k thin m g).2).trans_lt (lt_add_of_pos_right _ fp)) |>.mono (fun _ hsmall=>hsmall.le)

end YM.Integration.WilsonSeparatedOriginalSlabWatchPredicted
