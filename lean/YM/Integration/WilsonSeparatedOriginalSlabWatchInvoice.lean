import YM.Integration.WilsonSeparatedOriginalSlabWatchPacketField
import YM.Integration.WilsonSeparatedOriginalSlabWatchBilling

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabWatchInvoice
open Set Function Filter MeasureTheory Spec OPE OPE.Orbits PhysMS Lattice Wilson Next.UVStress RG05Readout.Native RG05Readout.Pulse
open WilsonSeparatedOriginalSlabWatchSupport WilsonSeparatedOriginalSlabWatchDensity WilsonSeparatedOriginalSlabWatchBorn
open WilsonSeparatedOriginalSlabWatchRoom WilsonSeparatedOriginalSlabWatchMean WilsonSeparatedOriginalSlabWatchMass WilsonSeparatedOriginalSlabWatchNormalization
open scoped Topology ContDiff Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}{I:Type}[Fintype I]

def calibrated (F:Final C f S)(R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (s:I→ℕ)(h:ℕ)(r:ℝ)(a:(i:I)→S.Field (s i))(m:ℕ)(Φ:Wave I):S.Field h:=
  factor C s m • ∫y:Points (Fintype.card I),Φ.val (native y) • R.packet h (native (r • y)) a 0

theorem original (F:Final C f S)(R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J:ℝ→tower S)(leading:Leading F J)(foundation:Foundation F R)(W:Watch C)(s:I→ℕ)
    (v:(i:I)→(Climb.Bel C.book).Field (s i))(h:ℕ){M η ε:ℝ}(bound:0≤M)(eta:0<η)(gain:0<ε)
    (A:Set (Cloud I))(compact:IsCompact A)(Ψ:Wave I)(inside:tsupport Ψ.val⊆A)
    (separated:∀y∈A,∀i j:I,i≠j→η≤‖y i-y j‖)(housed:∀y∈A,∀i,‖y i‖≤M):
    ∃X:ℝ,0<X ∧ ∀ᶠ r in Trace.Pilot.trail,∀(k:ℕ),C.S.a k≤r→∀(m:ℕ)(g:Body),
      let Φ:=wave (C.S.a k/r) Ψ g;let a:=Frame.born J r v
      Integrable (fun y:Points (Fintype.card I)=>Φ.val (native y) • R.packet h (native (r • y)) a 0) volume ∧
      ‖WilsonSeparatedOriginalSlabWatchTarget.reading W s r a m Φ-W.tester S h (calibrated F R s h r a m Φ)‖≤
        ‖factor C s m‖ * (volume.real (plot A)*(charge g*X)) *r^((h:ℝ)+1-ε):=by
  obtain ⟨X,Xp,gross⟩:=WilsonSeparatedOriginalSlabWatchMass.charged A compact s Ψ inside
  refine ⟨X,Xp,?_⟩
  have openRoom:=admissible_separated F R (I:=I) (show 0≤M+1 by linarith) eta h
  have price:=WilsonSeparatedOriginalSlabWatchPacket.original F R J leading foundation W s v h bound eta gain
  filter_upwards [openRoom,price,(WilsonSeparatedOriginalSlabWatchSupport.room W (M+1)).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with r safe paid out rp k thin m g
  let Φ:=wave (C.S.a k/r) Ψ g;let a:=Frame.born J r v
  let e:=fun y:Points (Fintype.card I)=>Φ.val (native y)
  let q:=fun y:Points (Fintype.card I)=>R.packet h (native (r • y)) a 0
  let P:=fun y:Points (Fintype.card I)=>watch W s a (r • y)
  have pos:0<r:=rp;have ht:C.S.a k/r∈Icc (0:ℝ) 1:=⟨div_nonneg (C.S.a_pos _).le pos.le,(div_le_one pos).2 thin⟩
  have known(y:Points (Fintype.card I))(hy:y∈plot A):WithinRoom r (M+1) η (native (r • y)) 0 ∧ joined W (native (r • y))∈conf _:=by
    obtain ⟨apart,size⟩:=housing A separated housed (native y) (WilsonSeparatedOriginalSlabWatchMass.inside.mp hy)
    exact WilsonSeparatedOriginalSlabWatchPacket.placed W pos eta y size apart (fun j=>(by linarith [out j]:r*(M+1)<‖fixedSites W j‖))
  have K:=WilsonSeparatedOriginalSlabWatchMass.compact compact
  have ef:Continuous e:=(show ContDiff ℝ ∞ Φ.val from Φ.property).continuous.comp native_continuous
  have off:∀y∉plot A,e y=0:=by
    intro y hy;by_contra live;apply hy;apply WilsonSeparatedOriginalSlabWatchMass.inside.mpr
    exact WilsonSeparatedOriginalSlabWatchRoom.original _ ht Ψ g A compact inside (subset_tsupport _ live)
  have pf:ContinuousOn P (plot A):=WilsonSeparatedOriginalSlabWatchPacketField.physical F W s a r _ (fun y hy=>(known y hy).2)
  have qf:ContinuousOn q (plot A):=WilsonSeparatedOriginalSlabWatchPacketField.calibration F R s a h r _ (fun y hy=>safe _ 0 (known y hy).1)
  refine ⟨WilsonSeparatedOriginalSlabWatchBilling.supported _ K _ (ef.continuousOn.smul qf) (fun y hy=>by change e y • q y=0;rw [off y hy,zero_smul]),?_⟩
  have income:=WilsonSeparatedOriginalSlabWatchBilling.observed W (factor C s m) _ K e ef off P q pf qf _ (paid k thin A Ψ g compact inside separated housed)
  exact income.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (gross _ ht g).2 (norm_nonneg _)) (Real.rpow_nonneg pos.le _))

end YM.Integration.WilsonSeparatedOriginalSlabWatchInvoice
