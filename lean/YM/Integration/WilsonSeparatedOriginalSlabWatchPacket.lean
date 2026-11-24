import YM.Integration.WilsonSeparatedOriginalSlabWatchPhysical
import YM.Integration.WilsonSeparatedOriginalSlabWatchRoom

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabWatchPacket
open Set Function Filter MeasureTheory Spec OPE OPE.Orbits PhysMS Lattice Wilson Next.UVStress RG05Readout.Native RG05Readout.Pulse
open WilsonMacroscopicRichWatchReader WilsonSeparatedOriginalSlabWatchSupport WilsonSeparatedOriginalSlabWatchDensity
open WilsonSeparatedOriginalSlabWatchBorn WilsonSeparatedOriginalSlabWatchRoom WilsonSeparatedOriginalSlabWatchMean
open scoped Topology Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}{I:Type}[Fintype I]

theorem placed (W:Watch C){r M η:ℝ}(rp:0<r)(eta:0<η)(y:Points (Fintype.card I))
    (span:∀i,‖native y i‖≤M)(apart:∀i j:I,i≠j→η≤‖native y i-native y j‖)
    (out:∀j:Fin W.n,r*M<‖fixedSites W j‖):
    WithinRoom r M η (native (r • y)) 0 ∧ joined W (native (r • y))∈conf _:=by
  have room:WithinRoom r M η (native (r • y)) 0:=by
    constructor
    · intro i;change ‖r • native y i-(0:E4)‖≤M*r
      rw [sub_zero,norm_smul,Real.norm_eq_abs,abs_of_pos rp,mul_comm M r]
      exact mul_le_mul_of_nonneg_left (span i) rp.le
    · intro i j h;change η*r≤‖r • native y i-r • native y j‖
      rw [←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos rp,mul_comm η r]
      exact mul_le_mul_of_nonneg_left (apart i j h) rp.le
  refine ⟨room,?_⟩;apply runs_conf.mpr
  have stop(i:I)(j:Fin W.n):native (r • y) i≠fixedSites W j:=by
    intro eq;have cap:=room.span i;rw [eq,sub_zero,mul_comm] at cap;exact (out j).not_ge cap
  rintro (i|i) (j|j) h
  · apply congrArg Sum.inl;by_contra ne;have pos:0<‖native (r • y) i-native (r • y) j‖:=(mul_pos eta rp).trans_le (room.spaced i j ne)
    change native (r • y) i=native (r • y) j at h;simp [h] at pos
  · exact (stop i j h).elim
  · exact (stop j i h.symm).elim
  · exact congrArg Sum.inr ((distinct W).1 h)

theorem original (F:Final C f S)(R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J:ℝ→tower S)(leading:Leading F J)(foundation:Foundation F R)(W:Watch C)(s:I→ℕ)
    (v:(i:I)→(Climb.Bel C.book).Field (s i))(h:ℕ){M η ε:ℝ}(bound:0≤M)(space:0<η)(gain:0<ε):
    ∀ᶠ r in Trace.Pilot.trail,∀(k:ℕ),C.S.a k≤r→∀(A:Set (Cloud I))(Ψ:Wave I)(g:Body),
      IsCompact A→tsupport Ψ.val⊆A→(∀y∈A,∀i j:I,i≠j→η≤‖y i-y j‖)→(∀y∈A,∀i,‖y i‖≤M)→
      ∀y:Points (Fintype.card I),(wave (C.S.a k/r) Ψ g).val (native y)≠0→
      ‖watch W s (Frame.born J r v) (r • y)-W.tester S h (R.packet h (native (r • y)) (Frame.born J r v) 0)‖≤r^((h:ℝ)+1-ε):=by
  let E:=exterior S W;let z:=(OPE.positions S E).ofLp;let w:=fun i=>(OPE.tags S E i).2
  obtain ⟨δ,δp,clear⟩:=detector_exterior_clearance E (admitted S W)
  have sale:=Frame.single_report F R J leading foundation v w h (M+1) η δ ε (by linarith) space δp gain
  filter_upwards [sale,(WilsonSeparatedOriginalSlabWatchSupport.room W (M+1)).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with r paid far rp k thin A Ψ g compact inside separated bounded y active
  have pos:0<r:=rp
  have ht:C.S.a k/r∈Icc (0:ℝ) 1:=⟨div_nonneg (C.S.a_pos _).le pos.le,(div_le_one pos).2 thin⟩
  have home:=WilsonSeparatedOriginalSlabWatchRoom.original (C.S.a k/r) ht Ψ g A compact inside (subset_tsupport _ active)
  obtain ⟨sep,size⟩:=housing A separated bounded _ home
  obtain ⟨ready,live⟩:=placed W pos space y size sep (fun j=>(by linarith [far j]:r*(M+1)<‖fixedSites W j‖))
  rw [WilsonSeparatedOriginalSlabWatchPhysical.current F W s _ _ live,←WilsonMacroscopicRichWatchReader.same (S:=S) W h,detector_packet_residual F R h (native (r • y)) (Frame.born J r v) E (admitted S W)]
  exact (paid (native (r • y)) z 0 ready clear).2 none

end YM.Integration.WilsonSeparatedOriginalSlabWatchPacket
