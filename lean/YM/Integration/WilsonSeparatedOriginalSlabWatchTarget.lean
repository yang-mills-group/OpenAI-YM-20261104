import YM.Integration.WilsonSeparatedOriginalSlabWatchMean

/-! The original measured primary wave as a single smooth near-position profile with the macroscopic Watch fixed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabWatchTarget
open Function Set Filter MeasureTheory Analysis Wilson Lattice RG Source Extra.Histories Extraction Spec Cells OPE OPE.Orbits RG17 PhysMS
open PhysicalNext PhysicalNext.Repeat Legato Trace.Pilot Pier.Lair Next.UVStress RG05Readout RG05Readout.Native RG05Readout.Pulse
open WilsonSeparatedOriginalSlabPhysicalBox WilsonSeparatedOriginalSlabWatchSupport WilsonSeparatedOriginalSlabWatchDensity WilsonSeparatedOriginalSlabWatchFubini WilsonSeparatedOriginalSlabWatchNormalization WilsonSeparatedOriginalSlabWatchBorn WilsonSeparatedOriginalSlabWatchMean
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}{F:Final C f S}{I:Type}[Fintype I]

theorem stamp (k:ℕ){r:ℝ}(rp:0<r)(Ψ:Wave I)(g:Body)(y:Points (Fintype.card I))(z:E4):
    sheet C k r Ψ g (native (r • y)) z=leaf (C.S.a k/r) Ψ g (native y,z):=by
  apply congrArg (g.val z*·);apply congrArg Ψ.val;funext i
  change r⁻¹ • (-(C.S.a k • z))+r⁻¹ • (r • native y i)=native y i+ -((C.S.a k/r) • z)
  rw [smul_neg,smul_smul,smul_smul,inv_mul_cancel₀ rp.ne',one_smul,div_eq_inv_mul,add_comm]

theorem effective (k:ℕ){r:ℝ}(rp:0<r)(Ψ:Wave I)(g:Body)(y:Points (Fintype.card I)):
    WilsonSeparatedOriginalSlabWatchDensity.test C k r Ψ g (r • y)=(wave (C.S.a k/r) Ψ g).val (native y):=by
  change (∫z in Native.box,sheet C k r Ψ g (native (r • y)) z)=∫z in Native.box,leaf (C.S.a k/r) Ψ g (native y,z)
  apply integral_congr_ae;exact Eventually.of_forall (stamp k rp Ψ g y)

def reading (W:Watch C)(s:I→ℕ)(r:ℝ)(a:(i:I)→S.Field (s i))(m:ℕ)(Φ:Wave I):ℂ:=
    factor C s m*∫y:Points (Fintype.card I),Φ.val (native y)*watch W s a (r • y)

theorem registered (L:Layout F)(W:Watch C)(s:I→ℕ){r:ℝ}(rp:0<r)(w:(i:I)→C.label (s i))(a:(i:I)→S.Field (s i))(selected:∀i,master L (s i) r (w i)=a i)(k m:ℕ)(Ψ:Wave I)(g:Body)(A:Set (Cloud I))(enc:tsupport Ψ.val⊆A)(sep:band W k r A⊆conf _):
    WilsonSeparatedOriginalSlabWatchLaw.reading L W s r w k m Ψ g=reading W s r a m (wave (C.S.a k/r) Ψ g):=by
  rw [WilsonSeparatedOriginalSlabWatchLaw.reading,currency,mul_assoc,affine (I:=I) (C:=C) k rp (0:E4) (fun x=>WilsonSeparatedOriginalSlabWatchDensity.test C k r Ψ g x*signal L W s r w x),reading]
  apply congrArg (factor C s m*·);apply integral_congr_ae;apply Eventually.of_forall;intro y;dsimp only
  have zero:WilsonSeparatedOriginalSlabWatchFubini.point (I:=I) C k (0:E4)=0:=by ext i j;change ((C.S.a k • (0:E4)):E4) j=0;simp
  rw [WilsonSeparatedOriginalSlabWatchFubini.positions,zero,add_zero,←effective k rp Ψ g y]
  by_cases live:WilsonSeparatedOriginalSlabWatchDensity.test C k r Ψ g (r • y)=0
  · rw [live,zero_mul,zero_mul]
  · apply congrArg (_*·);apply received L W s r w a selected;apply sep
    obtain ⟨z,hz,q,hq,eq⟩:=wake (C:=C) k rp Ψ g (native (r • y)) live
    exact ⟨(z,q),⟨hz,enc hq⟩,congrArg (joined W) eq.symm⟩

theorem born (R:Run G){T:Table R.family.book}{H:Final R.family f T}(L:Layout H)(W:Watch R.family)(J:ℝ→FamilyBasis (C:=R.family) T)(s:Fin 3→ℕ)(v:(i:Fin 3)→Free R.family (s i))(h:ℕ){r:ℝ}(rp:0<r)(w:(i:Fin 3)→R.family.label (s i))(sel:WilsonReportHarvestReplayPrescribed.Selected R L J s v h r w)(k m:ℕ)(Ψ:Wave (Fin 3))(g:Body)(A:Set (Cloud (Fin 3)))(enc:tsupport Ψ.val⊆A)(sep:band W k r A⊆conf _):
    WilsonSeparatedOriginalSlabWatchLaw.reading L W s r w k m Ψ g=reading W s r (Frame.born J r v) m (wave (R.family.S.a k/r) Ψ g):=
  registered L W s rp w (Frame.born J r v) (fun i=>(sel i).1) k m Ψ g A enc sep

end YM.Integration.WilsonSeparatedOriginalSlabWatchTarget
