import YM.Integration.WilsonSeparatedOriginalSlabWatchNormalization
import YM.Integration.WilsonReportHarvestReplayPrescribed
import YM.PhysMS.Frame.Macroscopic

/-! The measured continuum reading with the physically filed near classes and the original exterior's own classes. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabWatchBorn
open Function Set MeasureTheory Analysis Wilson Lattice RG Source Extra.Histories Extraction Spec Cells OPE OPE.Orbits RG17 PhysMS
open Next.UVStress RG05Readout RG05Readout.Native RG05Readout.Pulse WilsonSeparatedOriginalSlabWatchCorners WilsonSeparatedOriginalSlabWatchDensity WilsonSeparatedOriginalSlabWatchSupport WilsonSeparatedOriginalSlabWatchFubini WilsonSeparatedOriginalSlabWatchNormalization
open PhysicalNext PhysicalNext.Repeat Lotus Legato Trace.Pilot Pier.Lair
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}{F:Final C f S}{I:Type}[Fintype I]

def panel (W:Watch C)(s:I→ℕ)(a:(i:I)→S.Field (s i)):Arms (I:=I) W→S.Tag
  | .inl i=>⟨s i,a i⟩
  | .inr e=>S.classTokens (W.q e)

def watch (W:Watch C)(s:I→ℕ)(a:(i:I)→S.Field (s i))(x:Points (Fintype.card I)):ℂ:=S.useAt S (joined W (native x)) (panel W s a ∘ runNames _)

theorem received (L:Layout F)(W:Watch C)(s:I→ℕ)(r:ℝ)(w:(i:I)→C.label (s i))(a:(i:I)→S.Field (s i))(selected:∀i,master L (s i) r (w i)=a i)(x:Points (Fintype.card I))(room:joined W (native x)∈conf _):
    signal L W s r w x=watch W s a x:=by
  let Q (j:Arms (I:=I) W):C.book.Token:=⟨grade W s j,fixed L W s r w j⟩
  have labels(j:Arms (I:=I) W):S.classTokens (Q j)=panel W s a j:=by
    cases j with
    | inl i=>exact congrArg (Sigma.mk (s i)) ((projected L W s r w i).trans (selected i))
    | inr e=>rfl
  have eval:=S.at_project S F.room.kernel.laws.toSymmetric (fun _=>le_refl _) room (Q ∘ runNames _)
  change S.read _ (Q ∘ runNames _)=S.useAt S _ (panel W s a ∘ runNames _)
  rw [←eval];apply congrArg;funext i;exact labels _

def smeared (W:Watch C)(s:I→ℕ)(r:ℝ)(a:(i:I)→S.Field (s i))(k m:ℕ)(Ψ:Wave I)(g:Body):ℂ:=
  factor C s m*∫z in Native.box,g.val z*(∫y,Ψ.val (native y)*watch W s a (WilsonSeparatedOriginalSlabWatchFubini.positions C k r z y))

theorem registered (L:Layout F)(W:Watch C)(s:I→ℕ){r:ℝ}(rp:0<r)(w:(i:I)→C.label (s i))(a:(i:I)→S.Field (s i))(selected:∀i,master L (s i) r (w i)=a i)(k m:ℕ)(Ψ:Wave I)(g:Body)(A:Set (Cloud I))(hA:IsCompact A)(enc:tsupport Ψ.val⊆A)(sep:band W k r A⊆conf _):
    WilsonSeparatedOriginalSlabWatchLaw.reading L W s r w k m Ψ g=smeared W s r a k m Ψ g:=by
  rw [normalized L W s rp w k m Ψ g A hA enc sep,positionsReading,smeared]
  apply congrArg (factor C s m*·);apply setIntegral_congr_fun Pert.Cellular.cells_compact.measurableSet;intro z hz
  apply congrArg (g.val z*·);apply integral_congr_ae;apply Filter.Eventually.of_forall;intro y
  by_cases hy:native y∈A
  · apply congrArg (Ψ.val (native y)*·);apply received L W s r w a selected;apply sep
    refine ⟨(z,native y),⟨hz,hy⟩,?_⟩;apply congrArg (joined W);funext i
    change C.S.a k • z+r • native y i=r • native y i+C.S.a k • z;apply add_comm
  · dsimp only;rw [image_eq_zero_of_notMem_tsupport (fun h=>hy (enc h)),zero_mul,zero_mul]

theorem born (R:Run G){T:Table R.family.book}{H:Final R.family f T}(L:Layout H)(W:Watch R.family)(J:ℝ→FamilyBasis (C:=R.family) T)(s:Fin 3→ℕ)(v:(i:Fin 3)→Free R.family (s i))(h:ℕ){r:ℝ}(rp:0<r)(w:(i:Fin 3)→R.family.label (s i))(sel:WilsonReportHarvestReplayPrescribed.Selected R L J s v h r w)(k m:ℕ)(Ψ:Wave (Fin 3))(g:Body)(A:Set (Cloud (Fin 3)))(hA:IsCompact A)(enc:tsupport Ψ.val⊆A)(sep:band W k r A⊆conf _):
    WilsonSeparatedOriginalSlabWatchLaw.reading L W s r w k m Ψ g=smeared W s r (Frame.born J r v) k m Ψ g:=
  registered L W s rp w (Frame.born J r v) (fun i=>(sel i).1) k m Ψ g A hA enc sep

end YM.Integration.WilsonSeparatedOriginalSlabWatchBorn
