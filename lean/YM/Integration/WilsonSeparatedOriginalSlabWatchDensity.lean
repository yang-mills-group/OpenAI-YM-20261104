import YM.Integration.WilsonSeparatedOriginalSlabWatchSupport

/-! The original whole centre integral is a compact test on the separated configuration of the fixed physical detector. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabWatchDensity
open Function Set Filter MeasureTheory Analysis Wilson Lattice RG Source Extra.Histories Extraction Spec Cells OPE OPE.Orbits RG17
open Next.UVStress RG05Readout RG05Readout.Native RG05Readout.Pulse WilsonSeparatedOriginalSlabPhysicalBox WilsonSeparatedOriginalSlabWatchCorners WilsonSeparatedOriginalSlabWatchSupport
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}{F:Final C f S}{I:Type}[Fintype I]

def ordered (x:Cloud I):Points (Fintype.card I):=points (x ∘ runNames I)

def native (x:Points (Fintype.card I)):Cloud I:=fun i=>x ((runNames I).symm i)

@[simp] theorem native_ordered (x:Cloud I):native (ordered x)=x:=funext fun i=>congrArg x ((runNames I).apply_symm_apply i)
@[simp] theorem ordered_native (x:Points (Fintype.card I)):ordered (native x)=x:=PiLp.ext fun i=>congrArg (fun j=>x j) ((runNames I).symm_apply_apply i)

theorem seq_continuous:Continuous (ordered (I:=I)):=by apply (PiLp.continuous_toLp 2 _).comp;apply continuous_pi;intro i;exact continuous_apply _

theorem native_continuous:Continuous (native (I:=I)):=by apply continuous_pi;intro i;exact (continuous_apply ((runNames I).symm i)).comp (PiLp.continuous_ofLp 2 _)

def test (C:Family G)(k:ℕ)(r:ℝ)(Ψ:Wave I)(g:Body)(x:Points (Fintype.card I)):ℂ:= row C k r Ψ g (native x)

theorem joint (C:Family G)(k:ℕ)(r:ℝ)(Ψ:Wave I)(g:Body):Continuous (test C k r Ψ g):=by
  apply Continuous.comp _ native_continuous
  apply continuous_parametric_integral_of_continuous (f:=fun x z=>sheet C k r Ψ g x z) (μ:=volume) _ Pert.Cellular.cells_compact
  refine ((body_smooth g 1).continuous.comp continuous_snd).mul ((lit Ψ 1).continuous.comp ?_)
  apply continuous_pi;intro i
  change Continuous (fun p:Cloud I×E4=>r⁻¹ • (-(C.S.a k • p.2)) + r⁻¹ • p.1 i)
  fun_prop

def footprint (C:Family G)(k:ℕ)(r:ℝ)(A:Set (Cloud I)):Set (Points (Fintype.card I)):= (fun p:E4×Cloud I=>ordered (fun i=>C.S.a k • p.1+r • p.2 i)) '' (Native.box ×ˢ A)

theorem bounded (k:ℕ)(r:ℝ)(A:Set (Cloud I))(hA:IsCompact A):IsCompact (footprint C k r A):=by
  apply (Pert.Cellular.cells_compact.prod hA).image;apply seq_continuous.comp;apply continuous_pi;intro i;fun_prop

theorem supported (k:ℕ){r:ℝ}(rp:0<r)(Ψ:Wave I)(g:Body)(A:Set (Cloud I))(hA:IsCompact A)(enc:tsupport Ψ.val⊆A):
    tsupport (test C k r Ψ g)⊆footprint C k r A:=by
  apply closure_minimal _ (bounded k r A hA).isClosed
  intro x live
  obtain ⟨z,hz,y,hy,actual⟩:=wake k rp Ψ g (native x) live
  exact ⟨⟨z,y⟩,⟨hz,enc hy⟩,(congrArg ordered actual).symm.trans (ordered_native x)⟩

theorem finite (k:ℕ){r:ℝ}(rp:0<r)(Ψ:Wave I)(g:Body)(A:Set (Cloud I))(hA:IsCompact A)(enc:tsupport Ψ.val⊆A):
    HasCompactSupport (test C k r Ψ g):=(bounded k r A hA).of_isClosed_subset (isClosed_tsupport _) (supported k rp Ψ g A hA enc)

def signal (L:Layout F)(W:Watch C)(s:I→ℕ)(r:ℝ)(w:(i:I)→C.label (s i))(x:Points (Fintype.card I)):ℂ:=
  S.value (grade W s ∘ runNames _) (joined W (native x)) (fun i=>fixed L W s r w (runNames _ i))

theorem measured (L:Layout F)(W:Watch C)(s:I→ℕ)(k:ℕ){r:ℝ}(rp:0<r)(w:(i:I)→C.label (s i))(Ψ:Wave I)(g:Body)(A:Set (Cloud I))(hA:IsCompact A)(enc:tsupport Ψ.val⊆A)(sep:band W k r A⊆conf _):
    Continuous (fun x=>test C k r Ψ g x * signal L W s r w x):=by
  apply continuous_iff_continuousAt.mpr;intro x
  by_cases hx:x∈tsupport (test C k r Ψ g)
  · obtain ⟨⟨z,y⟩,mem,loc⟩:=supported k rp Ψ g A hA enc hx
    have ok:joined W (native x)∈conf _:=sep ⟨⟨z,y⟩,mem, by rw [←loc,native_ordered]⟩
    let v (i:Fin (Fintype.card (Arms (I:=I) W))):C.book.Token:=⟨grade W s (runNames _ i),fixed L W s r w (runNames _ i)⟩
    have hval:ContinuousAt (fun y=>S.read y v) (joined W (native x)):=(S.smooth_read F.room.kernel.smooth v).continuousOn.continuousAt ((conf_open _).mem_nhds ok)
    have hloc:ContinuousAt (fun y:Points (Fintype.card I)=>joined W (native y)) x:=((joined_continuous W).comp native_continuous).continuousAt
    exact (joint C k r Ψ g).continuousAt.mul (hval.comp (f:=fun y:Points (Fintype.card I)=>joined W (native y)) hloc)
  · apply (continuousAt_const (x:=x) (y:=(0:ℂ))).congr
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y zero
    simp [zero]

end YM.Integration.WilsonSeparatedOriginalSlabWatchDensity
