import YM.Integration.WilsonSeparatedOriginalSlabWatchLaw

/-! Exchange of the genuine common centre with the complete joint spatial integral using the original separated compact footprint. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabWatchFubini
open Function Set Filter MeasureTheory Analysis Wilson Lattice RG Source Extra.Histories Extraction Spec Cells OPE OPE.Orbits RG17
open Next.UVStress RG05Readout RG05Readout.Native RG05Readout.Pulse WilsonSeparatedOriginalSlabPhysicalBox WilsonSeparatedOriginalSlabWatchSupport WilsonSeparatedOriginalSlabWatchDensity
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}{F:Final C f S}{I:Type}[Fintype I]

def point (C:Family G)(k:ℕ)(z:E4):Points (Fintype.card I):=ordered (fun _:I=>C.S.a k • z)

def positions (C:Family G)(k:ℕ)(r:ℝ)(z:E4)(y:Points (Fintype.card I)):Points (Fintype.card I):=r • y + point C k z

theorem physical {r:ℝ}(rp:0<r)(k:ℕ)(Ψ:Wave I)(g:Body)(z:E4)(y:Points (Fintype.card I)):
    sheet C k r Ψ g (native (positions C k r z y)) z=g.val z*Ψ.val (native y):=by
  apply congrArg (g.val z*·);apply congrArg Ψ.val;funext i
  change r⁻¹ • (-(C.S.a k • z))+r⁻¹ • (r • native y i+C.S.a k • z)=native y i
  rw [smul_add,smul_smul,inv_mul_cancel₀ rp.ne',one_smul,smul_neg];abel

theorem admitted (k:ℕ){r:ℝ}(rp:0<r)(Ψ:Wave I)(g:Body)(A:Set (Cloud I))(enc:tsupport Ψ.val⊆A){z:E4}(hz:z∈Native.box){x:Points (Fintype.card I)}(nonzero:sheet C k r Ψ g (native x) z≠0):x∈footprint C k r A:=by
  let y:=fun i=>r⁻¹ • (-(C.S.a k • z))+r⁻¹ • native x i
  have active:Ψ.val y≠0:=(mul_ne_zero_iff.mp nonzero).2
  refine ⟨⟨z,y⟩,⟨hz,enc (subset_tsupport _ active)⟩,?_⟩
  change ordered (fun i=>C.S.a k • z + r • y i)=x
  rw [←ordered_native x];apply congrArg ordered;funext i
  change C.S.a k • z + r • (r⁻¹ • (-(C.S.a k • z)) + r⁻¹ • native x i)=native x i
  rw [smul_add,smul_smul,smul_smul,mul_inv_cancel₀ rp.ne',one_smul,one_smul];abel

theorem spatial (k:ℕ)(r:ℝ)(Ψ:Wave I)(g:Body):Continuous (uncurry (fun x:Points (Fintype.card I)=>sheet C k r Ψ g (native x))):=by
  refine ((body_smooth g 1).continuous.comp continuous_snd).mul ((lit Ψ 1).continuous.comp ?_)
  apply continuous_pi;intro i
  change Continuous (fun p:Points (Fintype.card I)×E4=>r⁻¹ • (-(C.S.a k • p.2))+r⁻¹ • native p.1 i)
  have ev:Continuous (fun p:Points (Fintype.card I)×E4=>native p.1 i):=(continuous_apply i).comp (native_continuous.comp continuous_fst)
  fun_prop

theorem licensed (L:Layout F)(W:Watch C)(s:I→ℕ)(k:ℕ)(r:ℝ)(w:(i:I)→C.label (s i))(A:Set (Cloud I))(sep:band W k r A⊆conf _):
    ContinuousOn (signal L W s r w) (footprint C k r A):=by
  let v (i:Fin (Fintype.card (WilsonSeparatedOriginalSlabWatchCorners.Arms (I:=I) W))):C.book.Token:=⟨WilsonSeparatedOriginalSlabWatchCorners.grade W s (runNames _ i),WilsonSeparatedOriginalSlabWatchCorners.fixed L W s r w (runNames _ i)⟩
  apply (S.smooth_read F.room.kernel.smooth v).continuousOn.comp ((joined_continuous W).comp native_continuous).continuousOn
  rintro x ⟨⟨z,y⟩,mem,loc⟩;apply sep;refine ⟨⟨z,y⟩,mem,?_⟩
  rw [←loc];change joined W _=joined W (native (ordered _));rw [native_ordered]

theorem exchanged (k:ℕ){r:ℝ}(rp:0<r)(Ψ:Wave I)(g:Body)(A:Set (Cloud I))(hA:IsCompact A)(enc:tsupport Ψ.val⊆A)(H:Points (Fintype.card I)→ℂ)(hc:ContinuousOn H (footprint C k r A)):
    (∫x,test C k r Ψ g x*H x)=∫z in Native.box,∫x,sheet C k r Ψ g (native x) z*H x:=by
  let K:=footprint C k r A
  have compactK:IsCompact K:=bounded k r A hA
  let P(x:Points (Fintype.card I))(z:E4):=sheet C k r Ψ g (native x) z*H x
  have full:Integrable (uncurry P) ((volume.restrict K).prod (volume.restrict Native.box)):=by
    rw [Measure.prod_restrict]
    exact ((spatial (C:=C) k r Ψ g).continuousOn.mul (hc.comp continuous_fst.continuousOn (fun _ hz=>hz.1))).integrableOn_compact (compactK.prod Pert.Cellular.cells_compact)
  have outer:∀x,x∉K→test C k r Ψ g x*H x=0:=fun x hx=>by rw [image_eq_zero_of_notMem_tsupport (fun live=>hx (supported k rp Ψ g A hA enc live)),zero_mul]
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero outer]
  calc (∫x in K,test C k r Ψ g x*H x)=∫x in K,∫z in Native.box,P x z:=by
          apply setIntegral_congr_fun compactK.measurableSet;intro x _;change (∫z in Native.box,sheet C k r Ψ g (native x) z)*H x=∫z in Native.box,sheet C k r Ψ g (native x) z*H x;rw [integral_mul_const]
    _=∫z in Native.box,∫x in K,P x z:=integral_integral_swap full
    _=∫z in Native.box,∫x,sheet C k r Ψ g (native x) z*H x:=by
          apply setIntegral_congr_fun Pert.Cellular.cells_compact.measurableSet;intro z hz
          apply setIntegral_eq_integral_of_forall_compl_eq_zero;intro x hx;apply mul_eq_zero_of_left
          by_contra live;exact hx (admitted k rp Ψ g A enc hz live)

end YM.Integration.WilsonSeparatedOriginalSlabWatchFubini
