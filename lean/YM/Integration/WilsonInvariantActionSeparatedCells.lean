import YM.Integration.WilsonInvariantActionPromotedPair
import YM.OPE.Samples.Layout
import YM.RG17.Corners

/-! The original signed fine test forces its two actual coarse ancestors to
remain separated. The comparison uses periodic lattice distances at both dates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionSeparatedCells
open Function Filter Set MeasureTheory Lattice Wilson RG Source Marker Extraction Extraction.Order Spec
open Next.Rank PhysicalNext.Repeat.Legato RG17 FullVolume Table Climb Trace.Pilot Next.UVStress
open RGComparison.Core16
open scoped Topology BigOperators Classical

variable {G:Gauge} (C:Family G) {k N per:ℕ}

def gap (h:k≤N) (x:Fin 2→Site (C.side N per)):ℕ:=
  separation ((C.S.toDepth h per).parent (x 0)) ((C.S.toDepth h per).parent (x 1))

private theorem cells (h:k≤N) (x:Fin 2→Site (C.side N per)):
    C.S.a k*(gap C h x:ℝ) ≤ C.S.a N*separation (x 0) (x 1)+C.S.a k ∧
    C.S.a N*separation (x 0) (x 1) ≤ C.S.a k*(gap C h x:ℝ)+C.S.a k:=by
  let E:=C.S.toDepth h per
  let t:=E.count.val
  let D:=gap C h x
  let z:=separation (x 0) (x 1)
  have data:=OPE.Log.Trunk.Canvas.expands (C:=C) (x 0) (x 1) h
  have up:t*D≤z+t:=data.1.le
  have dn:z≤t*D+t:=data.2.le
  have up': (t:ℝ)*D≤(z:ℝ)+t:=by exact_mod_cast up
  have dn': (z:ℝ)≤(t:ℝ)*D+t:=by exact_mod_cast dn
  have mesh:C.S.a N*(t:ℝ)=C.S.a k:=C.S.embeds_scale E
  refine ⟨?_,?_⟩
  · change C.S.a k*(D:ℝ)≤C.S.a N*(z:ℝ)+C.S.a k
    calc _=C.S.a N*((t:ℝ)*D):=by rw [←mesh];ring
         _≤C.S.a N*((z:ℝ)+t):=mul_le_mul_of_nonneg_left up' (C.S.a_pos N).le
         _=_:=by rw [mul_add,mesh]
  · change C.S.a N*(z:ℝ)≤C.S.a k*(D:ℝ)+C.S.a k
    calc _≤C.S.a N*((t:ℝ)*D+t):=mul_le_mul_of_nonneg_left dn' (C.S.a_pos N).le
         _=_:=by rw [mul_add,←mul_assoc,mesh]

/-- One pair of positive constants works for every contributing signed mesh
coefficient, every original period and every earlier retained date. -/
theorem filed (φ:Test 2) {K:Set (Points 2)} (compact:IsCompact K) (separated:K⊆conf 2) (here:tsupport φ⊆K):
    ∃ l u:ℝ,0<l ∧ 0<u ∧ ∀ᶠ r in trail,∀ (hr:0<r) k N per (h:k≤N) (x:Fin 2→Site (C.side N per)),
      WilsonExternalMeshMass.charge C (dilate hr φ) x≠0 →
      l*r/C.S.a k ≤ (gap C h x:ℝ)+1 ∧
        (gap C h x:ℝ)≤u*r/C.S.a k+1:=by
  obtain ⟨T,δ,hT,hδ,window⟩:=roomCosts compact separated
  let u:=2*T+1
  have hu:0<u:=by dsimp only [u];linarith
  refine ⟨δ/2,u,half_pos hδ,hu,?_⟩
  have small:∀ᶠ r in trail,r<(1/2)/u:=nhdsWithin_le_nhds (gt_mem_nhds (by positivity))
  filter_upwards [small] with r thin
  intro hr k N per h x live
  let p:Points 2:=Order.cells C N per x
  let z:=r⁻¹ • p
  have nonzero:φ z≠0:=by
    intro no;apply live
    change (C.S.a N:ℂ)^(4*2)*((↑((r^(4*2))⁻¹):ℂ)*φ z)=0
    rw [no,mul_zero,mul_zero]
  have yz:=window r hr z (here (subset_tsupport _ nonzero))
  have coordinates (i:Fin 2):posed r z i=C.S.place (x i):=by
    change r • (r⁻¹ • p i)=p i
    rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  have span (i:Fin 2):‖C.S.place (x i)‖≤T*r:=by
    simpa only [coordinates,sub_zero] using yz.span i
  have big:‖C.S.place (x 0)-C.S.place (x 1)‖≤u*r:=by
    have triangle:=norm_sub_le (C.S.place (x 0)) (C.S.place (x 1))
    linarith only [triangle,span 0,span 1,show 0≤r from hr.le,
      show u*r=2*(T*r)+r from by dsimp only [u];ring]
  have separate:δ*r≤‖C.S.place (x 0)-C.S.place (x 1)‖:=by
    simpa only [coordinates] using yz.spaced 0 1 (by decide)
  have half:(1/2:ℝ)≤C.S.radius per:=div_le_div_of_nonneg_right (by exact_mod_cast (C.S.period per).property) (by norm_num)
  have inside:‖C.S.place (x 0)-C.S.place (x 1)‖<C.S.radius per:=
    big.trans_lt (by simpa only [mul_comm u r] using (((lt_div_iff₀ hu).mp thin).trans_le half))
  have native:=RG17.nativeShort C inside
  have moved:=cells C h x
  constructor
  · apply (div_le_iff₀ (C.S.a_pos k)).2
    linarith only [separate,native.2,moved.2,show ((gap C h x:ℝ)+1)*C.S.a k=C.S.a k*(gap C h x:ℝ)+C.S.a k from by ring,
      show δ/2*r=(δ*r)/2 from by ring]
  · rw [←sub_le_iff_le_add]
    apply (le_div_iff₀ (C.S.a_pos k)).2
    linarith only [native.1,big,moved.1,
      show ((gap C h x:ℝ)-1)*C.S.a k=C.S.a k*(gap C h x:ℝ)-C.S.a k from by ring]

end YM.Integration.WilsonInvariantActionSeparatedCells
