import YM.Integration.WilsonOriginalTwoFlatGridCapture
import YM.Integration.WilsonThermometerRegisteredTripleRoom

/-! Native capture rooms for the actual embedded public placements and for the microscopic
Rose cells. The same room contains every proper face at every physical cutoff and period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRHousing
open Set Filter Lattice Wilson RG Marker OPE RG16.Literal
open Extraction Cells RG12 XSpace WilsonThermometerAlignedCells
open PhysicalNext.Repeat.Legato
open scoped Classical Topology
variable {G:Gauge}(R:Run G)

theorem distance {I:Type} {j N c per:ℕ} (top:j≤N)(live:c≤N)(o:I → Cover)(K:ℕ)
    (size:∀v,‖R.family.S.gridPoint j (o v)‖≤(K:ℝ)*R.family.S.a c)
    : ∀v, separation ((R.family.S.toDepth live per).parent ((R.family.S.toDepth top per).embed
      (snap R.family j per o v))) 0 ≤ K+1 := by
  intro v
  let S:=R.family.S
  let g:=S.toDepth top per
  have eq:S.a N*(g.count.val:ℝ)=S.a j:=S.embeds_scale g
  have coord (a:Axis): |S.a N*((g.count.val • o v : Cover) a : ℝ)|≤(K:ℝ)*S.a c := by
    change |S.a N*((g.count.val • (o v a):ℤ):ℝ)|≤_
    rw [nsmul_eq_mul,Int.cast_mul,Int.cast_natCast,←mul_assoc,eq]
    exact (show ‖(S.gridPoint j (o v)) a‖≤_ from PiLp.norm_apply_le ..).trans (size v)
  change separation ((S.toDepth live per).parent (g.embed (wrap _ (o v)))) 0 ≤ _
  rw [g.embed_wrap]
  exact WilsonThermometerRegisteredPairRoom.integer S live (g.count.val • o v) K coord

theorem embedded {I:Type} {j N c per:ℕ} (top:j≤N)(live:c≤N)(o:I → Cover)(K:ℕ)
    (size:∀v,‖R.family.S.gridPoint j (o v)‖≤(K:ℝ)*R.family.S.a c)
    (capture:K+1≤(R.family.path.rep N per c).p.B) :
    ∀v, (R.family.S.toDepth live per).parent ((R.family.S.toDepth top per).embed
      (snap R.family j per o v)) ∈ halo (R.family.path.rep N per c).p.B {0}  := by
  intro v
  apply halo_spec.mpr
  refine ⟨0,by simp,?_⟩
  rw [separation_comm]
  exact (distance R top live o K size v).trans capture

theorem rose (simple:G.Simple)(φ:Test 3) : ∀ᶠ c:ℕ in atTop,
    ∀(N per:ℕ)(live:c≤N)(r:ℝ), |r|≤R.family.S.a c →
    ∀y:Site (R.family.side N per) × Site (R.family.side N per),
    mass (R:=R) r (N,per) φ y≠0 → ∀v:Fin 3,
    (R.family.S.toDepth live per).parent (atOrigin y v) ∈
      halo (R.family.path.levels.budget c).B {0} := by
  filter_upwards [WilsonThermometerRegisteredTripleRoom.spatial R simple φ] with c here
  intro N per live r fits y charged v
  exact halo_spec.mpr ⟨0,by simp,by rw [separation_comm]; exact here N per live r fits y charged v⟩

end YM.Integration.WilsonOriginalTwoFlatIRHousing
