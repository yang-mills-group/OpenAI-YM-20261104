import YM.Integration.WilsonAddressedWeakFixedChild
import YM.Integration.WilsonAddressedWeakCalibration

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakFixedPlacement
open Function Filter Set MeasureTheory Lattice Wilson RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Trace.Physical Table Spec Extraction XSpace
open WilsonAddressedWeakCalibration WilsonAddressedWeakFixedChild
open scoped BigOperators Classical Topology
variable {G:Gauge} (R:Run G) {k N p:ℕ}
local notation "Rf"=>R.family

private theorem axes {x y : Points 2} {b : ℝ} (hb : 0 < b)
    (close : ∀ i j, |x i j - y i j| ≤ b) : dist x y ≤ 8*b := by
  let E := x-y
  rw [dist_eq_norm]
  change ‖E‖ ≤ 8*b
  rw [←sq_le_sq₀ (norm_nonneg _) (by positivity),←(Points.flatten.norm_map E),EuclideanSpace.real_norm_sq_eq]
  calc _ ≤ ∑ _ : Fin 2 × Axis, b^2 := Finset.sum_le_sum fun i _=> sq_le_sq.mpr (by
         rw [abs_of_pos hb]; exact close i.1 i.2)
       _ ≤ _ := by
         simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,
           Nat.cast_mul,Nat.cast_ofNat]
         norm_num
         nlinarith [sq_nonneg b]

/-- Slide the two nominated fine residues into the two coarse cells of a prescribed real pair.
The new real read uses exactly those same fine residues at every finite cutoff and period. -/
theorem original (hk:k≤N) (ρ:ℝ) (pos:0<ρ) (x:Points 2) (z:Fin 2→Site ((Rf).side N p)):
    ∃ y:Points 2,
      WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) y=
        (fun i=>slide R hk (z i) (((Rf).S.toDepth hk p).parent (WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x i))) ∧
      dist y x≤24*((Rf).S.a k/ρ):=by
  let S:=(Rf).S;let g:=S.toDepth hk p
  let b:=lifts R (p:=p) hk ρ pos x
  let q (i:Fin 2):Cover:=g.count.val • b i+lift (g.residue (z i))
  let v:=ρ⁻¹ • tag (S.a k) b
  have par:=(actual R (p:=p) hk ρ pos x).1
  refine ⟨ρ⁻¹ • tag (S.a N) q,?_,?_⟩
  · funext i
    unfold WilsonPositionPhysicalCellTest.site
    simp only [smul_smul,mul_inv_cancel₀ pos.ne',one_smul]
    change wrap (S.side N p) (address (S.a N) (tag (S.a N) q) i)=_
    rw [address_matched (S.a_pos N)]
    have eq:wrap (S.side N p) (q i)=g.assemble (wrap (S.side k p) (b i),g.residue (z i)):=by
      simp only [q,map_add,Ratio.assemble,Ratio.embed_wrap]
    rw [eq]
    have sh:=parents R hk (z i) (g.parent (WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x i))
    calc _=g.assemble (g.parent (slide R hk (z i) (g.parent (WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x i))),
                        g.residue (slide R hk (z i) (g.parent (WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x i)))):=by
               rw [sh.1,sh.2,par]
         _=_:=g.unpack_at _
  · have scale:S.a N*g.count.val=S.a k:=S.embeds_scale g
    have fees:dist (tag (S.a N) q) (tag (S.a k) b)≤8*S.a k:=by
      apply axes (S.a_pos k);intro i j
      have cent:=lift_centers (g.residue (z i)) j
      have tiny:|(lift (g.residue (z i)) j:ℝ)|≤g.count.val:=by
        have t:|lift (g.residue (z i)) j|≤(g.count.val:ℤ):=abs_le.mpr ⟨by omega,by omega⟩
        exact_mod_cast t
      have ar:(q i j:ℝ)=(g.count.val:ℝ)*(b i j:ℝ)+lift (g.residue (z i)) j:=by
        change (↑(g.count.val • b i j + lift (g.residue (z i)) j):ℝ)=_
        rw [nsmul_eq_mul,Int.cast_add,Int.cast_mul,Int.cast_natCast]
      change |S.a N*(q i j:ℝ)-S.a k*(b i j:ℝ)|≤S.a k
      rw [ar,←scale]
      calc _=|S.a N*(lift (g.residue (z i)) j:ℝ)|:=by congr 1;ring
           _≤_:=by rw [abs_mul,abs_of_pos (S.a_pos N)];exact mul_le_mul_of_nonneg_left tiny (S.a_pos N).le
    have shift:dist (ρ⁻¹ • tag (S.a N) q) v≤8*(S.a k/ρ):=by
      rw [dist_eq_norm,←smul_sub,norm_smul,Real.norm_of_nonneg (inv_pos.mpr pos).le]
      rw [dist_eq_norm] at fees
      calc _≤ ρ⁻¹*(8*S.a k):=mul_le_mul_of_nonneg_left fees (inv_pos.mpr pos).le
           _=8*(S.a k/ρ):=by ring
    exact (dist_triangle _ v x).trans ((add_le_add shift (actual R (p:=p) hk ρ pos x).2).trans_eq (by ring))
end YM.Integration.WilsonAddressedWeakFixedPlacement
end
