import YM.Integration.WilsonOriginalTwoFlatGrid
import YM.Integration.WilsonAddressedPublicOpticalPair

/-! A physical gap of original grid-test points in the ordered finite torus. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonAddressedPublicPairGeometry
open Lattice RG Wilson Source MergeProof MergeProof.Accent OPE Ribbons Cells
open Classical Next.Rank.Station Extra.Histories RG16 RG16.Literal
variable {G:Gauge}(C:Family G)

theorem gap {site N p:ℕ}(later:site ≤ N)(x y:Cover)
    (inside₀:‖C.S.gridPoint site (x-y)‖ ≤ 1):
    ‖C.S.gridPoint site x-C.S.gridPoint site y‖ ≤
    2*C.S.a N*(separation (Cells.location C.S site N p x) (Cells.location C.S site N p y):ℝ):=by
  have prior:=(normC C site p (wrap (C.side site p) (x-y))).2
  rw [inside C site p inside₀,Frontier6.Road.grid_sub C site,map_sub] at prior
  simp only [separation,sub_zero] at prior
  simp only [Cells.location,dif_pos later,both,Nat.cast_mul]
  rw [←C.S.embeds_scale (C.S.toDepth later p)] at prior
  apply prior.trans_eq
  dsimp [separation]
  ring

end YM.Integration.WilsonAddressedPublicPairGeometry
end
