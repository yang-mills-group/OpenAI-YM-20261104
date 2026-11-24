import YM.Integration.WilsonOriginalGalleryTwinsField
import YM.RG05Readout.Many.Stage

/-! The doubled physical numerator has identically vanishing unary inputs on its own menu. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalGalleryTwinBoard
open Finset Function Lattice Wilson RG Ac Marker Push GridApprox.Nil QuadraticLocal MergeProof MergeProof.Accent MeasureTheory
open RG05Readout.Many RG05Readout.Address Extra.Histories Extra.Trajectories QuadraticLocal.Fusion.Attached Lodestar
open WilsonOriginalGalleryTwins
open scoped BigOperators Classical
variable {V T I : Type} [DecidableEq V] [Fintype V] [Countable I] {G:Gauge}{n:Side}{P:Rep G n}
  {o:V → Site n}(A:Gallery T I o P (Marks V))(x:T)(w:V → ℝ)(pos:∀i,0<w i){a:ℝ}
  (expo:0≤a)(reg:A.E.Paid (fun i=>w i^2) P.p.B a 1)(forced:A.K.Paid (fun i=>w i^2) P.p.B a 1)

include pos expo reg in
omit [Countable I] in
private theorem silent : (clear A x).part (Marks V).quiet=0:=by
  let entries:Set I:={i|A.E.clear i}
  have wp(i:V):0<w i^2:=pow_pos (pos i) _
  change (∑' i,WilsonPhysicalHistoryGroupedLamps.row A.E entries x i 1).part _=_
  rw [Poly.share ((WilsonPhysicalHistoryGroupedLamps.stored A.E _ wp entries expo reg x).repair wp 1).2]
  calc
    _ = ∑' _:I,(0:ℂ):=by
      apply tsum_congr
      intro i
      by_cases h:i∈entries <;> simp [WilsonPhysicalHistoryGroupedLamps.row,h]
    _=0:=tsum_zero

include pos expo reg forced in
theorem original (actual:Integrable (A.density x) (prior G n)):
    MenuBoard P (fun _:V×Bool=> (0:Three G n)) (entered A x) (o ∘ Prod.fst) (w ∘ Prod.fst) a 1:=by
  have wp(i:V):0<w i^2:=pow_pos (pos i) _
  have nil:=(silent A x w pos expo reg)
  have niln:(-clear A x).part (Marks V).quiet=0:=by simp [Poly.part_neg,nil]
  have opposite : Poly.pass (-clear A x)*Poly.pass (clear A x)=1:=by
    rw [←pass_add niln nil,neg_add_cancel]
    simp
  let L : Poly (Marks V) →ₗ[ℂ] Poly (Marks (V×Bool)):=
    { toFun:=fun b=>duplicate V (Poly.pass (-clear A x)*b)
      map_add':=by intros;rw [mul_add,map_add]
      map_smul':=by intros; simp }
  have same (U):L (A.density x U)=entered A x U:=by
    change duplicate V (Poly.pass (-clear A x)*A.density x U)=_
    rw [map_mul,WilsonOriginalGalleryTwinsField.original A x _ wp expo reg forced U,←mul_assoc,
      ←map_mul,opposite,map_one,one_mul]
  refine ⟨?_,fun _=>Useful.zero P,?_⟩
  · rw [show entered A x=L ∘ A.density x from (funext same).symm]
    exact L.toContinuousLinearMap.integrable_comp actual
  have profile0: (fun _ : V×Bool=>profile P.activities ((0:Three G n).2.2))=0:=by
    ext i b U
    simp [profile,cram]
  rw [profile0]
  exact paid A x w pos expo reg forced le_rfl le_rfl

end YM.Integration.WilsonOriginalGalleryTwinBoard
end
