import YM.Integration.WilsonMovingForkAbsolutePhase

/-! One simultaneous genuine translation at the original microscopic Wilson
integral. The assertion is made solely about the unconditioned quantity. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkCommonTranslation
open Function Finset MeasureTheory Lattice Wilson RG Source Marker Multi Extraction
open Push.GridApprox Extra.Trajectories PhysicalNext.Repeat.Legato
open WilsonOriginalTwoFlatGridCapture (word)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){I:Type}[Fintype I]{j N p:ℕ}
local notation "C" => R.family

theorem original (d:I → ℕ)(top:j≤N)(o:I → Cover)(v:∀i,(C).label (d i))(z:Cover):
    (C).omega N p (word R d j N p top (fun i=>o i+z) v)=(C).omega N p (word R d j N p top o v):=by
  let H:=(C).S.toDepth top p
  let y:=fun i=>H.embed (wrap ((C).side j p) (o i))
  let t:=H.embed (wrap ((C).side j p) z)
  let W:=fun U=>∏i,(C).O N p (v i) (y i) U
  have seat(i:I):H.embed (wrap ((C).side j p) (o i+z))=y i+t:=by
    rw [map_add]
    exact H.root.map_add _ _
  change moment ((C).beta N p) (fun U=>∏i,(C).O N p (v i) (H.embed (wrap _ (o i+z))) U)=moment _ W
  simp_rw [seat]
  have equal:(fun U=>∏i,(C).O N p (v i) (y i+t) U)=W ∘ translate t:=by
    funext U;simp only [W,Function.comp_apply,Family.O,TransferData.cylinder,initial,Pi.smul_apply,
      SectionData.places_trans]
  have cont:Continuous W:=continuous_finsetProd _ fun i _=>(C).continuousO N p (d i) (v i) (y i)
  have sale:=moment_pull ((C).beta N p) 1 t W (cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  rw [show pull (K:=G.El) 1 t=Lattice.translate t from funext (pull_one t)] at sale
  rw [equal];exact sale

end YM.Integration.WilsonMovingForkCommonTranslation
