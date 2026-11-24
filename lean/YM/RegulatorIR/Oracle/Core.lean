import YM.RegulatorIR.Oracle.Crust

/-! Core top and interior metric costs. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Oracle
open Function Finset Lattice Laurent Bloch Set Filter Budget Spatial Budget.Packet Budget.Tuple Budget.Layer Quadratic Quarry Sources Tree Tree.Forest PertExtension Geometry Geometry.Field
open FreeResolvent (Slot PAC Vec component ix tensor)
open Exterior RG Wilson Matrix
open scoped Topology ENNReal NNReal BigOperators Classical Matrix Matrix.Norms.Frobenius
variable {G: Gauge} {X Y A : Type} {n f: Side} {r s p:ℕ} {α σ δ υ:ℝ} {C:Clip}

-- evaluation through Maxwell d stencil, order exact. equality of all gauges.
variable (G) (n)
def onslot : Edge (Site n)× G.ColorIndex ≃ Slot G n 1 := (Equiv.prodAssoc _ _ _).trans (Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr axisEquiv (Equiv.refl _)))
lemma on_at (u : Site n) a i: onslot G n ((u,a),i)=(u,coord a,i):=rfl
lemma on_wrap (p:Long G.ColorIndex): onslot G n (around n p.1,p.2)=(linksQ G).swrap n p:=v_coarse p n |>.symm
variable (B:Precision.Bed)(h:B.metric.strip σ α)(hv:0≤σ)(hc:0≤α)
include G
lemma crust_f (h:B.metric.strip σ α)(hv:0≤σ)(hc:0≤α):Billed (crust G B):= (crust_price _ _ h hv hc).billed hv (ENNReal.mul_ne_top (by finiteness) ENNReal.ofReal_ne_top)
variable {G n}
private def face_map (x:Edge (Site n)→ G.Color): fieldDir G n 1:= fun i=>x (i.1,axisEquiv.symm i.2)
private lemma masking(x:Edge (Site n)→G.Color) (i: Edge (Site n)): face_map x (i.1,coord i.2)=x i:=by unfold face_map; rw [show (i.1,coord i.2).2=axisEquiv i.2 from rfl,axisEquiv.symm_apply_apply]
include G h hv hc in
lemma crust_s (hC:Precision.Floor B C f δ υ): StopB.Ellipt (crust G B) δ f:=by
 intro x
 have he := Work.F01.curl_floor hC (face_map x)
 let S := linksQ G; let y:=FreeResolvent.flatten (face_map x);let F:=ledgerRow S S (crust G B) f
 have h₁ : StopB.lifted G x=y ∘ S.swrap f:=by ext1 i; rw [Function.comp_apply, ← on_wrap G]; rcases i with ⟨e,j⟩; exact Eq.symm (congr_arg (fun z:G.Color=> z j) (masking x (around f e)))
 have hg: StopB.evenQ (crust G B) x=y ⬝ᵥ (F *ᵥ y)/2:=by
    unfold StopB.evenQ; rw [h₁];dsimp only [Function.comp_apply]; simp_rw [← Oracle.transmit S S (crust G B) y (h:=crust_f G B h hv hc) (he:=crustA G B)]
    apply congr_arg (fun s:ℝ=>s/2); rw [dotProduct,← (onslot G f).sum_comp];conv_rhs=>rw [Fintype.sum_prod_type]
    apply sum_congr rfl;intro p _;apply sum_congr rfl;intro i _
    let v:Long G.ColorIndex:= ((Lattice.lift p.1,p.2),i)
    change x p i * (F *ᵥ y) (S.swrap f v)=y (onslot G f (p,i))*_
    have hu: around f v.1=p:=by simp [around,v]
    rw [show y (onslot G f (p,i))=x p i from congr_arg (fun z:G.Color=>z i) (masking x p),← on_wrap,hu]
 have ht: y ⬝ᵥ (F *ᵥ y)=Bid.gaugeFiscal B (face_map x) (face_map x):=by
    unfold F; rw [crust_id _ _ h hv,FreeResolvent.component_dot];simp_rw [FreeResolvent.component_mul];rfl
 have hv : ∑ i:Face (Per f),‖Orb.Curl x i.1 i.2.val.1 i.2.val.2‖^2=∑ i, ‖dColor G f 1 (face_map x) i‖^2:=by
    rw [← (Equiv.prodCongr (Equiv.refl (Site f)) plaqEquiv).sum_comp]
    refine sum_congr rfl fun i _=> congr_arg (fun v:G.Color=> ‖v‖^2) ?_
    change Orb.Curl _ _ _ _=dColor G f 1 (face_map x) (i.1,plaquette i.2)
    ext1 j;change _=(Exterior.d 1 f*ᵥ _) _;rw [d_plaquettes]
    simp_rw [Exterior.parts,fun (x':Site f) k=> show face_map x (x',coord k)=_ from masking x (x',k)]
    unfold Orb.Curl; rw [PiLp.sub_apply,PiLp.sub_apply,PiLp.add_apply]; abel
 rw [hg,ht,hv];rw [← mul_div_assoc];exact div_le_div_of_nonneg_right he (by norm_num)
-- gust top. need Wick Moon equality
end YM.RegulatorIR.Oracle
