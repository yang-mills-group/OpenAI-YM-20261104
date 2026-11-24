import YM.RegulatorIR.Oracle.Core

/-! Top identities. Equality by full-period polarization; in particular
rank packets on all periodic data. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Oracle
open Function Finset Lattice Laurent Bloch Set Filter Budget Spatial Budget.Packet Budget.Tuple Budget.Layer Quadratic Quarry Sources Tree Tree.Forest PertExtension Geometry Geometry.Field
open FreeResolvent (Slot PAC Vec component ix tensor)
open Exterior RG Wilson Matrix
open scoped Topology ENNReal NNReal BigOperators Classical Matrix Matrix.Norms.Frobenius
variable {G: Gauge} {X Y A : Type} {n f: Side} {α σ δ υ:ℝ} {C:Clip}
section rays
variable (x y:Vec G n 1)
def plasm(v:Site n)(e:PlaqAxes)(u:G.ColorIndex):= (Exterior.d 1 n*ᵥ (FreeResolvent.component x u)) (v,plaquette e)
def compositionE (v:Site n)(k:Axis)(e:PlaqAxes)(i:G.ColorIndex) := let h:=e.val.1;let l:=e.val.2; (if k=h then plasm x v e i-plasm x (v-step l) e i else 0)+(if k=l then plasm x (v-step h) e i-plasm x v e i else 0)
lemma bill_sun (v:Cover)(e:PlaqAxes)(u:G.ColorIndex) : combo (x∘ (linksQ G).swrap n) (sun v e u)=plasm x (wrap n v) e u:=by
 simp_rw [sun,map_sub,map_add,combo,Finsupp.linearCombination_single,one_smul,Function.comp_apply,v_coarse]; rw [plasm,d_plaquettes]; simp only [map_add,wrap_step,FreeResolvent.component,FreeResolvent.ix]; abel
lemma bill_dream (v: Long G.ColorIndex)(e:PlaqAxes):combo (x∘ (linksQ G).swrap n) (dream v.1 e v.2)= compositionE x (wrap n v.1.1) v.1.2 e v.2 :=by simp only [compositionE,dream]; split_ifs <;> simp only [map_sub,map_zero,map_add] <;> simp [bill_sun]
lemma footprint (i: Long G.ColorIndex): (ledgerRow (linksQ G) (linksQ G) (finer moon) n*ᵥ x) ((linksQ G).swrap n i)= ∑ k,compositionE x (wrap n i.1.1) i.1.2 k i.2:=by rw [cargo_of _ _ _ _ _ moon (puff G) x,moon,map_sum]; simp_rw [bill_dream]
lemma bunch (i: Edge (Site n))(j:G.ColorIndex) : (ledgerRow (linksQ G) (linksQ G) (finer moon) n*ᵥ x) (onslot G n (i,j))=∑ k,compositionE x i.1 i.2 k j:=by
 let p:Long G.ColorIndex:= ((Lattice.lift i.1,i.2),j)
 have ht:= footprint x p
 change _= ∑ k,compositionE x (wrap _ (Lattice.lift i.1)) i.2 k j at ht; rw [← on_wrap,show around n p.1= i from (by unfold p; simp [around]),wrap_lift] at ht; exact ht
private lemma flow {g h:Site n→ℝ}(v:Site n): (∑ p,g p*h (p-v))=∑ p,g (p+v)*h p:=by rw [← Equiv.sum_comp (Equiv.addRight v) (fun p=>g p*h (p-v))]; exact Finset.sum_congr rfl fun p _=>by simp
lemma staffed (a:G.ColorIndex) (b:PlaqAxes) : ∑ e:Edge (Site n), x (onslot G n (e,a))*compositionE y e.1 e.2 b a= ∑ i:Site n,plasm x i b a*plasm y i b a:=by
 let u:=b.val.1;let v:=b.val.2;let F (i:Site n):=x (onslot G n ((i,u),a));let K(i):=x (onslot G n ((i,v),a));let S(n):=plasm y n b a
 have he(i):∑ j:Axis,x (onslot G n ((i,j),a))*compositionE y i j b a=F i*S i+K i*S (i-step u) - (F i*S (i-step v)+K i*S i):=by
    simp_rw [compositionE]; simp only [mul_add,mul_ite,mul_zero, Finset.sum_add_distrib,Finset.sum_ite_eq', Finset.mem_univ,if_true]; unfold F K S u v;ring
 rw [Fintype.sum_prod_type];simp_rw [he];rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_add_distrib,flow (g:=K),flow (g:=F), ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl;intro i _; rw [plasm,d_plaquettes]; unfold FreeResolvent.component FreeResolvent.ix; change _=(K (i+step u)-K i-(F (i+step v)-F i))* S i; ring
variable {B:Precision.Bed} (H:Precision.Floor B C n δ υ)(V:B.diagonal.acts n=1)
include H V
lemma flashes : x ⬝ᵥ (ledgerRow (linksQ G) (linksQ G) (finer moon) n*ᵥ y)= x ⬝ᵥ (FreeResolvent.tensor G (Precision.K (B.metric.acts n)) *ᵥ y) :=by
 rw [FreeResolvent.component_dot (u:=x) (v:=FreeResolvent.tensor G _*ᵥ y)]; simp_rw [FreeResolvent.component_mul,Precision.K,Matrix.mul_assoc,H.same, V,Matrix.one_mul] -- replace
 let f(a:G.ColorIndex)(b:PlaqAxes)(e:Edge (Site n)):=x (onslot G n (e,a))*compositionE y e.1 e.2 b a
 rw [dotProduct,← Equiv.sum_comp (onslot G n),Fintype.sum_prod_type]; simp_rw [bunch, Finset.mul_sum]; rw [Finset.sum_comm]; refine sum_congr rfl fun i hi=>?_
 rw [Finset.sum_comm]; simp_rw [staffed x y i,← mulVec_mulVec,dotProduct_transpose_mulVec]; rw [dotProduct_comm ((Exterior.d 1 n)*ᵥ _),dotProduct]
 rw [← Equiv.sum_comp (Equiv.prodCongr (Equiv.refl (Site n)) plaqEquiv), Fintype.sum_prod_type] -- wrong target
 rw [Finset.sum_comm]; rfl
end rays
lemma symmetry_h (G:Gauge)(B: Precision.Bed) (F:∀ n,Precision.Floor B C n δ α)(hs:0≤σ)(ht:0≤α)(h:B.metric.strip σ α):Function.swap (crust G B)=crust G B :=by
 let H:= crust G B;let V:=linksQ G;have hx:= (fond V V _ (color_strip G _ (FreeResolvent.hBlock_width hs h) (FreeResolvent.kinPrice_nn _ α ht))).buys hs
 apply solely V V hx.2 (hx.1) (Albedo.swap (crustA G B)) (crustA G B) (Eventually.of_forall fun i=> ?_)
 intro p; change ledgerRow V V (Function.swap (crust G B)) p=ledgerRow V V (crust G B) p; rw [Ledger.rev _ _ p (crustA G B),crust_id G B h hs p,FreeResolvent.tensor_transpose]; apply congr_arg; unfold Precision.K; rw [Matrix.transpose_mul,Matrix.transpose_mul,(F p).symmetric.1, Matrix.transpose_transpose,Matrix.mul_assoc]
lemma moon_copy (G:Gauge)(B: Precision.Bed) (F:∀ n,Precision.Floor B C n δ α)(Y:∀ n,B.diagonal.acts n=1)(hs:0≤σ)(ht:0 ≤ α)(h:B.metric.strip σ α): crust G B=finer moon:=by
 let S:=linksQ G; apply solely S S (crust_f G B h hs ht) ((FundE.bill_s (puff G) (fun i=>(moon i).hasFiniteSupport) 0).buys le_rfl).1 (crustA G B) (puff G) (Eventually.of_forall fun i=>?_); intro p
 ext1 x y;  rw [crust_id G B h hs p]; have hp:=flashes (G:=G) (Pi.single x 1) (Pi.single y 1) (F p) (Y p)
 let M:=FreeResolvent.tensor G (Precision.K (B.metric.acts p))
 change M x y= _; have hv (M:Matrix (FreeResolvent.Slot G p 1) (FreeResolvent.Slot G p 1) ℝ): Pi.single x 1 ⬝ᵥ (M*ᵥ Pi.single y 1)=M x y:=by rw [dotProduct_comm, dotProduct_single_one]; exact dotProduct_single_one ..
 exact (hv M).symm.trans (hp.symm.trans (hv _))
end YM.RegulatorIR.Oracle
