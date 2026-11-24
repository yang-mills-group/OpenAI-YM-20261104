import YM.FVA2.Facade.Build
/-!
 # Frozen prefix world

 Collapse FINAL coarse nodes (all planted nodes) to *one* none-root node; discard
 their links from Loom only. We keep ALL their values external to the Haar transfer.
 This implements the prefix integration's interior gauge-fixing as a root truss on
 that exact world. Don't evolve coarse gauge-transformation variables independently:
 interior spin once on all layers. This is also not the `L.loom.Truss` on a Fabric;
 that one necessarily fixes a tree over even the final coarse degrees.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Facade
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open Function Filter Set MeasureTheory PertExtension Precision Lattice GaussianScore PowerSeries Chart RG
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric Papers MarkovChain Warp Line Roof Router OpenSlots.Quadratic
open PertExtension.Orb
open scoped Classical Topology BigOperators
variable {G: Gauge} {c f n:Side}

abbrev Interior (S: StepData c f):={v:Vertex f// ¬planted S.ratio v}
def Quick {n:Side}(L: Fabric G n) : Type:= match L with
 | .endcap _ _=> Empty
 | .layer S _ _ _ L=> Interior S⊕Quick L
 def Used {n:Side}(L: Fabric G n) : Type:= match L with
 | .endcap _ _=> Empty
 | .layer (f:=f) _ _ _ _ L=> OEdge f ⊕Used L
@[implicit_reducible] def iQ {n:Side}(L: Fabric G n):Fintype (Quick L):= by
 cases L with
 | endcap=> unfold Quick; infer_instance
 | layer _ _ _ _ L=> letI:= iQ L; unfold Quick; infer_instance
termination_by structural L
@[implicit_reducible] def iU {n:Side}(L: Fabric G n):Fintype (Used L):= by
 cases L with
 | endcap=> unfold Used; infer_instance
 | layer _ _ _ _ L=> letI:= iU L; unfold Used; infer_instance
termination_by structural L
attribute [instance] iQ iU
abbrev Hub (L:Fabric G n):= Option (Quick L)

 def hub {n:Side}(L:Fabric G n)(v:Vertex n): Hub L:= match L with
 | .endcap _ _=> none
 | .layer S _ _ _ L=> if h:planted S.ratio v then Option.map Sum.inr (hub L (ancestral S.ratio v)) else some (Sum.inl (Subtype.mk v h : Interior S))

section
variable (S:StepData c f){H:S.patch.Branches S.kernel G}{hf:Even f.val}{t:S.Choices}{L:Fabric G c}
local notation "Γ"=> layer S H t hf L
 def embed_next : Hub L→ Hub Γ:= fun x=> (Option.map (Sum.inr (α:=Interior S)) x)
local notation "F"=> embed_next (H:=H) (hf:=hf) (t:=t) (L:=L) S
lemma hubs (v : Vertex c): hub Γ (placement S.ratio v)= F (hub L v):= by
 rw [hub, dif_pos (show planted S.ratio (placement S.ratio v) from by unfold planted; rw [ancestor S.patch.odd_side]),ancestor S.patch.odd_side]; rfl
end
lemma hub0 {n:Side}(L: Fabric G n) : hub L 0=none:= by cases L with
                                                      | endcap=> rfl
                                                      | layer S H t hf L=> rw [←place_zero S.ratio, hubs,hub0 L]; rfl
termination_by structural L

 def source {n:Side}(L:Fabric G n) : Used L→ Hub L:= match L with
 | .endcap _ _=> Empty.elim
 | .layer S H t hf L=> Sum.elim (fun x=> hub (layer S H t hf L) ((rim _).fromEdge x)) (fun i=> embed_next (H:=H) (hf:=hf) (t:=t) S (source L i))
 def target {n:Side}(L:Fabric G n) : Used L→ Hub L:= match L with
 | .endcap _ _=> Empty.elim
 | .layer S H t hf L=> Sum.elim (fun x=> hub (layer S H t hf L) ((rim _).toEdge x)) (fun i=> embed_next (H:=H) (hf:=hf) (t:=t) S (target L i))

variable (L:Fabric G n)
 def rift: Loom (Hub L) (Used L) := ⟨none,Facade.source L,Facade.target L⟩

-- pack all degrees from top to bottom (optionally used on pinned tree too)
 def rear {n:Side}(L:Fabric G n)(a:LinkFrame G (Bottom L)) : (Used L→ G.El)→ L.LinksOn:= match L with
 | .endcap _ _=> fun _=> Sum.elim a (fun i : Empty=> i.elim)
 | .layer _ _ _ _ L=> fun x=> Sum.elim (fun i=> x (Sum.inl i)) (rear L a (fun i=>x (Sum.inr i)))

section
variable (S:StepData c f) (H:S.patch.Branches S.kernel G) (hf:Even f.val)(t:S.Choices)(U:Fabric G c)
local notation "Γ"=> layer S H t hf U
lemma main_rear (a:LinkFrame G (Bottom U))(x): (Γ).principal (rear Γ a x)=fun i=> x (Sum.inl i):= rfl
lemma future_rear (a:LinkFrame G (Bottom U))(x) : future S H t hf U (rear Γ a x)= rear U a (fun i=> x (Sum.inr i)):= rfl
local notation "F"=> embed_next (H:=H) (hf:=hf) (t:=t) (L:=U) S
lemma spinNow (u: Used Γ→ G.El)(g:Hub Γ→ G.El)(i:OEdge f): (rift Γ).spin g u (Sum.inl i)= (rim f).spin (g ∘ hub Γ) (fun i=> u (Sum.inl i)) i:= rfl
lemma spinLater (u:Used Γ→ G.El)(g:Hub Γ→ G.El)(i:Used U): (rift Γ).spin g u (Sum.inr i)= (rift U).spin (g ∘ F) (fun i=>u (Sum.inr i)) i:=rfl
end
lemma rear_spin {n:Side}(L:Fabric G n) (g:Hub L→ G.El)(h:g none=1)(a:LinkFrame G (Bottom L))(u:Used L→ G.El) : rear L a ((rift L).spin g u)= L.loom.spin (g∘ hub L) (rear L a u):= by
 cases L with
 | endcap n he=>
    let A:= rear (endcap (G:=G) _ he) a u
    ext1 (i|i)
    · change a i= g none * a i * (g none)⁻¹; rw [h,one_mul,inv_one,mul_one]
    exact Empty.elim i
 | @layer c f S H t hf L=>
    let Γ:= layer S H t hf L; ext1 (i|i); exact spinNow ..
    let F:= embed_next (H:=H) (t:=t) (hf:=hf) (L:=L) S
    let Y:= fun i:Used L=> u (Sum.inr i); let j (x:L.Path) : Γ.Path:= Sum.inr x
    let w:= rear L a
    have hh : w ((rift L).spin (g ∘ F) Y)= future S H t hf L (Γ.loom.spin (g∘ hub Γ) (rear Γ a u)) := by
       unfold Γ; rw [spin_future,future_rear];
       rw [show ((g ∘ hub (layer S H t hf L)) ∘ placement S.ratio)= (g ∘ F) ∘ hub L from funext (fun i=> congr_arg g (hubs S i))]; exact rear_spin L (g∘F) h _ _
    exact congr_fun hh (show L.Path from i)
termination_by structural L

lemma rear_cont {n:Side}(L:Fabric G n): Continuous (Function.uncurry (rear L)):= by
 cases L with
 | endcap k b=> apply continuous_pi; rintro (i|i); exact (continuous_apply i).comp continuous_fst; exact Empty.elim i
 | @layer c f S H t hf L=>
    let Γ:=layer S H t hf L
    apply continuous_pi; rintro (i|i); exact (continuous_apply (show Used Γ from Sum.inl i)).comp continuous_snd
    let j:L.Path:= i; let A:(LinkFrame G (Bottom L) × (Used Γ→G.El))→ (LinkFrame G (Bottom L) × (Used L→G.El)):= fun x=>(x.1,fun i=>x.2 (Sum.inr i));
    exact (continuous_apply j).comp ((rear_cont L).comp (show Continuous A from continuous_fst.prodMk (continuous_pi (fun i=>(continuous_apply (show Used Γ from Sum.inr i)).comp continuous_snd))))
termination_by structural L

-- literal gauge action and its curtain observables at frozen links and rooted spins
lemma rift_price (z:L.Accounts→ℝ) (u : Used L→ G.El)(g:Hub L→ G.El)(h:g none=1)(a:LinkFrame G (Bottom L)): L.spend z (rear L a ((rift L).spin g u))= L.spend z (rear L a u):= by rw [rear_spin L g h, L.invariant_cost]
lemma rift_marks (O:Wilson.Config G n→ℝ)(h:PreTest O) (u:Used L→G.El) (g:Hub L→ G.El)(he:g none=1)(a) : attending L O (rear L a ((rift L).spin g u)) = attending L O (rear L a u):= by
 rw [rear_spin L g he]; apply (StationaryMarks.eligible L h).reading.leg; change g (hub L 0)=1; rw [hub0 L]; exact he
end YM.FVA2.Facade
