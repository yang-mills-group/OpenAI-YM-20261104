import YM.FormalOPE.RG10.MarkovChain.Warp
/-!
 # migratory multiplicative and additive criterion
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.MarkovChain
open Function Filter Topology Set MeasureTheory PertExtension Precision
open Inherit Push.Loops Chart Lattice RG GaussianScore PowerSeries
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric
open Papers Warp Line Roof
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G: Gauge} {c f n: Side}
variable {S:StepData c f} {H:S.patch.Branches S.kernel G}{t:S.Choices}{hf:_root_.Even f.val}{L:Fabric G c} {C:Cloth L}{P:Inside S.ratio}
-- $W(x,y)W(0,z)=W(x,z)W(0,y)$ plus inheritance. No units demanded.
local notation "T0"=> Cloth.inLayer (t:=t) (b:=H) (h:=hf) P C
open Splice
/-- Same decomposition as `sector`; use cloth at all module signatures including typeclass instances. -/
 def Pathway : (Cross (G:=G) S P × Field C.choose) ≃ₗ[ℝ] Field ((T0).choose):= sector S H t hf L P C.choose
local notation "d"=> Pathway (S:=S) (H:=H) (t:=t) (hf:=hf) (C:=C) (P:=P)
variable {L':Fabric G n}
 def Successor (u: Ticket (Field ((T0).choose))): Ticket (Field C.choose):= boost (coarse d) u
 def Ancestor (u:Ticket (Field C.choose)): Ticket (Field ((T0).choose)):= boost ((LinearMap.snd ..) ∘ₗ (d).symm.toLinearMap) u
-- allow direct rule .mul∧.2 rather than refolding Vault
 def paired (u:Ticket (Field ((T0).choose))): Prop:= ∀ x:Cross (G:=G) S P,∀ y z: Field C.choose, send _ y=send C.choose z → Stack.read (d (x,y)) u * Stack.read (d (0,z)) u= Stack.read (d (x,z)) u * Stack.read (d (0,y)) u
-- avoid implicits that break inference use param T & defs
 def Vault {n:Side}{L:Fabric G n} (T:Cloth L)(v:Ticket (Field T.choose)): Prop:= match T with
 | .floor _ _ _=> True
 | .inLayer (b:=H) (t:=t) (h:=hf) P C=> paired (H:=H) (hf:=hf) (t:=t) (P:=P) (C:=C) v ∧ Vault C (boost (coarse (Pathway (H:=H) (hf:=hf) (t:=t) (P:=P) (C:=C))) v) -- not Succ to avoid high simp
 def Library {L:Fabric G n}(T:Cloth L)(v:Ticket (Field T.choose)): Prop:= ∀ i, Roof T (coeff i v).val
namespace Vault
lemma jointly {u v:Ticket (Field ((T0).choose))} (hu:paired (H:=H) (t:=t) (hf:=hf) (P:=P) (C:=C) u)(hv:paired v): paired (u*v):= by
 intro x y z h; specialize hu x y z h; specialize hv x y z h
 simp only [_root_.map_mul]
 rw [mul_mul_mul_comm (Stack.read (d (x,y)) u) (Stack.read (d (x,y)) v) (Stack.read (d (0,z)) u), hu,hv, mul_mul_mul_comm (Stack.read (d (x,z)) u) (Stack.read (d (x,z)) v) (Stack.read (d (0,y)) u)] -- test rhs rewrite
lemma mul {n:Side} {L:Fabric G n} {T:Cloth L}{u v:Ticket (Field T.choose)}(hu:Vault T u) (hv:Vault T v): Vault T (u*v):= by
 cases T with
 | floor=> trivial
 | @inLayer c f S H t hf L P C=>
   rw [Vault] at hu hv ⊢;
   refine ⟨jointly hu.1 hv.1,?_⟩; rw [_root_.map_mul]; exact mul hu.2 hv.2
termination_by structural T

lemma openHW {u:Ticket (Field ((T0).choose))} (h:Library T0 u) (x y z) (hA:send C.choose y=send C.choose z) :
 Stack.read (d (x,y)) u+Stack.read (d (0,z)) u = Stack.read (d (x,z)) u + Stack.read (d (0,y)) u:= by
 apply PowerSeries.ext; intro i; specialize h i; rw [Roof] at h
 have he:(coeff i u).val (d (x,y)) - (coeff i u).val (d (0,y)) = (coeff i u).val (d (x,z)) - (coeff i u).val (d (0,z)):= h.1 x y z hA
 simp_rw [map_add, Stack.reading_term]
 linarith [he]
lemma continued {u:Ticket (Field ((T0).choose))} (h:Library T0 u): Library C (boost (coarse d) u):= by
 intro i; specialize h i; rw [Roof] at h; unfold boost; rw [coeff_map]; exact h.2
lemma sealing {u:Ticket (Field ((T0).choose))} (h:Library T0 u)(Hz:constantCoeff u=0): paired (Stack.exponential u):= by
 intro x y z hu
 simp_rw [exponent, ← Formal.multispecies (RingHom.id _) (wrap Hz (d (x,y))) (wrap Hz (d (0,z))), ←Formal.multispecies (RingHom.id _) (wrap Hz (d (x,z))) (wrap Hz (d (0,y))), openHW h x y z hu]
lemma expForm {n: Side}{L:Fabric G n}{T:Cloth L}{W:Ticket (Field T.choose)} (h:Library T W)(Hz:constantCoeff W=0):Vault T (Stack.exponential W):= by
 cases T with
 | floor=>trivial
 | @inLayer c f S H t hf L P C=>
   rw [Vault]; refine ⟨sealing h Hz,?_⟩; rw [boost_exp]; exact expForm (continued h) (vacant _ Hz)
termination_by structural T
end Vault
end YM.FormalOPE.RG10.MarkovChain
