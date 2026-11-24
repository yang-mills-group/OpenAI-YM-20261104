import YM.QuadraticLocal.Sunrise.Crowns
/-!
 # Elementary polynomial algebra and price of finite differences

 Horizontal constant markers for reading the auxiliary bill: `λ:ι→ℝ`. Freeze each label/template
 and look up perturbations by `θ:ι→Bool` at the true coupling. Extract all in the SAME query, not
 separate moments/fiber basis. Need TOTAL valence relative to virtual powers paying no repeats
 in estimate. Only at regulator-integral polynomial precision; Φ order still ordinary unmasked
 coefficient on all periods. Even if λ test-support cost signed, keep truth.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Aperture
open Function Filter MeasureTheory Finset Lattice
open Topology AllOrder AllOrder.Fire AllOrder.Laplace
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response
open Marker Multi Sunrise
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge} {L n f: Side}{Y:Type}{k m d r:ℕ}
-- degree-separable buying. May instantiate C by rank and marker legs.
structure Drawer (Y:Type) where
  Screen : (Y→ℝ)→ Prop
  const (v:ℝ) : Screen (fun _=>v)
  add {f g:Y→ℝ} : Screen f→Screen g→ Screen (f+g)
  mul {f g:Y→ℝ} : Screen f→Screen g→ Screen (f*g)
instance (Y:Type) : CoeFun (Drawer Y) (fun _=>(Y→ℝ)→Prop):= ⟨Drawer.Screen⟩
namespace Drawer
variable {V X:Type}(C:Drawer Y)
lemma scales {f:Y→ℝ} (h:C f)(c:ℝ):C (c•f):=C.mul (C.const _) h
lemma opposes {f:Y→ℝ}(h:C f):C (-f):= neg_one_smul ℝ f ▸ scales C h (-1)
-- any rotor#m.Paint.Select. No ζ price.
abbrev view (x:V→ℝ)(L:Multiset V):=(L.map x).prod
abbrev Knife (V:Type):= V→ℝ
def shape (L:Multiset V)(f:Y→ℝ): ((V→ℝ) × Y)→ℝ:= fun x=> view x.1 L * f x.2
local notation "M"=> Multiset V
local notation "Vs"=> Knife V
inductive School (C:Drawer Y) (k:ℕ) : ((Knife V) × Y→ℝ)→ Prop where
 | one (L:Multiset V) (h:L.card≤k)(f:Y→ℝ)(hf:C f): School C k (shape L f)
 | graft {u v : (Knife V) × Y→ℝ}: School C k u→School C k v→School C k (u+v)
namespace School
variable (V)
local notation "P"=> (V→ℝ) × Y
local notation "D"=> Drawer.School (V:=V) C
lemma constant (k:ℕ)(f:Y→ℝ)(hf:C f): (D) k (fun p:P=> f p.2):= by
 convert School.one (C:=C) (0:Multiset V) (show (0:Multiset V).card ≤ k from Nat.zero_le _) f hf using 1; ext1 x; change f x.2=(1:ℝ)*_; rw [one_mul]
lemma stable (k:ℕ)(v:ℝ):School (V:=V) C k (fun (_:P)=>v):=constant V C k (fun _=>v) (C.const _)
lemma coordinates (i:V) (k:ℕ)(h:0<k): D k (fun x=> x.1 i):= by
 convert School.one (C:=C) ({i}: Multiset V) (show _ ≤ k from Multiset.card_singleton _|>.trans_le h) (fun (_:Y)=>1) (C.const 1) using 1; ext1 x; simp [shape,view]
lemma sit_v (i:V)(f:Y→ℝ)(k:ℕ)(hf:C f)(h:0<k): D k (fun x=> x.1 i*f x.2):= by
 convert School.one (C:=C) ({i}:Multiset V) ((Multiset.card_singleton _).trans_le h) f hf using 1; ext1 x; simp [shape,view]
variable {C V} {u v:(V→ℝ) × Y→ℝ}
lemma up (h:School C k u)(hk:k ≤ m):School C m u:=by induction h with | one s hs f hf=> exact School.one s (hs.trans hk) f hf | graft _ _ x y=> exact x.graft y
lemma product (h:School C k u)(hz:School C m v): School C (k+m) (u*v):= by
 induction hz with
 | graft _ _ x y=> rw [mul_add]; exact x.graft y
 | one s hl f hf=>
   induction h with
   | one L h' g hg=>
      have he:(L+s).card≤ k+m:= Multiset.card_add ..|>.trans_le (add_le_add h' hl)
      convert School.one (C:=C) (L+s) he (g*f) (C.mul hg hf) using 1; ext1 x; change view x.1 L * g x.2*(view x.1 s*f x.2)=view x.1 (L+s)*(_*_); rw [view,view,view,Multiset.map_add,Multiset.prod_add]; ring
   | graft _ _ x y=> rw [add_mul]; exact x.graft y
lemma scale (h:School C k u)(a:ℝ): School C k (a•u):= Nat.zero_add k ▸ (stable V C 0 a).product h
lemma negate (h:School C k u): School C k (-u):= neg_one_smul ℝ u ▸ scale h (-1)
lemma sub (h:School C k u)(hv:School C k v): School C k (u-v):= sub_eq_add_neg u v ▸ h.graft hv.negate
lemma pivot {X':Type*}{s:Finset X'}(U:X'→((V→ℝ) × Y→ℝ))(h:∀ i∈s, School C k (U i)): School C k (∑ i∈s,U i):= by
 induction s using Finset.induction_on with
 | empty=> rw [Finset.sum_empty]; exact stable _ _ _ 0
 | insert i j hi ih=> rw [Finset.sum_insert hi]; exact (h i (mem_insert_self ..)).graft (ih fun i hi=> h _ (mem_insert_of_mem hi))
lemma knows (h:School C k u) (x: V→ℝ): C (fun y=> u (x,y)):= by
 induction h with
 | one L h f hf=> exact C.scales hf (view x L)
 | graft _ _ y z=> exact C.add y z
section poly
variable [Fintype V]
lemma simpleR (L:Multiset V) : Rank (Knife V) L.card (fun x=> view x L):= by
 induction L using Multiset.induction_on with
 | empty=> exact Rank.nil _ 1
 | cons i L ih=> rw [Multiset.card_cons]; let z:= ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:V=>ℝ) i; convert Rank.dot z _ ih using 1; ext1 x; simp [view,z]
lemma rankR (h:School C k u)(y:Y): Rank (Knife V) k (fun x=> u (x,y)):=by
 induction h with
 | one L h f hf=>
    convert ((simpleR L).up h).scal (f y) using 1; ext1 x; exact mul_comm (view x L) (f y)
 | graft _ _ f g=> exact f.add g
lemma understands (h: School C k u)(y:Y): Plausible (fun x=>(u (x,y))):=(h.rankR y).read
end poly
section average
variable (T:X→(Y→ℝ)→ℝ) (C':Drawer X) (he:∀ u:Y→ℝ,C u → C'.Screen (fun x=>T x u)) (hs:∀ u v:Y→ℝ,C u→C v→∀ x,T x (u+v)=T x u+T x v)(hf:∀ u:Y→ℝ,C u→∀ (p:ℝ) x,T x (p•u)=p*T x u)
include hs hf he
lemma cost (h:School C k u): School C' k (fun x : (V→ℝ)×X=> T x.2 (fun y=> u (x.1,y))):= by
 induction h with
 | one L h f hF =>
    convert School.one L h _ (he _ hF) using 1; ext1 x; exact hf _ hF (view x.1 L) x.2
 | @graft u v h h' a b=>
    convert a.graft b using 1; ext1 x; exact hs _ _ (knows h x.1) (knows h' x.1) x.2
end average
end School
end Drawer
end YM.QuadraticLocal.Aperture
