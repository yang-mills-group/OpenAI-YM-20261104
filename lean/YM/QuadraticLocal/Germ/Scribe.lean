import YM.QuadraticLocal.Germ.Stock
import YM.RG.Push
/-!
# qlocal passive budget extensions
 ℓ independent slot revenue χ. Study over physical complex tests, through REAL projection.
 No integrability with unjustified ``inactive T`` inferred from budgets. May extend `Test.In`
 outside wallets as well. Only test attachment/continuation.Old flags all U even after projection.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.ModeWeight
open Function Filter Finset Lattice Wilson RG Marker MeasureTheory
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {V:Type}[DecidableEq V]{R:Census V}
-- useful even for zero w to isolate exact words
variable (R : Census V) (w:V→ℂ)
def entry : Poly R→ Poly R:= fun x=> Poly.inject fun q=> (∏ i∈q.val,w i)* x.part q
def paperKnob : Poly R→ₗ[ℂ] Poly R where
   toFun := entry R w
   map_add' x y:= by ext i; exact mul_add ..
   map_smul' := fun t y=> by ext i; exact mul_left_comm ..
def turn := (LinearMap.toContinuousLinearMap (paperKnob R w))
lemma scale (x:Poly R) (i:R.Mode): (turn R w x).part i = (∏ j∈i.val,w j)* x.part i:= rfl
lemma rum (x y:Poly R) : turn R w (x*y)=turn R w x*turn R w y:=by
   ext i; rw [scale,Poly.part_mul,Poly.part_mul,mul_sum]; refine sum_congr rfl fun j _=> ?_
   rw [mul_sum]; refine sum_congr rfl fun k _=>?_
   split
   next h=> rw [← h.2, Finset.prod_union h.1,scale,scale]; ring
   next=> exact mul_zero _
lemma roll : turn R w 1=1:=by
  ext i; rw [scale,Poly.one_part]; split; next h=> subst i; simp [Census.quiet]
  next=>exact mul_zero _
private lemma commutes (a:ℂ): turn R w ((algebraMap ℂ (Poly R)) a)=(algebraMap ℂ (Poly R)) a:=by
   simpa [Algebra.algebraMap_eq_smul_one,roll] using (map_smul (turn R w) a (1:Poly R))

def alg : Poly R→ₐ[ℂ] Poly R:={ (turn R w).toLinearMap.toAddMonoidHom with map_one':=roll R w, map_mul':=rum R w, commutes':=commutes R w }
lemma send (q:R.Mode) (x:ℂ): turn R w (Poly.send q x)= Poly.send q ((∏ i∈q.val,w i)*x):=by
    ext t; rw [scale,Poly.part_send,Poly.part_send]; by_cases h:t=q; · rw [h]; simp
    simp [h]
lemma mult {I:Type*}(s:Finset I)(x:I→Poly R): turn R w (∏ i∈s,x i)=∏ i∈s,turn R w (x i):=map_prod (alg R w) ..
lemma pass [Fintype V](x:Poly R): turn R w (Poly.pass x)=Poly.pass (turn R w x):= by
   unfold Poly.pass; rw [map_sum]; apply sum_congr rfl; intro j _; rw [map_smul,show turn R w (x ^ j) = _ from map_pow (alg R w) x j]; rfl -- check
variable {G:Gauge}{n c:Side} {T:Type*}{a:ℝ}
variable {S:StepData c n}
lemma advance [Fintype V] (p:Poly R→L[ℝ] Poly R)
    (F:Config G n→ Poly R)(h: S.IsKernel a G)(hp:Integrable F (prior G n)):
    p∘ S.push a F=S.push a (p∘ F):=by
   funext v; have he:= S.push_slice h v _ hp; unfold StepData.push; rw [Function.comp_apply,← p.integral_comp_comm he]; refine integral_congr_ae (ae_of_all _ fun x=> p.map_smul ..)
-- test α, Learn.K Ext carrying arbitrary K bits.
end YM.QuadraticLocal.ModeWeight

namespace YM.QuadraticLocal.Affinity
open Function Filter Finset Lattice Wilson RG Marker MeasureTheory
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {V : Type} [DecidableEq V] {R : Census V}
variable {E:V→Type*} [∀ i, AddCommGroup (E i)]
variable {Q : Type}[RCLike Q] [∀ i, Module Q (E i)] [NormedAlgebra Q ℂ]
variable (K: ∀ i, Submodule Q (E i))(A:∀ i,Set (E i))
open RG3.Held
-- variables for entire test extension. Domain modules need no norms; Budget itself on independent-height can use `Bill 1` sets from interface.
abbrev Full : Type _ := ∀ i, E i -- uses implicit E, add binder
def readH {T T':Type*} {G:Gauge}{n:Side}{P:Rep G n}{I:Type*}{o:V→Site n}(L:Gallery T I o P R)(g:T'→T): Gallery T' I o P R:= ⟨L.E.pullback g,L.K.pullback g⟩
local notation "W"=> Wallet A
local notation "T"=> Full (E:=E)
variable {s:Finset V}
-- include ℂ restriction set of test-horizon kernel
structure Eligible (s: Finset V) (F: (∀ i,E i) →ℂ): Prop where
   full : Letter Q E s F
   hollow (i:V) : i∈s → ∀ t,t i∈K i → F t=0
namespace Eligible
-- Radius grant: tests in A, extends ℝ-algebraic ModeKnob only. Calling with positive UNIT fixed. Doesn't imply complexity of decline lease budget.A.Grain
variable {K} {F G:(∀ i,E i)→ℂ}
lemma restrict (h:Eligible K s F): Attn K A s fun v=>F (readBack A v):=by
   refine ⟨fun t v he=> h.full.stay _ _ fun i hi=> congr_arg Subtype.val (he i hi),fun i hi t x y z a b hv=>?_,fun i hi t hv=> h.hollow i hi _ hv⟩
   rw [atCoord, atCoord, atCoord, hv, h.full.join _ i hi,h.full.scale _ i hi,h.full.scale _ i hi]
-- ambient conveniences
variable {A}
lemma silent : Eligible K s fun _=>0:= ⟨Letter.still,fun _ _ _ _=>rfl⟩
lemma quiet (v:ℂ): Eligible K ∅ fun _=>v:= ⟨Letter.const v, fun _ hi=> by simp at hi⟩
lemma linear (h:Eligible K s F)(L:ℂ→ₗ[Q] ℂ): Eligible K s (fun t=>L (F t)):=⟨h.full.linear L,fun i hi t ht=> by rw [h.hollow i hi t ht,map_zero]⟩
lemma cs (a:ℂ)(h:Eligible K s F): Eligible K s (fun t=> a*F t):=h.linear (Algebra.lmul Q ℂ a)
lemma plus (h: Eligible K s F)(hg:Eligible K s G): Eligible K s (fun t=> F t+G t):=⟨h.full.add hg.full, fun i hi t ht=>by rw [h.hollow i hi t ht,hg.hollow i hi t ht, add_zero]⟩
-- hom weighted by every i using algebra Q. Efficiency count only at FINTYPES.
lemma rescales (p:∀ i,E i)(t:V→Q) (h:Eligible K s F): F (fun i=> t i • p i)=(∏ i∈s,t i) • F p:= by
   -- adapted Laminate.on norm
   let U (a:Finset V) := piecewise a (fun i=> t i • p i) p
   have hu (a:Finset V) (hA:a⊆s): F (U a)=(∏ i∈a,t i) • F p:= by
      induction a using Finset.induction with
      | empty=> simp [U]
      | insert i a hi ih=>
         rw [show U (insert i a)=Function.update (U a) i (t i • p i) from funext fun x=> by by_cases he:x=i; subst x; simp [U]; simp [U,he]]
         have hz : Function.update (U a) i (p i)=U a:= by rw [← show U a i=p i from piecewise_eq_of_notMem _ _ _ hi,Function.update_eq_self]
         rw [h.full.scale _ i (hA (mem_insert_self ..)), hz, ih ((subset_insert ..).trans hA), prod_insert hi,mul_smul]
   rw [h.full.stay (fun i=> t i • p i) (U s) (fun i hi=>Eq.symm (piecewise_eq_of_mem _ _ _ hi)),hu s (Subset.refl _)]
lemma sees (h:Eligible K s F) (u v:∀ i,E i) (hJ:∀ i∈s,u i-v i∈K i) : F u=F v:=by
    let t (a:Finset V): Π i,E i:=piecewise a u v
    have hh(a:Finset V)(ha:a⊆s):F (t a)=F v:=by
       induction a using Finset.induction with
       | empty=>simp [t]
       | insert i a hi he=>
          let p:=t a; have hT:Function.update p i (v i)=p:=by rw [← show p i=v i from piecewise_eq_of_notMem _ _ _ hi,Function.update_eq_self]
          have hv:i∈s:= ha (mem_insert_self ..); rw [show t (insert i a)=Function.update p i ((u i-v i)+v i) from funext fun j=> by by_cases hj:j=i; subst j; simp [t]; simp [t,p,hj], h.full.join _ i hv, hT, h.hollow i hv _ (by rw [Function.update_self]; exact hJ i hv),zero_add]; exact he ((subset_insert ..).trans ha)
    exact (h.full.stay u (t s) (fun i hi=> (piecewise_eq_of_mem s u v hi).symm)).trans (hh s (Subset.refl _))
end Eligible
-- arbitrary scale not necessarily sign/monotone; use ℝ extension for price budgets.E.
structure Spring (Q:Type)[RCLike Q] [∀ i,Module Q (E i)] (A:∀ i,Set (E i)) where
   rate : ∀ i:V, E i→ Q
   nonzero i x : rate i x≠0
   level i x : x∈A i → rate i x=1
   accepts i x : (rate i x)⁻¹ • x∈A i
namespace Spring
variable {A K}
variable (Y:Spring Q A)
def tune (i:V)(x:E i): A i:= ⟨(Y.rate i x)⁻¹•x,Y.accepts i x⟩
def profile (x:Π i,E i) : Wallet A:= fun i=> Y.tune _ (x i)
lemma suited (x:Wallet A): Y.profile (readBack A x)=x:=funext fun i=> Subtype.ext (by unfold readBack profile tune; simp only [level Y i _ (x i).prop,inv_one,one_smul])
lemma acclaim (x:Π i,E i) : (fun i=> Y.rate i (x i) • (Y.profile x i).val)=x:= by funext i; unfold profile tune; simp [Y.nonzero]
lemma update (x:Π i,E i)(i:V)(z:E i): Y.profile (Function.update x i z)=Function.update (Y.profile x) i (Y.tune _ z):= by funext j; by_cases h:j=i; subst j; simp only [profile,Function.update_self]; simp only [profile,Function.update_of_ne h]
variable {F:Wallet A →ℂ} {G :(∀ i,E i)→ℂ}
def heft (s: Finset V)(x:Π i,E i):Q:= ∏ i∈s,Y.rate i (x i)
def issue (s:Finset V)(F:Wallet A→ℂ)(x:Π i,E i):ℂ:= Y.heft s x • F (Y.profile x)
lemma stay (x:Wallet A): Y.issue s F (readBack A x)= F x:= by
   unfold issue; rw [Y.suited]; unfold heft readBack; rw [Finset.prod_eq_one (fun i _=>Y.level i _ (x i).prop),one_smul]
lemma determines (h: Eligible K s G): Y.issue s (fun t=>G (readBack A t))=G:=by
   funext t; have hz:= h.rescales (readBack A (Y.profile t)) (fun i=> Y.rate i (t i)); exact hz.symm.trans (congr_arg G (acclaim Y t))
-- ledger Lane labels only, using Attn ⇒ Eligible, interior smoothness local is still supplied separately.
lemma recoil (x:Π i,E i)(i:V)(hi:i∈s)(z:E i): Y.heft s (Function.update x i z)= Y.rate i z * Y.heft (s.erase i) x:=by
   unfold heft; rw [← Finset.mul_prod_erase _ _ hi,Function.update_self]; apply congr_arg; refine Finset.prod_congr rfl (fun j hj=>?_); rw [Function.update_of_ne (ne_of_mem_erase hj)]
lemma immersive (h:Attn K A s F)(x: Π i,E i)(i:V)(hi:i∈s)(b c:E i)(z y:Q):
   Y.issue s F (Function.update x i (z • b + y • c)) = z • Y.issue s F (Function.update x i b)+ y • Y.issue s F (Function.update x i c):=by
   let a:= z • b+y • c; let v:=Y.rate i a; let d:=Y.rate i b; let e:=Y.rate i c; let p:= z*d/v; let q:= y*e/v; let k:= Y.heft (s.erase i) x
   have hv:v ≠0:= Y.nonzero _ _; have hd:d ≠0:=Y.nonzero _ _; have he:e≠0:= Y.nonzero _ _
   have hh : (Y.tune i a).val= p • (Y.tune i b).val + q • (Y.tune i c).val := by
      change v⁻¹ • (z • b+y • c)= p • (d⁻¹ • b)+ q • (e⁻¹ • c); rw [smul_add,smul_smul,smul_smul,smul_smul,smul_smul,show v⁻¹ * z=p*d⁻¹ from Eq.symm (by unfold p;field_simp),show v⁻¹*y=q*e⁻¹ from Eq.symm (by unfold q;field_simp)]
   have hP : (v*k)*p=z*(d*k):=by unfold p; field_simp
   have hQ : (v*k)*q=y*(e*k):=by unfold q; field_simp
   unfold issue; rw [recoil Y x i hi,recoil Y x i hi,recoil Y x i hi,Y.update,Y.update,Y.update,h.turns i hi _ _ _ _ _ _ hh,smul_add, smul_smul,smul_smul,smul_smul,smul_smul,hP,hQ]
lemma extend (h:Attn K A s F): Eligible K s (Y.issue s F):=by
   refine ⟨⟨fun x y he=>?_, fun x i hi b c=>?_,fun x i hi b c=>?_⟩,fun i hi t ht=>?_⟩
   · exact congr_arg₂ (· • ·) (prod_congr rfl (fun i hi=>congr_arg (Y.rate i) (he i hi))) (h.sit (Y.profile x) (Y.profile y) (fun i hi=> congr_arg (Y.tune i) (he i hi)))
   · simpa only [one_smul] using immersive Y h x i hi b c 1 1
   · simpa only [zero_smul,add_zero] using immersive Y h x i hi c c b 0
   unfold issue; rw [h.idle i hi (Y.profile t) (Submodule.smul_mem (K i) _ ht),smul_zero]
end Spring
end YM.QuadraticLocal.Affinity
