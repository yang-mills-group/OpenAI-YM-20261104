import YM.SignedWilsonExpansion.F9.Porch
/-!
# For every order, equivalence of the receive etude modulo this program's equations

`SameV`: under **all** spectators outside BOTH patch and mirror, not at coincidence.
Uses projectively accurate through matrices on actual `Stove`. The resulting
finite coincidences of endpoints can be used in the credit argument on the
same filiation. There is no separate match operation on predictions here.
-/
set_option autoImplicit false
set_option maxHeartbeats 720000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa.StationA
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Matrix
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos PathCost FVA2
open Cloth XSpace
open PertExtension PertExtension.Orb FormalOPE FormalOPE.RG10 FormalOPE.RG10.InversionWard
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical ENNReal InnerProductSpace
variable {G:Gauge}{H:Hol G}{h i j k a m r d n l:ℕ}{F:Frame G h}{x:Label G h}{P:Period} {s:Side} {ι:Type*}
section test
variable (T:P.Tree)(x:P.Sites)(b:ℕ)
local notation "Σ'"=> Bare.Series T G
structure SameV (x:P.Sites)(b:ℕ)(A B:Bare.Series T G): Prop where
    tests (i:ℕ) (v:Config G P.side→ℝ) (Y:Bare.Series T G): X^i*Y=BareOrb.stencil T v → Proxy v → respects v → ContDiff ℝ ω (v∘ T.links) → LocalOn ↑(away x b) v → Bare.normalized T G (A*Y)= Bare.normalized T G (B*Y)
inductive Aid : Bare.Series T G→Prop where
    | fromP (Y:Bare.Series T G)(i:ℕ)(v:Config G P.side→ℝ) (p:X^i*Y=BareOrb.stencil T v)(q: Proxy v)(u:respects v)(vL:ContDiff ℝ ω (v∘ T.links))(z:LocalOn ↑(away x b) v) : Aid Y
    | nil : Aid 0
    | plus : ∀{A B}, Aid A→ Aid B→ Aid (A+B)
    | multiple : ∀ {A:Bare.Series T G}, ∀ c:PowerSeries ℂ, Aid A→ Aid (Bare.scalar T c*A)
variable {T x b}{A B E U Y V:Bare.Series T G}
lemma real_scalar_eq (v:ℝ)(A:Bare.Series T G): (Complex.ofReal v) • A=v • A:=by rw [show Complex.ofReal v=v • (1:ℂ) from by simp [Complex.real_smul]]; rw [smul_assoc,one_smul]
namespace SameV
lemma gift : SameV T x b A A:= ⟨fun _ _ _ _ _ _ _ _=> rfl⟩
lemma binds (p:SameV T x b A B)(q:SameV T x b B U): SameV T x b A U:= ⟨fun _ _ _ v w t z u=>(p.tests _ _ _ v w t z u).trans (q.tests _ _ _ v w t z u)⟩
lemma turns (p:SameV T x b A B): SameV T x b B A:= ⟨fun _ _ _ v w t z u=>(p.tests _ _ _ v w t z u).symm⟩
lemma plus (p:SameV T x b A B)(q:SameV T x b Y U): SameV T x b (A+Y) (B+U):= ⟨fun i v Y w t z j k=>by rw [add_mul, add_mul,map_add,map_add,p.tests _ _ _ w t z j k,q.tests _ _ _ w t z j k]⟩
lemma multiple (p:SameV T x b A B)(V:PowerSeries ℂ): SameV T x b (Bare.scalar T V*A) (Bare.scalar T V*B):=⟨fun i v Y w t z j k=>by rw [mul_assoc,mul_assoc,Bare.normalized_scalar,Bare.normalized_scalar,p.tests _ _ _ w t z j k]⟩
lemma self_power (T:P.Tree)(G:Gauge)(q:ℂ): Bare.scalar T (G:=G) (PowerSeries.C q)=algebraMap ℂ (Bare.Series T G) q:=by unfold Bare.scalar; rw [PowerSeries.map_C, PowerSeries.algebraMap_apply]
lemma fee (p:SameV T x b A B)(v:ℂ): SameV T x b (v • A) (v • B):=by
    simpa only [self_power,Algebra.smul_def] using p.multiple (PowerSeries.C v)
lemma real_fee (p:SameV T x b A B)(v:ℝ): SameV T x b (v • A) (v • B):= by
    simpa only [real_scalar_eq] using p.fee (v:ℂ)
lemma sumP {A B:ι→Σ'}{S:Finset ι}(h:∀ i∈S, SameV T x b (A i) (B i)): SameV T x b (∑ i∈S,A i) (∑ i∈S,B i):=by
    induction S using Finset.induction_on with
    | empty=> rw [Finset.sum_empty,Finset.sum_empty]; exact gift
    | @insert i s p ih=> rw [Finset.sum_insert p,Finset.sum_insert p]; exact (h i (Finset.mem_insert_self ..)).plus (ih fun i hi=> h i (Finset.mem_insert_of_mem hi))
lemma covering (p:SameV T x b A B)(u:b≤ m):SameV T x m A B:= ⟨fun _ _ _ v w t z h=> p.tests _ _ _ v w t z (fun _ _ hz=> h _ _ (agrees_mono hz (Finset.coe_subset.mpr (away_tiny u))))⟩ -- order? Need LocalOn away_b from LocalOn away_m; bigger set (away_b); yes
lemma pairs (p: SameV T x b A B)(q: Aid T x b Y): Bare.normalized T G (A*Y)=Bare.normalized T G (B*Y):=by
   induction q with
   | fromP V v Z hp hq t he hz => exact p.tests _ _ _ hp hq t he hz
   | nil => simp only [mul_zero,map_zero]
   | plus a b ha hb=> rw [mul_add,mul_add,map_add,map_add,ha,hb]
   | multiple c v h=> rw [mul_left_comm A,mul_left_comm B,Bare.normalized_scalar, Bare.normalized_scalar,h]
end SameV
namespace Aid
lemma mul (p:Aid T x b A)(q:Aid T x b B): Aid T x b (A*B):=by
   induction p with
   | fromP F i v hp hq hv ht hP =>
      induction q with
      | fromP V k z hy he hw hz hV =>
         refine Aid.fromP _ (i+k) (v*z) ?_ (hq.mul he) (fun _ h U=> congr_arg₂ (·*·) (hv _ h U) (hw _ h U)) (ht.mul hz) (fun _ _ h=> congr_arg₂ (·*·) (hP _ _ h) (hV _ _ h))
         rw [mergeBook T ht hz,← hp,← hy,pow_add]; ring
      | nil=> rw [mul_zero]; exact nil
      | plus p q a b=> rw [mul_add]; exact plus a b
      | multiple c p h=> rw [mul_left_comm]; exact multiple c h
   | nil=> rw [zero_mul]; exact nil
   | plus p q a h=> rw [add_mul]; exact plus a h
   | multiple c p h=> rw [mul_assoc]; exact multiple c h
lemma unit : Aid T x b (1:Bare.Series T G):=by
    refine Aid.fromP _ 0 1 ?_ (Proxy.const _) (fun _ _ _=>rfl) contDiff_const (fun _ _ _=>rfl)
    unfold BareOrb.stencil TreeFormal.enter; rw [pow_zero,one_mul]; change 1= XSpace.Taylor.expandTaylor (T.basis G) (fun _=> (↑(1:ℝ):ℂ)); rw [XSpace.Taylor.expand_const]; simp
lemma scalar (p:Aid T x b A)(v:ℂ): Aid T x b (v • A):=by rw [Algebra.smul_def, ← SameV.self_power T G v]; exact multiple _ p
lemma fee (p:Aid T x b A)(v:ℝ): Aid T x b (v • A):= by simpa only [real_scalar_eq] using p.scalar (v:ℂ)
lemma purse (p:Aid T x b A)(n:ℕ): Aid T x b (PowerSeries.X^n*A):=by
   rw [show (PowerSeries.X^n:Bare.Series T G)=Bare.scalar T (PowerSeries.X^n) from by simp [Bare.scalar]]; exact p.multiple _ -- parameter order
lemma advances (p:b≤m) (h:Aid T x m A): Aid T x b A := by
    induction h with
    | fromP K i v he hu hv ht hr=> exact fromP _ _ _ he hu hv ht (fun _ _ h=> hr _ _ (agrees_mono h (Finset.coe_subset.mpr (away_tiny p))))
    | nil=> exact nil
    | plus _ _ h h'=> exact plus h h'
    | multiple _ _ h=> exact multiple _ h
lemma purchases {Y:ι→ Bare.Series T G}{S:Finset ι}(p:∀ i∈S,Aid T x b (Y i)): Aid T x b (∑ i∈S,Y i):=by
   induction S using Finset.induction_on with
   | empty=> rw [Finset.sum_empty]; exact nil
   | @insert i s h ih=> rw [Finset.sum_insert h]; exact plus (p i (Finset.mem_insert_self ..)) (ih fun i hi=> p i (Finset.mem_insert_of_mem hi))
lemma stamp (x: Pill G)(y z:P.Sites){S:Finset Cover}(v:LocalOn ↑S x.f)(p:b+cord S<separation y z)(q:b+cord S < separation y (-z)): Aid T z b (propose T y x):=
    fromP _ _ _ (apex T y x) (proxy _ x.valid) (respect x y) (flies T x.valid y) (fun U V ht=> by apply LocalOn.expandAt ↑S x.f v y; refine agrees_mono ht ?_; rw [show (fun p=>wrap P.side p+y) '' ↑S=(footprint S y: Set _) from by simp [footprint]]; exact Finset.coe_subset.mpr (vision S z y b p q))
-- apply before going to period F9. Absolute width in *lattice units*
lemma leased (v:Cloth G k): ∃ B:ℕ,∀(P:Period)(T:P.Tree)(y z:P.Sites)(b:ℕ), b+B<separation y z→b+B<separation y (-z)→Aid T z b (requesting T y k v):=by
    apply Cloth.recCloth v ?_ ?_; · exact ⟨0,fun P T y z b p q=> by rw [map_zero]; exact nil⟩
    rintro V a h n c ⟨B,hB⟩
    obtain ⟨S,H⟩:= a.valid.cover; refine ⟨max B (cord S), fun P T y z b p q=>?_⟩; rw [map_add,map_smul, request_card]; exact plus (hB P T y z b (by omega) (by omega)) (fee (purse (stamp a y z H (by omega) (by omega)) n) c)
end Aid
end test
end YM.WilsonCoeffUV.Mer.Xa.StationA
