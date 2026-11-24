import YM.WilsonCoeffUV.Stable.CostKme
/-!
# Tested coefficient family

Era uses evaluated profiles with a single physical center, support relative to
capture/reference; permits amplitude vectors, explicitly retaining evaluation
at the SAME center of all factors. Careful: not claiming arbitrary sup-multi
estimated by sup-center products (when using separation gains).
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Exterior Next.Free Tree Precision Power Embroider Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm Fountain PathCost Embroider.Canvas Shard PowerSeries
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n c:Side}{U α β V W E W' ι : Type*}{r h D k j l m e i:ℕ} {A:ℝ}{G:Gauge}

section
variable [NormedAddCommGroup V][NormedSpace ℝ V][NormedAddCommGroup W][NormedSpace ℝ W]

def ply (T:V→ₗ[ℝ]W) : Pal V U →ₗ[ℝ]Pal W U:= LinearMap.pi fun i=> (cloaks T).comp (LinearMap.proj i)
@[simp] lemma ply_v (T:V→ₗ[ℝ]W)(P:Pal V U)(i j v) : ply T P i j v= T (P i j v):=rfl
lemma ply_shell (T:V→ₗ[ℝ]W){P:Pal V U}(h:shellK k P): shellK k (ply T P):=fun i j u=>funext fun v=>by rw [ply_v,h i j u]; exact map_zero T
lemma ply_pure (T:V→ₗ[ℝ]W){P:Pal V U}(p:Pure (P i)): Pure (ply T P i):=fun r u v=> congr_arg T (p r u v)

-- coefficientwise linear probing suffices
abbrev Parcelized (x:Type*)(G:Gauge)(n:Side):= Pal x (Woods G n)
abbrev Bookend (x:Type*)(G:Gauge):= Pal x (YForest G)
abbrev Era (G:Gauge)(V:Type*):=((n:Side)→ Parcelized V G n) × Bookend V G
variable {P:Era G V}
def Cert (X: Parcelized V G n): Prop:=∀ t : V→ₗ[ℝ]ℝ,rollTest (flash (ply t X)) (flash (ply t X)) 1 0
structure Auth (k:ℕ)(P: Era G V):Prop where
    wing : ∀ i r,Bends 0 (fun n=>P.1 n i r) (P.2 i r)
    span : ∀ n,shellK k (P.1 n)
    pale : ∀ n i,Pure (P.1 n i)
    token : ∀ n,Cert (P.1 n)
lemma Auth.tall (h:Auth k P)(p:k≤l):Auth l P:=⟨h.wing,fun i e j hv=> h.span i e j (by omega),h.pale,h.token⟩
lemma Auth.ext {Q:Era G V}(h:Auth k P)(p:Auth l Q)(e:P.1=Q.1): P=Q:=Prod.ext e (funext fun i=>funext fun r=> (show P.2 i r=Q.2 i r from ((h.wing ..).congr (Eventually.of_forall fun n=> congr_fun (congr_fun (congr_fun e n) _) _)).exten (p.wing ..)))
def tuftV (T : V→L[ℝ]W) (P:Era G V): Era G W:= (fun n=> ply T.toLinearMap (P.1 n), ply T.toLinearMap P.2)
lemma Auth.tuft (h:Auth k P)(T: V→L[ℝ]W): Auth k (tuftV T P):=⟨fun i r=>(h.wing i r).touch T,fun i=> ply_shell _ (h.span i),fun i j=>ply_pure _ (h.pale i j),fun n t {_} _ _ _ _ e=> h.token n (t.comp T.toLinearMap) e⟩
-- foot basis: express each coefficient of a history train as a linear probe on V
lemma cup_coefficient [Fintype α] [Fintype W'] {X:Pal V α}(p:shellK k X)(v:α→ Ink W')(M:ℕ)(m:W'→₀ℕ) : ∃ a:V,∀ T:V→ₗ[ℝ]ℝ,MvPolynomial.coeff m (coeff M (train v (flash (ply T X))))= T a:=by
    let K:POL α→ₐ[ℝ]Ink W' :=(MvPolynomial.aeval v); let Φ (j:ℕ)(B:POL α) :ℝ := MvPolynomial.coeff m (coeff M ((K B)*PowerSeries.X^j))
    let L (j):POL α→ₗ[ℝ]ℝ := {
        toFun:=Φ j
        map_add' x y:=by simp [Φ,map_add,add_mul]
        map_smul' c x:=by simp [Φ,map_smul] }
    let A j (r:ℕ)(x:Fin r→α):ℝ:= L j (∏ i,MvPolynomial.X (x i)); let B j:= Finset.range (k+j+1); let S:= Finset.range (M+1)
    refine ⟨∑ j∈S,∑ r∈B j,∑ x:Fin r→α,A j r x • X j r x,?_⟩; intro T
    rw [train,edit_coeff _ _ _ (Nat.lt_succ_self M),map_sum,MvPolynomial.coeff_sum,map_sum]; apply Finset.sum_congr rfl; intro i _; rw [flash,coeff_mk]; change L i (totalR (ply T X i))=_
    have hs: still (ply T X i) (k+i+1):= fun j hj=> ply_shell T p i j hj
    rw [visible hs,map_sum,map_sum]; refine Finset.sum_congr rfl (fun j _=>?_); rw [paint,palm_form,map_sum,map_sum]; exact Finset.sum_congr rfl (fun x _=>by rw [map_smul,map_smul,ply_v]; exact mul_comm ..)
lemma certify (samples:ι→ V→ₗ[ℝ]ℝ)(hp:∀ x y:V,(∀ i,samples i x=samples i y)→x=y)(X: Parcelized V G n)(p:shellK k X)(z:∀ i,rollTest (flash (ply (samples i) X)) (flash (ply (samples i) X)) 1 0): Cert X:=by
   intro t Z I a T T' H; ext1 j; apply MvPolynomial.ext; intro m; obtain ⟨A,hA⟩:= cup_coefficient p (spool T) j m; obtain ⟨B,hB⟩:= cup_coefficient p (spool T') j m; rw [hA,hB]; exact congr_arg t (hp A B (fun i=> by rw [←hA, ←hB, z i H]))

lemma On_auth {P:TowerS G D}(p:On k P): Auth k P:=by
   refine ⟨p.shore,p.launch,p.evenS,fun i=>?_⟩; refine certify (fun x : Volume D=> ((ContinuousLinearMap.apply ℝ ℝ) x).toLinearMap) (fun _ _ h=> DFunLike.ext _ _ (fun x=> h x)) _ (p.launch i) ?_
   intro x Z I a T T' H; have hp:= p.oneS i x H; rw [Soil.anchor] at hp; exact hp
lemma Auth_on {P:TowerS G D}(p:Auth k P): On k P:=⟨p.wing,p.span,p.pale,fun i t {_} _ _ _ _ h=>by rw [Soil.anchor]; exact p.token i (((ContinuousLinearMap.apply ℝ ℝ) t).toLinearMap) h⟩
lemma Auth.μ (p:Auth k P)(c:ℝ): Auth k (c•P):=by
    refine ⟨fun i j=>(p.wing i j).μ c,fun i=> mu_shellG (p.span i) c,fun i j v=>(p.pale i j v).smul _,fun n t {_} _ _ _ _ H=>?_⟩; rw [Prod.smul_fst,Pi.smul_apply,map_smul,flash_mu c (ply_shell _ (p.span n)),train_smul,train_smul,p.token n t H]
lemma Auth.sum {P:ι→ Era G V}{S:Finset ι}(p:∀ i∈S,Auth k (P i)):Auth k (∑ i∈S,P i):=by
    refine ⟨fun i r=>?_,fun i=>?_,fun i j r=>?_,fun n t {_} _ _ _ _ h=>?_⟩
    · simp_rw [Prod.snd_sum,Prod.fst_sum,Finset.sum_apply]; exact anzas S (fun i hi=> (p i hi).wing ..)
    · rw [Prod.fst_sum,Finset.sum_apply]; exact shelf (fun i hi=>(p i hi).span _)
    · rw [Prod.fst_sum,Finset.sum_apply,Finset.sum_apply,Finset.sum_apply]; exact Blue.Smooth.sum (fun i hi=> (p i hi).pale _ _ _)
    rw [Prod.fst_sum,Finset.sum_apply,map_sum,flash_term S (fun i hi=> ply_shell _ ((p i hi).span n)),map_sum,map_sum]; exact Finset.sum_congr rfl fun i hi=>(p i hi).token n t h
lemma Auth.add {Q:Era G V}(p:Auth k P)(q:Auth k Q):Auth k (P+Q):= by
    have h: ∀ i∈ Finset.univ,Auth k (![P,Q] i):=by intro i _; fin_cases i; exact p; exact q
    simpa [Fin.sum_univ_succ] using Auth.sum h
lemma Auth.sub {Q:Era G V}(p:Auth k P)(q:Auth k Q):Auth k (P-Q):= by rw [sub_eq_add_neg,← neg_one_smul ℝ]; exact p.add (q.μ _)
end
end YM.WilsonCoeffUV.Mer
