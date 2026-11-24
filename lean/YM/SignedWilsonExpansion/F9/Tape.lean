import YM.XSpace.Playing
/-!
# Recall of coefficient arithmetic in correlating multiple offshell-series slots
Tape extensions to correlation adapted from `FVA2.ShowX.Read`. Use ℂ-series with proof of
real coefficients for action through motion whenever needed, all assertions a full formal PS (unless charged truncations).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Function Set Filter XSpace XSpace.Normalize PowerSeries FPS
open scoped BigOperators Topology ContDiff Classical Matrix
variable {E F: Type} [AddCommGroup E][Module ℂ E] [AddCommGroup F][Module ℂ F]
variable {I:Type}
abbrev Tape (E:Type):= ℕ→ E
local notation "Ink"=> PowerSeries ℂ
variable {x y:Ink}{d n:ℕ}
namespace Tape
/-! scalar arithmetic -/
abbrev pep (a:ℂ)(v:E): E:= a • v
def starE (x:Ink) : Module.End ℂ (Tape E) where
   toFun y k:= ∑ i∈Finset.antidiagonal k, pep (coeff i.1 x) (y i.2)
   map_add' x y:=by ext1 i; simp only [pep,Pi.add_apply,smul_add,Finset.sum_add_distrib]
   map_smul' c x:=by ext1 i; rw [Pi.smul_apply,Finset.smul_sum]; exact Finset.sum_congr rfl fun _ _=> smul_comm _ _ _
def side (v: E): Ink→ₗ[ℂ] Tape E where
   toFun x k:= pep (coeff k x) v
   map_add' x y:= funext fun i=> by simp only [map_add, Pi.add_apply,pep,add_smul]
   map_smul' c x:= funext fun i=> by simp only [map_smul,Pi.smul_apply,pep,smul_assoc,RingHom.id_apply]
lemma side_read (v:E)(x:Ink)(d:ℕ): side v x d=coeff d x • v:=rfl
lemma side_one (v:E): side v 1=Pi.single 0 v:=by funext i; rw [side_read, coeff_one]; by_cases h : i=0 <;> simp [h]
lemma starE_side (x y:Ink)(v:E): starE x (side v y)= side v (x*y):=by funext i; rw [side_read,coeff_mul,Finset.sum_smul]; simp only [starE, LinearMap.coe_mk, AddHom.coe_mk,pep,side_read,mul_smul]; try exact Finset.sum_congr rfl fun j _=>(mul_smul _ _ _).symm
lemma stars_left (x y:Ink)(P:Tape E): starE (x+y) P=starE x P+starE y P:=by ext1 i; simp only [starE,Pi.add_apply, LinearMap.coe_mk,AddHom.coe_mk,map_add,pep,add_smul, Finset.sum_add_distrib]
abbrev nearC (b:Module.Basis I ℂ E)(i:I): Tape E →ₗ[ℂ] Ink:=by
   exact { toFun:= fun x=> PowerSeries.mk fun n=> b.repr (x n) i, map_add':=fun x y=> PowerSeries.ext fun n=> by simp, map_smul':=fun c x=> PowerSeries.ext fun n=> by simp [coeff_smul] }
lemma nearC_pay (B:Module.Basis I ℂ E)(x:Tape E)(n:ℕ)(i): coeff n (nearC B i x)= B.repr (x n) i:=by simp [nearC]
lemma tabulated [Fintype I](B:Module.Basis I ℂ E)(x:Tape E): x=∑ i,side (B i) (nearC B i x):=by funext j; rw [Finset.sum_apply]; simp_rw [side_read,nearC_pay]; exact (B.sum_repr _).symm
lemma stars [FiniteDimensional ℂ E] (x y:Ink)(P:Tape E): starE x (starE y P)= starE (x*y) P:=by
    let B:= Module.finBasis ℂ E; rw [tabulated B P]; simp_rw [map_sum,starE_side,mul_assoc]
-- act with coupling under substitution (`Side`, left-carries)
def tempo (p:Ink): Tape E →ₗ[ℂ] Tape E where
   toFun z i:= ∑ j∈Finset.range (i+1), coeff i (p^j) • z j
   map_add' x y:=by ext1 i; simp only [Pi.add_apply,smul_add,Finset.sum_add_distrib]
   map_smul' c x:=by ext1 i; rw [Pi.smul_apply,Finset.smul_sum]; exact Finset.sum_congr rfl fun _ _=> smul_comm ..
lemma side_tempo (h:constantCoeff x=0)(y:Ink)(v:E): tempo x (side v y)=side v (y.subst x):=by
    funext i; rw [side_read,FPS.coeff_substituted _ h,Finset.sum_smul]; simp only [tempo, LinearMap.coe_mk, AddHom.coe_mk,side_read]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [smul_eq_mul,mul_smul]; exact smul_comm ..
lemma tempo_south [FiniteDimensional ℂ E](h:constantCoeff x=0)(p:Tape E)(y:Ink): tempo x (starE y p)=starE (y.subst x) (tempo x p):=by
   let B:=Module.finBasis ℂ E; rw [tabulated B p]; simp_rw [map_sum,starE_side,side_tempo h, subst_mul (HasSubst.of_constantCoeff_zero' h),starE_side] -- check order
lemma tempo_first (h:constantCoeff x=0)(p:Tape E): tempo x p 0=p 0:=by simp only [tempo,zero_add,Finset.range_one,LinearMap.coe_mk,AddHom.coe_mk]; rw [Finset.sum_singleton,pow_zero,coeff_one]; simp
lemma tempo_comp [FiniteDimensional ℂ E] (h:constantCoeff x=0)(g:constantCoeff y=0)(p:Tape E): tempo x (tempo y p)=tempo (y.subst x) p:=by
    have hh: constantCoeff (y.subst x)=0:=by rw [←coeff_zero_eq_constantCoeff_apply,FPS.coeff_substituted _ h,zero_add,Finset.range_one,Finset.sum_singleton,coeff_zero_eq_constantCoeff_apply,g,zero_smul]
    rw [tabulated (Module.finBasis ℂ E) p]; simp_rw [map_sum,side_tempo g,side_tempo h,side_tempo hh, subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' g) (HasSubst.of_constantCoeff_zero' h)]
lemma tempo_same [FiniteDimensional ℂ E](p:Tape E): tempo PowerSeries.X p=p:=by rw [tabulated (Module.finBasis ℂ E) p]; simp_rw [map_sum,side_tempo (show constantCoeff (PowerSeries.X:Ink)=0 from by simp),X_subst]
/-! pressure of formal field changes in all Papers -/
def layer (L:E→ₗ[ℂ]F): Tape E→ₗ[ℂ] Tape F where
   toFun x i:= L (x i)
   map_add' _ _:= funext fun _=> map_add ..
   map_smul' _ _:= funext fun _=> map_smul ..
def respond (A:Tape (E→ₗ[ℂ]F)): Tape E→ₗ[ℂ] Tape F where
   toFun x i:= ∑ j∈ Finset.antidiagonal i, A j.1 (x j.2)
   map_add' x y:= by funext i; simp only [Pi.add_apply,map_add,Finset.sum_add_distrib]; -- rfl?
   map_smul' c x:= by funext i; simp only [Pi.smul_apply,map_smul, Finset.smul_sum, RingHom.id_apply]
def facet (A:PowerSeries (Module.End ℂ E)): Tape (Module.End ℂ E):= fun i=> coeff i A
def spur (A:Tape (E→ₗ[ℂ]F))(x:E):Tape F:= fun i=> A i x
lemma respond_side (A:Tape (E→ₗ[ℂ]F))(x:Ink)(v:E): respond A (side v x)= starE x (spur A v):=by
    funext i; let K(n:ℕ×ℕ):= coeff n.2 x • A n.1 v; have h:∑ n∈Finset.antidiagonal i,K n=∑ n∈Finset.antidiagonal i,K n.swap:=by
       symm; exact Finset.Nat.sum_antidiagonal_swap (f:=K)
    unfold respond; simp_rw [LinearMap.coe_mk,AddHom.coe_mk,side_read,map_smul]; exact h
lemma response [FiniteDimensional ℂ E][FiniteDimensional ℂ F](A:Tape (E→ₗ[ℂ]F))(x:Ink)(p:Tape E): respond A (starE x p)= starE x (respond A p):=by
    rw [tabulated (Module.finBasis ℂ E) p]; simp_rw [map_sum,starE_side,respond_side,stars]
lemma tribute (A:PowerSeries (Module.End ℂ E))(x: E)(B:PowerSeries (Module.End ℂ E)): respond (facet A) (spur (facet B) x)=spur (facet (A*B)) x:=by
    funext i; unfold spur facet; rw [coeff_mul i A,LinearMap.sum_apply]; rfl
lemma star_one (f:Tape E): starE 1 f=f:=by
    funext i; change ∑ j∈ Finset.antidiagonal i, coeff j.1 (1:Ink) • f j.2=f i; rw [ Finset.sum_eq_single (0,i)]; simp; intro j hj h; rw [coeff_one,if_neg (show j.1≠0 from fun h'=> h (Prod.ext h' (by have u:=Finset.mem_antidiagonal.mp hj; omega))), zero_smul]; simp
lemma spur_early (v:E): spur (facet (1:PowerSeries (Module.End ℂ E))) v= side v 1:=by
   funext i; rw [side_read,coeff_one]; unfold spur facet; rw [coeff_one]; split_ifs; exact (one_smul _ _).symm; exact (zero_smul ..).symm
lemma respond_mul [FiniteDimensional ℂ E](A B:PowerSeries (Module.End ℂ E))(p:Tape E): respond (facet (A*B)) p=respond (facet A) (respond (facet B) p):=by
   rw [tabulated (Module.finBasis ℂ E) p]; simp_rw [map_sum,respond_side,response,tribute] -- need avoid recursive expansion
lemma respond_one [FiniteDimensional ℂ E](p:Tape E) : respond (facet (1:PowerSeries (Module.End ℂ E))) p=p:=by rw [tabulated (Module.finBasis ℂ E) p]; simp_rw [map_sum,respond_side,spur_early,starE_side,mul_one]
end Tape
end YM.WilsonCoeffUV.Mer.Xa
