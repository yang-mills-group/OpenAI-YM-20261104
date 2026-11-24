import YM.SignedWilsonExpansion.F9.Tape
/-!
# Complete formal Tape correlation with costs
- Commitment port mp .parchment in F9 larger P; same ∘ repetition for any finite mask.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Function Set Filter XSpace XSpace.Normalize PowerSeries FPS
open scoped BigOperators Topology ContDiff Classical Matrix
variable {E F: Type} [AddCommGroup E][Module ℂ E] [AddCommGroup F][Module ℂ F] {n:ℕ} {G:Gauge}{d:ℕ} {I:Type}
local notation "Ink"=> PowerSeries ℂ
namespace Tape
abbrev Table (E:Type)[AddCommGroup E][Module ℂ E](n:ℕ):= Tape (MultilinearMap ℂ (fun _:Fin n=> E) ℂ)
def archive (v:Table E n)(x: Fin n→ E): Ink:= mk fun n=> v n x
def tall (F:Table E n)(p:ℕ) : MultilinearMap ℂ (fun _:Fin n=> Tape E) ℂ:= ∑ i∈Normalize.tally p n,(F (i none)).compLinearMap (fun j=> LinearMap.proj (R:=ℂ) (φ:=fun _:ℕ=> E) (i (some j)))
def tabular (F:Table E n) : MultilinearMap ℂ (fun _:Fin n=> Tape E) Ink:= MultilinearMap.mk' (fun p=> mk fun i=> tall F i p) (by intro f i x y; apply PowerSeries.ext; intro n; rw [map_add,coeff_mk,coeff_mk,coeff_mk,MultilinearMap.map_update_add]) (by intro p i c x; apply PowerSeries.ext; intro n; rw [ PowerSeries.coeff_smul,coeff_mk,coeff_mk,MultilinearMap.map_update_smul ])
lemma tab_coeff (F:Table E n)(p:Fin n→ Tape E)(i:ℕ): coeff i (tabular F p)=∑ v∈ Normalize.tally i n, F (v none) (fun j=> p j (v (some j))):=by simp only [tabular,MultilinearMap.mk'_apply,coeff_mk]; unfold tall; rw [_root_.sum_apply]; rfl
lemma table_side (F:Table E n)(x:Fin n→E)(y:Fin n→ Ink): tabular F (fun i=>side (x i) (y i))=(∏ i,y i)*archive F x:=by
    let f (a:Option (Fin n)):= Option.elim a (archive F x) y; rw [mul_comm, show archive F x * (∏ i:Fin n,y i)=∏ a,f a from (by rw [Fintype.prod_option]; rfl)]
    apply PowerSeries.ext; intro i; rw [tab_coeff,coeff_prod]; apply Finset.sum_congr rfl; intro v hv; simp_rw [side_read]; rw [MultilinearMap.map_smul_univ,Fintype.prod_option]; change (∏ i: Fin n, coeff _ (y i)) * _= coeff _ (archive F x)* _; rw [mul_comm]; exact congr_arg (fun x:ℂ=> x* _ ) (coeff_mk (v none) (fun z=> F z x)).symm -- hm
lemma archives (F:Table E n)(p: Fin n→ E): tabular F (fun i=>side (p i) 1)=archive F p:=by rw [table_side];simp
/- evaluate *any* spectrum with full argument power.Avoid combinatorial reindex by finite basis. -/
lemma prices_ar [Fintype I] (F:Table E n)(p:Fin n→Tape E)(b:Module.Basis I ℂ E): tabular F p=∑ j:Fin n→I,(∏ i,nearC b (j i) (p i))*archive F (b ∘ j):=by
   -- nth only
   nth_rw 1 [show p=(fun i=> ∑ k, side (b k) (nearC b k (p i))) from funext fun i=> tabulated b _]; rw [MultilinearMap.map_sum]; exact Finset.sum_congr (by simp) (fun j _=> table_side F _ _)
lemma table_cost [FiniteDimensional ℂ E](F:Table E n)(p:Fin n→ Tape E)(x: Fin n→Ink) : tabular F (fun i=> starE (x i) (p i))=(∏ i,x i)*tabular F p:=by
   let b:= Module.finBasis ℂ E; rw [prices_ar F p b];
   conv_lhs => arg 2; intro i; rw [tabulated b (p i), map_sum]
   simp_rw [starE_side]
   rw [MultilinearMap.map_sum,Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; rw [table_side,Finset.prod_mul_distrib,mul_assoc]; rfl
lemma price_list [Fintype I][FiniteDimensional ℂ E](F:Table E n)(p:Fin n→ I→Tape E)(x:Fin n→ I → Ink): tabular F (fun i=> ∑ j,starE (x i j) (p i j))=∑ a:Fin n→I,(∏ i,x i (a i))*tabular F (fun i=> p i (a i)):=by rw [MultilinearMap.map_sum]; exact Finset.sum_congr (by simp) fun i _=>table_cost F _ _
-- position conversion
variable (D:Normalize.Guard G d)
variable (P: Table (Sec G d) n)
def horizon (D:Normalize.Guard G d) (F: Tape (MultilinearMap ℂ (fun _:Fin n=> Sec G d) ℂ)) (k:ℕ): MultilinearMap ℂ (fun _:Fin n=> Sec G d) ℂ := ∑ i∈Normalize.tally k n,(F (i none)).compLinearMap (fun j=> PowerSeries.coeff (i (some j)) D)
lemma horizon_spur (t:Fin n→Sec G d): archive (horizon D P) t=tabular P (fun i=>spur (facet D) (t i)):=by apply PowerSeries.ext; intro i; rw [archive,coeff_mk,tab_coeff]; unfold horizon; rw [_root_.sum_apply]; rfl
lemma layover (x:Fin n→Tape (Sec G d)) : tabular P (fun i=> respond (facet D) (x i))=tabular (horizon D P) x:=by
   let b:= Module.finBasis ℂ (Sec G d); rw [prices_ar _ x b]; conv_lhs=> arg 2; intro i; rw [tabulated b (x i),map_sum]
   simp_rw [respond_side]
   rw [price_list]; simp_rw [horizon_spur]
   rfl
-- cost ring of measure. We remember χ substitution and Jensen.W.W.C.
def composed (F:Table E n)(x: Ink)(p:ℕ) : MultilinearMap ℂ (fun _:Fin n=> E) ℂ:= ∑ i∈Finset.range (p+1), coeff p (x^i) • F i
lemma comp_clock (F:Table E n)(x: Ink)(h:constantCoeff x=0)(p:Fin n→ E): (archive F p).subst x= archive (composed F x) p:=by apply PowerSeries.ext; intro i; rw [FPS.coeff_substituted _ h, archive,archive,coeff_mk]; unfold composed; rw [_root_.sum_apply]; apply Finset.sum_congr rfl; intro j _; rw [coeff_mk,_root_.smul_apply,smul_eq_mul,smul_eq_mul,mul_comm]
lemma comp_tape [FiniteDimensional ℂ E](F:Table E n)(x:Ink)(h:constantCoeff x=0)(p:Fin n→ Tape E): (tabular F p).subst x=tabular (composed F x) (fun i=>tempo x (p i)):=by
   let L:Ink→ₐ[ℂ]Ink:= substAlgHom (HasSubst.of_constantCoeff_zero' h); rw [← show L _= (tabular F p).subst x from congr_fun (coe_substAlgHom _) _]; let b:=Module.finBasis ℂ E; rw [prices_ar F p b]; conv_rhs=> arg 2; intro i; rw [tabulated b (p i),map_sum]
   simp_rw [side_tempo h]
   rw [map_sum,MultilinearMap.map_sum]; apply Finset.sum_congr rfl; intro i _; rw [map_mul,map_prod]; let v:=b ∘ i; rw [table_side]; unfold L; rw [coe_substAlgHom]; exact congr_arg (fun c:Ink=> (∏ j,(nearC b (i j) (p j)).subst x)*c) (comp_clock F x h v)
lemma comp_cover (F:Table E n)(u v:Ink)(x:constantCoeff u=0)(y:constantCoeff v=0): composed (E:=E) (composed F u) v=composed F (u.subst v):=by
   have hh:constantCoeff (u.subst v)=0:=by rw [←coeff_zero_eq_constantCoeff_apply,FPS.coeff_substituted u y,zero_add,Finset.range_one,Finset.sum_singleton,coeff_zero_eq_constantCoeff_apply,x,zero_smul]
   funext i; ext k; exact (coeff_mk _ _).symm.trans <| (congr_arg (coeff i) (show archive (composed (E:=E) (composed F u) v) k= archive (composed F (u.subst v)) k from by rw [← comp_clock (composed F u) v y k,←comp_clock F u x k, ←comp_clock F (u.subst v) hh k,subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' x) (HasSubst.of_constantCoeff_zero' y)])).trans (coeff_mk ..)
lemma composed_id (F:Table E n): composed F X=F:=by
   funext j; ext1 v; have hv:=congr_arg (coeff j) (comp_clock F X (by simp) v); rw [X_subst] at hv; exact (coeff_mk _ _).symm.trans (hv.symm.trans (coeff_mk ..))
end Tape
end YM.WilsonCoeffUV.Mer.Xa
