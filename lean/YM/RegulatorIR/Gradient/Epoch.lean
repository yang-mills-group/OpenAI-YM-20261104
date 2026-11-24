import YM.RegulatorIR.Gradient.Line
import YM.RegulatorIR.Diagram.Drained

/-! Algebraic reading of homogeneous substitutions. All finite ranks. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Gradient
open Budget Budget.Layer Budget.Packet Budget.Tuple Budget.Tariff Train Uniform Diagram Function Finset PowerSeries
open scoped ENNReal Topology BigOperators Classical
variable {X Y : Type}{r:ℕ}

-- powerseries in scalar coupling, (actual) coefficients not derivatives
private lemma grades {M:Type} [CommRing M] (F:Fin r→PowerSeries M) (s):
    PowerSeries.coeff s (∏ i,F i)=∑ g∈ turns r s,∏ i,PowerSeries.coeff (g i) (F i):=by
 induction r generalizing s with
 | zero =>
     simp_rw [Fin.prod_univ_zero, PowerSeries.coeff_one]
     by_cases h:s=0
     · subst s; simp [turns,charge]
     rw [if_neg h]; simp [turns,charge,Ne.symm h]
 | succ r ih =>
    rw [Fin.prod_univ_succ,PowerSeries.coeff_mul]
    simp_rw [ih (fun i => F i.succ),Finset.mul_sum]
    -- bij from all turns to head-norm and tail distributions
    rw [Finset.sum_sigma' (antidiagonal s) (fun x=> turns r x.2) (fun x (v:Fin r→ℕ)=> (coeff x.1 (F 0)) * ∏ i,coeff (v i) (F i.succ))]
    let f (a : (_:ℕ×ℕ) × (Fin r→ℕ)) : Fin (r+1) → ℕ:= Fin.cons a.1.1 a.2
    have he (p:ℕ×ℕ)(x:Fin r→ℕ): charge (f ⟨p,x⟩) = p.1 + charge x:=by unfold f charge; rw [Fin.sum_univ_succ]; simp
    refine Finset.sum_bij (fun a _=> f a) ?_ ?_ ?_ ?_
    · rintro ⟨p,q⟩ h;rw [turns_iff,he,(turns_iff ..).mp (Finset.mem_sigma.mp h).2];exact mem_antidiagonal.mp (mem_sigma.mp h).1
    · rintro ⟨⟨i,p⟩,v⟩ h ⟨⟨j,q⟩,w⟩ hw hh
      have H:p=_:= ((turns_iff ..).mp (Finset.mem_sigma.mp h).2).symm; have hv:q=_:=((turns_iff ..).mp (Finset.mem_sigma.mp hw).2).symm
      have h':Tuple.glueEquiv ℕ r (i,v)=Tuple.glueEquiv ℕ r (j,w):=hh
      obtain ⟨rfl,rfl⟩:= Prod.mk.inj ((Tuple.glueEquiv ℕ r).injective h'); have : p=q:= by rw [H,hv]
      rw [this]
    · intro b hb; refine ⟨⟨(b 0,charge (Fin.tail b)),Fin.tail b⟩, Finset.mem_sigma.mpr ⟨?_,(turns_iff ..).mpr rfl⟩,Fin.cons_self_tail ..⟩
      apply Finset.mem_antidiagonal.mpr
      rw [← he (b 0,charge (Fin.tail b))]; rw [show f _=b from Fin.cons_self_tail ..]; exact (turns_iff ..).mp hb
    rintro ⟨p,q⟩ _; rw [Fin.prod_univ_succ]; simp [f]

variable [Fintype X][Fintype Y]

def related (Γ : Curve X Y) (x:X): PowerSeries (Jet Y) := PowerSeries.mk fun i=>render (Γ x i)

def alter (Γ:Curve X Y) : Jet X →ₐ[ℝ] PowerSeries (Jet Y):= MvPolynomial.aeval (related Γ)

omit [Fintype X] in
lemma split_product (Γ:Curve X Y) (p:Tuple X r) (g:Fin r→ℕ): render (tracked Γ g p) = ∏ i, render (Γ (p i) (g i)):=by
 unfold render
 rw [← (setting g Y).symm.sum_comp, Fintype.prod_sum]
 -- same positions reshuffled
 apply sum_congr rfl;intro z h
 rw [Train.tracked,Equiv.apply_symm_apply, Train.trips,map_prod, Finset.prod_mul_distrib]
 congr 1
 unfold word; rw [← (stations g).prod_comp, Fintype.prod_sigma]
 apply Finset.prod_congr rfl; intro i _; apply Finset.prod_congr rfl;intro j _
 congr 1; exact congr_fun (congr_fun ((setting g Y).apply_symm_apply z) i) j

lemma render_series (Γ:Curve X Y)(g:Fin r→ℕ)(T:Packet X r): render (cut Γ T (charge g) g)= ∑ x:Tuple X r,MvPolynomial.C (T x)*(∏ i, render (Γ (x i) (g i))):=by
 rw [cut, dif_pos rfl];change render (symmetry _)=_
 rw [render_symmetry];unfold render Train.series; simp_rw [tsum_fintype,map_sum,Finset.sum_mul]; rw [Finset.sum_comm]
 apply Finset.sum_congr rfl; intro i _
 change _ = MvPolynomial.C (T i)*(∏ j,render (Γ (i j) (g j)))
 rw [← show render (tracked Γ g i)= _ from split_product Γ i g]; unfold render; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _=> by rw [map_mul,mul_assoc]
lemma update_formula (Γ:Curve X Y)(T:Packet X r)(s): render (updateQ Γ T s)=PowerSeries.coeff s (alter Γ (render T)):=by
 have hp x : alter Γ (MvPolynomial.C (T x)*word x)= (T x) • (∏ i, related Γ (x i)):= by rw [map_mul]; simp_rw [alter,MvPolynomial.aeval_C,word,map_prod,MvPolynomial.aeval_X,Algebra.smul_def]
 rw [updateQ, render_sum, show alter Γ (render T)=∑ z:Tuple X r,(T z) • ∏ i,related Γ (z i) from by rw [render,map_sum]; exact sum_congr rfl fun i _=>hp _, map_sum]
 simp_rw [PowerSeries.coeff_smul,grades,Finset.smul_sum]; rw [Finset.sum_comm (t:=turns r s)]
 apply Finset.sum_congr rfl;intro i hi
 have hs:charge i=s:= (turns_iff ..).mp hi
 subst s; rw [render_series]; simp_rw [related,PowerSeries.coeff_mk,Algebra.smul_def]; rfl
end YM.RegulatorIR.Gradient
