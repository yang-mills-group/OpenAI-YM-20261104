import YM.RG06.Continuum.Reconstruct
import YM.RG06.Continuum.Grades
import YM.Next.FOUNDATIONS.LinkBounds
/-!
# Raw symbol to radial gauge variables: finite order truncation for nonlinear continuum jets
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.Continuum
namespace Raw
open Labels Tensor Lattice Analysis Wilson Function
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical InnerProductSpace
variable {G : Gauge}

lemma derivative_tensor (w:List Axis)(f:E4→G.Color)(v : Fin w.length → Axis)(h : v = w.get)(hf:Good f):
    derivative w f = fun x=>iteratedFDeriv ℝ w.length f x (basis ∘ v):=by
  subst v; exact (congrArg (fun l: List Axis=>derivative l f) (List.ofFn_get w).symm).trans ((deltaList w.length w.get f).symm.trans (dx _ _ _ hf)) -- need hf

lemma diagonal_calc (i:Axis)(d:ℕ)(J:Labels.Jet G)(j:ℕ)(h:j+2 ≤ d):
    Tensor.coeff (radField d J i) (j+1) (0:E4)= (J j).val i:=by
  let A:= radField d J i
  have hA : ContDiffAt ℝ ((j+1:ℕ):WithTop ℕ∞) A 0 := (ContDiff.contDiffAt (rad_smooth d J i)|>.of_le (WithTop.coe_le_coe.mpr le_top))
  apply Tensor.ext_diag
  · exact Tensor.coeff_symm hA
  · exact (J j).property.1 i
  funext z
  rw [show diagonal (coeff (radField d J i) (j+1) 0) z = ((j+1).factorial:ℝ)⁻¹ • iteratedDeriv (j+1) (fun t:ℝ=>radField d J i (t • z)) 0 from ?_]
  · unfold radField Source.potential; simp_rw [Taylor.value_hom]
    rw [iteratedDeriv_fun_sum (show ∀ (p:ℕ)(_h:p∈Finset.range (d-1)), ContDiffAt ℝ (↑(j+1:ℕ)) (fun t:ℝ=> t^(p+1) • (J p).value i z) 0 from fun _ _=> (contDiffAt_id.pow _).smul contDiffAt_const), Finset.sum_eq_single j]
    · rw [iteratedDeriv_smul_const, iteratedDeriv_fun_pow_zero,if_pos rfl,inv_smul_smul₀] -- arguments orientation
      all_goals first | rfl | exact contDiffAt_id.pow _ | positivity
    · intro a ha he; rw [iteratedDeriv_smul_const, iteratedDeriv_fun_pow_zero, if_neg (by omega), Nat.cast_zero,zero_smul]; exact contDiffAt_id.pow _
    intro he; rw [Finset.mem_range] at he; omega
  rw [YM.Next.Foundations.iteratedDeriv_on_line hA]; rfl

-- Produces every derivative convention consumers use through d without casts in a statement.
lemma order_eval (d:ℕ)(J:Labels.Jet G)(w:List Axis)(a b:Axis)(hd:w.length+2 ≤ d) :
    let k:=w.length
    let y : Fin (k+1)→ E4:=Fin.cons (basis a) (basis ∘ w.get)
    derivative (a::w) (radField d J b) 0=((k+1).factorial:ℝ) • (J k).val b y :=by
  intro k y
  have he := DFunLike.congr_fun (diagonal_calc b d J k hd) y
  rw [derivative_tensor (a::w) _ _ rfl (rad_smooth d J b)]
  have hx: (basis ∘ (a::w).get)= y:=by
    funext i; refine Fin.cases ?_ (fun j=>?_) i
    all_goals simp [k,y,Function.comp]
  rw [hx]
  change iteratedFDeriv ℝ (k+1) _ _ y=_
  unfold Tensor.coeff at he; rw [smul_apply, inv_smul_eq_iff₀] at he -- r≥ etc
  · exact he
  positivity

def radialVar :Raw.Key G→Labels.Pol G
 | ⟨_,[],_⟩=> 0
 | ⟨a,b::w,i⟩=> let k:=w.length
                 let y:Fin (k+1)→E4:=Fin.cons (YM.basis b) (YM.basis ∘ w.get)
                 MvPolynomial.C (((k+1).factorial:ℕ) :ℂ) *
                   ∑ l : Fin (Labels.dim G k), MvPolynomial.X (⟨k,l⟩:Labels.Key G) * MvPolynomial.C (((axes G k l).val a y i : ℝ) :ℂ)

def radialPol : Raw.Pol G→+* Labels.Pol G:= MvPolynomial.eval₂Hom MvPolynomial.C radialVar

lemma var_reads (d:ℕ)(J:Labels.Jet G)(k:Raw.Key G)(h:k.chain.length+1 ≤ d):
    Labels.read J (radialVar k)=↑(derivative k.chain (radField d J k.primary) 0 k.color):=by
  rcases k with ⟨a,_|⟨b,w⟩,i⟩
  · simp [radialVar,derivative]
  simp only at *
  rw [order_eval _ _ _ _ _ h,radialVar]; simp only [map_mul,map_sum,Labels.read,MvPolynomial.aeval_C,MvPolynomial.aeval_X,Algebra.algebraMap_self,RingHom.id_apply, PiLp.smul_apply,smul_eq_mul,Complex.ofReal_mul, Complex.ofReal_natCast]; congr 1
  conv_rhs=> rw [← (axes G w.length).sum_repr (J w.length)]
  simp only [Labels.coord,AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul_of_tower, Finset.sum_apply,WithLp.ofLp_sum,Pi.smul_apply,PiLp.smul_apply,Complex.ofReal_sum,smul_eq_mul,Complex.ofReal_mul,sum_apply,smul_apply]

end Raw
end YM.RG06.Continuum

set_option autoImplicit false
noncomputable section
namespace YM.RG06.Continuum
namespace Raw
open Labels Tensor Lattice Analysis Wilson Function MvPolynomial
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical InnerProductSpace
variable {G : Gauge}
lemma grades_var (k:Raw.Key G): Tier Labels.bidegree (Raw.measure k) (radialVar k):=by
  cases k with | mk a w i=> cases w with
   | nil=> exact MvPolynomial.isWeightedHomogeneous_zero ..
   | cons b w=>
    rw [radialVar]; apply MvPolynomial.IsWeightedHomogeneous.C_mul; apply MvPolynomial.IsWeightedHomogeneous.sum; intro z hz
    rw [mul_comm]; exact (MvPolynomial.isWeightedHomogeneous_X _ _ (⟨w.length,z⟩:Labels.Key G)).C_mul _
lemma graded_pol {n l:ℕ}{p : Raw.Pol G} (h:Tier measure (n,l) p): Tier Labels.bidegree (n,l) (radialPol p):= Tier.bind _ _ (fun i=>grades_var i) h -- .. applied extra

lemma scope {p:Raw.Pol G}{n l}(h:Tier measure (n,l) p) {k}(hk:k ∈ p.vars) : Raw.size k≤n:=by
  obtain ⟨i,hi,hI⟩:= (MvPolynomial.mem_vars_iff_mem_support _).mp hk
  have hp:= congr_arg Prod.fst (h (MvPolynomial.mem_support_iff.mp hi))
  simp [Finsupp.weight_apply, Finsupp.sum,measure,Prod.fst_sum] at hp
  rw [←hp]; apply le_trans _ (Finset.single_le_sum (f:=fun a=>i a * Raw.size a) (fun a _=>by positivity) hI)
  apply le_mul_of_one_le_left (Nat.zero_le _) (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hI))

lemma region {p:Raw.Pol G} {n l:ℕ} (d:ℕ)(v:Labels.Jet G)(h:Tier measure (n,l) p)(hp:n≤d):read (radField d v) 0 p=Labels.read v (radialPol p):=by
  have hh(x)(he:x∈p.vars): read (radField d v) 0 (X x)=Labels.read v (radialVar x):= by
    rw [var_reads d v _ ((scope h he).trans hp),read,MvPolynomial.eval_X]
  rw [p.as_sum,_root_.map_sum,_root_.map_sum,_root_.map_sum]; refine Finset.sum_congr rfl fun i hi=>?_
  rw [read,MvPolynomial.eval_monomial,radialPol,MvPolynomial.eval₂Hom_monomial,_root_.map_mul]
  unfold Finsupp.prod;rw [_root_.map_prod]; simp only [_root_.map_pow,Labels.read,MvPolynomial.aeval_C,Algebra.algebraMap_self,RingHom.id_apply];
  congr 1; exact Finset.prod_congr rfl fun k hk=>congrArg (fun u:ℂ=>u^(i k)) (by
    rw [show MvPolynomial.aeval (Labels.coord v) (radialVar k) = read (radField d v) 0 (MvPolynomial.X k) from (hh _ (MvPolynomial.support_subset_vars_of_mem_support hi hk)).symm,read,MvPolynomial.eval_X])

/-- Main nonlinear renormalizer-free reading of one bare continuum field variable in Labels.Pol.
All input derivative orders, valid exactly within field horizon at root. -/
lemma radial_receipt (d:ℕ)(J:Labels.Jet G)(g:ℝ){j:ℕ}(w:Fin j→Axis)(a b:Axis)(i:G.ColorIndex)
    (h:j+2≤d):Labels.read J (radialPol (frame g w a b i))= (↑(covJet g (radField d J) w a b 0 i):ℂ):=by
  rw [← frame_eq (radField d J) (rad_smooth d J) g w a b, coeff_rebuild g w a b i (j+1) le_rfl, _root_.map_sum,_root_.map_sum,_root_.map_sum]
  refine Finset.sum_congr rfl fun k _=> ?_
  rw [MvPolynomial.smul_eq_C_mul,_root_.map_mul,_root_.map_mul,_root_.map_mul,region d J (grade_frame w a b i k) h]
  congr 1
  simp [radialPol,read,Labels.read] -- header read ambiguities
end Raw
end YM.RG06.Continuum
