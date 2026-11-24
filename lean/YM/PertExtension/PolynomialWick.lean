import YM.PertExtension.OrbCovariance
import YM.Next.RANK.Common

/-! Agreement of the tree Hessian ordinary Gaussian polynomial moment
with purely finite Wick pairing on source legs, with no color or slot
cardinality hypotheses. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.PertExtension.SlopeWick
open Function Filter Set Wilson Lattice RG MeasureTheory GaussianScore Orb Gauge MvPolynomial Finset Next.Rank Normal
open scoped ContDiff Topology Classical BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}{V:Type*}(S : V→Source G n)(e:Even n.val)

def formed : Symmetric V:= by
  let P:= Orb.saddle (G:=G) e
  refine ⟨fun i j=>(↑(P.wick (S i) (S j)):ℂ),fun i j=>?_⟩
  change ↑(S j _)= (↑(S i _):ℂ)
  exact congr_arg Complex.ofReal (calc
     _ = P.P (P.inverse (S j)) (P.inverse (S i)) :=by rw [P.applies]
     _ = P.P (P.inverse (S i)) (P.inverse (S j)):= P.turns ..
     _ = S i (P.inverse (S j)) :=by rw [P.applies])
lemma glyph_overlap {I:Type*} [Fintype I](f:I→V)(s: Finset I):
    ((gaussian e (Law.product (S ∘ f) s):ℝ):ℂ)=blend (formed S e) 0 (glyphs f s):=by
   classical
   induction s using Finset.strongInduction with
   | _ s ih=>
    obtain rfl|⟨i,hi⟩:=s.eq_empty_or_nonempty
    · simp [Law.product,gaussian,show (Law.product _ ∅)=1 from rfl,Law.empty,glyphs]
    change (↑(gaussian e (fun x=>∏ j∈s,S (f j) x) : ℝ):ℂ) = _
    rw [Orb.gaussian_recursion e _ _ hi,← Finset.insert_erase hi]
    rw [erase_insert (notMem_erase _ _), Normal.spring 0 (formed S e) f (s.erase i) (notMem_erase i s),Pi.zero_apply,zero_mul,zero_add]
    rw [Complex.ofReal_sum];apply Finset.sum_congr rfl fun j hj=> ?_
    have hh : (s.erase i).erase j ⊂ s:= Finset.ssubset_of_subset_of_ssubset (erase_subset ..) (erase_ssubset hi) -- name
    rw [Complex.ofReal_mul,mul_comm]; exact congr_arg₂ (·*·) (α:=ℂ) rfl (ih _ hh)

lemma glyph_price {I:Type*} [Fintype I](f:I→V)(s:Finset I)(x) (c:ℂ) : (aeval (R:=ℂ) (fun i:V=> (↑(S i x:ℝ):ℂ)) (c • glyphs f s)).re = c.re * (Law.product (S ∘ f) s x) := by
   simp [glyphs, Law.product, map_smul,← Complex.ofReal_prod,Complex.mul_re]
local notation "dg"=> Chart.tangent G (Cotree n)
protected lemma expansion (p:poly V):
      let L:= (saddle (G:=G) e).kern
      gaussian e (fun x=>(aeval (R:=ℂ) (fun i:V=> (↑(S i x:ℝ):ℂ)) p).re) = (blend (formed S e) 0 p).re:=by
  intro L
  choose f hf using fun a:V→₀ℕ=>Common.letter a; try dsimp only at f hf -- may fail
  have he (i:V→₀ℕ): monomial i (coeff i p)= (coeff i p) • glyphs (f i) univ := by rw [← hf i,← map_smul,smul_eq_mul,mul_one]
  let U(i:V→₀ℕ):= Law.product (E:=Orb.Dir G n) (S∘ f i) univ
  let c(i):=(coeff i p).re
  let a(i:V→₀ℕ) x:= c i * U i x * L x
  have ha (i:V→₀ℕ):Integrable (a i) dg:=by
     unfold a; simp_rw [mul_assoc]; exact (Integrable.const_mul ((saddle (G:=G) e).integrable_entry dg (A:=U i) (Law.product_bound _ _) (Law.product_cont _ _)) (c i))
  nth_rw 1 [p.as_sum];change (∫ x:Dir G n, Complex.re (aeval (R:=ℂ) (fun (i:V)=> (S i x:ℂ)) (∑ i∈p.support,(monomial i) (coeff i p))) * L x ∂dg) / (∫ x,L x ∂dg)= _
  calc
     _ = (∫ x, (∑ i∈p.support, a i x) ∂dg) / _ := by congr 1; exact integral_congr_ae <| Eventually.of_forall fun x=>by dsimp only; rw [map_sum,Complex.re_sum,Finset.sum_mul];apply Finset.sum_congr rfl;intro i _; rw [he,glyph_price]
     _ = ∑ i∈p.support,c i * gaussian e (U i):= by
        rw [MeasureTheory.integral_finsetSum _ (fun i _=>ha i), Finset.sum_div]; exact Finset.sum_congr rfl fun i hi=> by unfold a; simp_rw [mul_assoc,MeasureTheory.integral_const_mul]; change (c i*(∫ x,U i x *L x ∂dg))/(∫ x,L x ∂dg) = c i * ((∫ x,U i x *L x ∂dg) / _); ring
     _ = _:= by
       have hval i : (blend (formed S e) 0 (monomial i (coeff i p):poly V)).re = c i * gaussian e (U i):= by rw [he,map_smul, ← glyph_overlap]; simp [smul_eq_mul,c,U,Complex.mul_re]
       conv_rhs => rw [p.as_sum];
       rw [map_sum,Complex.re_sum]; exact Finset.sum_congr rfl fun i hi=> (hval i).symm
end YM.PertExtension.SlopeWick
