import YM.FVA2.Harmonic
/-!
# Compress site complement pairing to unambiguous Grassmann conventions

Measure twice half site: in particular at fixed sites project then double. Evaluate
BV ghost vertices on c=liftMean(cx) and K=-d(liftMean(cbarx)), B=0. Choose cbar
as the **ℓ-dual basis** to the c basis. Then unit Wick pair. Changing the real basis
 does not affect normalized bosonic insertion correlations (no statement about changing
 coordinates in BV sectors independently). Costs ℓ use full cover including all site weights.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Trans
open Lattice Gauge FormalOPE.RG10 FormalOPE.RG10.BlockGauge
open PertExtension PertExtension.Series PertExtension.Orb PertExtension.Chart
open Function Finset Filter Set Metric MeasureTheory Precision Inherit Push.Loops TreeBasis
open Wilson Based GaussianScore MultiGauge MS.Orbit MS MS.Orbit.Cog MS.Swirl Green MS.Bare
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable (G : Gauge) (n : Side) (hn : _root_.Even n.val)

lemma siteSum (p:Param G n)(i:G.ColorIndex): ∑ x:Site n,siteColour G n p i x=0:= by
    have hv:= DFunLike.congr_arg (EuclideanSpace.proj i : G.Color →L[ℝ] ℝ) (sum_mean G n p); rw [map_zero,map_sum] at hv; exact hv
lemma payGF (p q : Param G n): ℓ G n p q=(∑ b:G.ColorIndex, Green.dot (siteColour G n p b) (lap (siteColour G n q b)))/2:= by
    rw [pair_ghost,prod_cost]; simp_rw [grad_color]; apply congr_arg (fun x:ℝ=>x/2); refine Finset.sum_congr rfl fun i _=> ?_; rw [Green.dot_grads]; rfl

variable (y:Site n) (i:G.ColorIndex)
lemma exists_center : ∃ p, siteCover G n p= fun x=>EuclideanSpace.single i (siteG y x):= by
   refine in_sector G n (fun x=>congr_arg _ (siteG_even x y)) ?_
   apply PiLp.ext; intro j; rw [WithLp.ofLp_sum,Finset.sum_apply]; by_cases h:j=i
   · subst j; simp [siteG_mean]
   simp [h]

def center : Param G n := (exists_center G n y i).choose
lemma center_eq (j:G.ColorIndex) : siteColour G n (center G n y i) j= if j=i then siteG y else 0:= by
   ext x; unfold siteColour center; rw [(exists_center G n y i).choose_spec]; split
   next h=> simp [h]
   next h=> simp [h]
def ghostMode : Module.Dual ℝ (Param G n) := (EuclideanSpace.proj i).toLinearMap ∘ₗ (LinearMap.proj y ∘ₗ siteCover G n)
lemma basis_P (q:Param G n) : ℓ G n (center G n y i) q=ghostMode G n y i q := by
   rw [ghost_turn,payGF,Finset.sum_eq_single i,center_eq,if_pos rfl,show Green.dot _ _=2 * siteColour G n q i y from pay_siteG _ (fun x=> congr_arg (fun c:G.Color=> c i) (evenSite G n q x)) (siteSum G n q i) y]; rotate_left
   · intro j _ hj; rw [center_eq,if_neg hj,map_zero,Green.dot_turn, Green.dot_zero]
   · simp
   change 2 * ghostMode G n y i q/2= _; ring
lemma solve_G : (poisson G n).symm (ghostMode G n y i)=center G n y i:= by
   apply (poisson G n).injective; rw [LinearEquiv.apply_symm_apply]; symm; exact LinearMap.ext (basis_P G n y i)

-- dual conventions
variable {T:Type}[Fintype T](b:Module.Basis T ℝ (Param G n))
lemma character (x:Site n)(j:G.ColorIndex) : let e : T→Param G n:= fun k=>(poisson G n).symm (b.coord k)
     ∑ k:T, ghostMode G n x j (b k)* ghostMode G n y i (e k) = if j=i then siteG y x else 0:= by
   intro e; let A:= center G n y i; let U:= ghostMode G n x j; let V:= ghostMode G n y i
   have he(k:T): V (e k)=b.coord k A:= by rw [show V _ = _ from (basis_P G n y i (e k)).symm, ghost_turn]; change poisson G n (e k) A= _; rw [show poisson G n (e k)=_ from LinearEquiv.apply_symm_apply (poisson G n) (b.coord k)]
   have hU:U A=(if j=i then siteG y x else 0):= by change siteColour G n A j x = _; rw [center_eq]; split <;> rfl
   rw [← hU, ← (show ∑ k:T, b.coord k A • b k=A from b.sum_repr A), map_sum]; apply Finset.sum_congr rfl; intro k _; rw [show ghostMode G n y i _=b.coord k A from he k, map_smul]; exact mul_comm ..

private def minusBar (y:Site n) (i:G.ColorIndex) (j:Axis) (p:Param G n):= - coverL G n (d G (rim n) p) (y,j) i
lemma pairG (x:Site n)(j:Axis)(a:G.ColorIndex) : Chill (cov G n true) (SiteC i,x) (KV j a,y) =
          ((∑ k:T, ghostMode G n x i (b k) * (-coverL G n (d G (rim n) ((poisson G n).symm (b.coord k))) (y,j) a) :ℝ):ℂ):= by
     let f k:= (poisson G n).symm (b.coord k); let V (y:Site n) (p:Param G n):= siteColour G n p a y
     rw [show (∑ k:T, ghostMode G n x i (b k)*_)= -( (∑ k:T, ghostMode G n x i (b k)*ghostMode G n (y+step j) a (f k))-(∑ k:T,ghostMode G n x i (b k)*ghostMode G n y a (f k))) from (?_)]; swap
     · rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro k _; rw [differential G n, PiLp.sub_apply]; change ghostMode G n x i (b k)*(-(V (y+step j) (f k)-V y (f k))) = -(ghostMode G n x i (b k)*V (y+step j) (f k)-ghostMode G n x i (b k)*V y (f k)); ring
     have hv (t:Site n) : ∑ k:T,ghostMode G n x i (b k)*ghostMode G n t a (f k)= if i=a then siteG t x else 0 := character G n t a b x i
     rw [hv,hv]; by_cases he:i=a; · subst a; rw [contracted_ghost, siteLine,fwd_of,if_pos rfl, siteG_sym x,siteG_sym x y,if_pos rfl]; -- `if_pos` one
     rw [cov_color _ _ he, if_neg he,if_neg he]; simp

end YM.FVA2.Trans
