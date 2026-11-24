import YM.WilsonCoeffUV.Vacuum.UV.LimitGauge
import YM.Next.STATIONARY.Lift.Pathways
/-!
# Laurent contraction on arbitrary-arity *translation invariant* slots

Rank counted in own mesh (there is one DEPENDENT momentum leg). No floating
translation convention. True distance weights paid when changing root norms.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank.Mosaic
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Stationary
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{n N M e m i k r t:ℕ}{α β V:Type*}

abbrev Haze:= Stationary.Ink
abbrev post (G:Gauge)(t:ℕ):= Ten ℝ (YForest G) (t+1)
-- general rooted

def feetP (x:Shift (Keys t)) : Fin (t+1) → Cover := Fin.cons 0 fun i a=> x (i,a)
def goose (x:Shift (Keys t))(u:Haze G (t+1))(i:Run (t+1)): Fin (t+1)→ YForest G:= fun j=> (feetP x j,i j,u j)
def plantern (F:post G t)(u)(i)(x):= F (goose x u i)
def pictures (F :post G t) : Picture G t:= fun u i=>readable (plantern F u i)
lemma trunkG (x:Shift (Keys t))(u:Haze G (t+1))(i:Run (t+1)): size x≤ t * soar terrain (goose x u i):=by
    have he : size x= ∑ j:Fin t, terrain.gap (feetP x 0) (feetP x j.succ):=by
       unfold Laurent.size; rw [Fintype.sum_prod_type]; apply Finset.sum_congr rfl; intro j _; change _= size (feetP x j.succ-feetP x 0); simp [feetP,Laurent.size]
    rw [he]; refine le_trans (Finset.sum_le_sum (g:=fun _=>soar terrain (goose x u i)) (fun j _=> (leg_le terrain (Prod.fst ∘ goose x u i) 0 j.succ))) ?_; simp

def hingeZ (σ:ℝ)(t:ℕ):ℝ:= σ/(2*(t+1:ℕ))
def hinges (σ:ℝ)(t:ℕ):ℝ:= (2*((1+hingeZ σ t)/(hingeZ σ t)))^Fintype.card (Keys t)
lemma hinge_paid {σ:ℝ}(h:0<σ)(t:ℕ):0<hingeZ σ t:= by unfold hingeZ; positivity
lemma hinge_reserve {σ:ℝ}(h:0<σ)(t:ℕ):0< hinges σ t:=by unfold hinges; have he:=hinge_paid h t; positivity

variable {F :post G t}{s A:ℝ}
lemma wages (h:Amber terrain s A F)(p:0<s)(i j): Width (hingeZ s t) (A*hinges s t) (fun x=>(plantern F i j x:ℂ)):= by
   let a:= hingeZ s t
   have he:0<a:=hinge_paid p _
   have hv : 2*a*((t+1:ℕ):ℝ)=s:=by unfold a hingeZ; field_simp
   apply budget_minor (cap_scale (Width.compactPay (α:=Keys t) a he) h.1) (fun _=>by positivity); intro x
   let y:=soar terrain (goose x i j)
   rw [Complex.norm_real]; apply le_trans (mul_le_mul_of_nonneg_left (h.2 _) (by positivity)); rw [mul_left_comm]
   apply mul_le_mul_of_nonneg_left _ h.1; rw [← Real.exp_add,Real.exp_le_exp];
   change a*size x + -s*y≤ -a*size x
   rw [← hv]; have ht : (size x:ℝ) ≤ t * (y:ℝ):=by exact_mod_cast trunkG x i j
   push_cast; nlinarith
lemma sums_read (h:Amber terrain s A F)(p:0<s) (r:Corn (Keys t))(i j): Summable fun x=> mode (axes r) x * (plantern F i j x:ℂ) := ((wages h p i j).series (axes r) (fun i=>by simp [axes, (hinge_paid p t).le])).2.1.of_norm

-- displacement under move one foot by w

def deltaP {t:ℕ}(i:Fin (t+1))(w:Cover): Shift (Keys t) := fun j=> ((if j.1.succ=i then w else 0)-(if 0=i then w else 0):Cover) j.2
lemma feet_move (x:Shift (Keys t))(i:Fin (t+1))(w:Cover)(j:Fin (t+1)):
    feetP (x+deltaP i w) j=(feetP x j + (if j=i then w else 0))-(if 0=i then w else 0):=by
   refine Fin.cases ?_ (fun j=>?_) j
   · simp [feetP]
   funext a; simp [feetP,deltaP]; abel
lemma rel_anchored (h:stroll F)(x:Shift (Keys t))(u:Haze G (t+1))(v:Run (t+1))(j)(w:Cover):
    F (update (goose x u v) j (feetP x j+w, v j,u j)) = F (goose (x+deltaP j w) u v) := by
   let b: Cover:= if (0:Fin (t+1))=j then w else 0
   apply Eq.trans ?_ (h b _); congr 1
   funext i
   by_cases p:i=j
   · subst i; rw [update_self]; change (_,_,_)=(b+feetP _ j,_,_); rw [feet_move, if_pos rfl]; refine Prod.ext ?_ rfl; unfold b; dsimp only; abel
   rw [update_of_ne p]; change (_,_,_)=(b+feetP _ i,_,_); rw [feet_move,if_neg p]; refine Prod.ext ?_ rfl; unfold b; dsimp only; abel
lemma mode_delta (p :Phase (Keys t))(i:Fin (t+1))(w:Cover): mode p (deltaP i w)=mode (plotted p i) w:= by
   refine Fin.cases ?_ (fun j=>?_) i
   · simp only [plotted,Fin.cons_zero]; unfold missing mode
     congr 2
     rw [Fintype.sum_prod_type,Finset.sum_comm]; apply Finset.sum_congr rfl; intro a _
     simp only [Pi.neg_apply,Finset.sum_apply,Function.comp_apply,strand]; rw [← Finset.sum_neg_distrib, Finset.sum_mul]; apply Finset.sum_congr rfl; intro j _; simp [deltaP]
   simp only [plotted,Fin.cons_succ]; unfold mode
   congr 2
   rw [Fintype.sum_prod_type,Finset.sum_eq_single j]
   · apply Finset.sum_congr rfl; intro a _; rw [deltaP,if_pos rfl,if_neg (Fin.succ_ne_zero j).symm,sub_zero]; rfl
   · intro b _ hb; simp [deltaP,hb,(Fin.succ_ne_zero j).symm]
   simp
lemma zeroth (p:Momentum)(a:Axis) : symbol 0 p (coord a) vac=mode p (step a)-1:=by
   unfold symbol wedge Exterior.q; rw [Matrix.sum_apply,Finset.sum_eq_single a]; rotate_left
   · intro k _ h; simp [Exterior.left,coord,h]
   · simp
   rw [show mode p (step a)= Complex.exp (Complex.I * p a) by simp [mode, step_apply,apply_ite ((↑):ℤ→ℂ),mul_ite]]
   simp [Exterior.left,coord,vac_only,Exterior.parity,Exterior.pre,Finset.filter_singleton]
lemma truck (F:post G t)(h:Blue.Smooth F)(x:Fin (t+1)→ YForest G) (j:Fin (t+1)): ∃ y: Fin t→YForest G,∀ u, F (update x j u)=F (Fin.cons u y):= by
   let f:= Equiv.swap 0 j; let y:=Fin.tail (x ∘ f)
   refine ⟨y,fun u=>?_⟩; rw [← h f (update x j u)]; congr 1
   funext i; refine Fin.cases (by simp [f]) (fun i=>?_) i
   have hz: f i.succ≠ j:= fun he=>(Fin.succ_ne_zero i) (f.injective (he.trans ((Equiv.swap_apply_left ..).symm)))
   rw [Function.comp_apply,update_of_ne hz, Fin.cons_succ]; rfl
lemma drift_real (h:stroll F)(hp:Blue.Smooth F)(w:∀ x i,windsL x i F=0) (i)(x:Shift (Keys t))(j:Haze G (t+1))(u:Run (t+1)) :
    ∑ a:Axis,(plantern F j (update u i (coord a)) (x+ deltaP i (-step a))- plantern F j (update u i (coord a)) x)=0:=by
   let z:= feetP x i
   obtain ⟨y,hy⟩:=truck F hp (goose x j u) i
   have hw a : goose x j (update u i (coord a))=update (goose x j u) i (stone (z,a) (j i)):= by funext k; by_cases H:k=i<;>simp [goose,stone, H,z]
   have he a: plantern F j (update u i (coord a)) (x+deltaP i (-step a))=F (Fin.cons (stone (z-step a,a) (j i)) y):= by
       rw [plantern, ← rel_anchored h x j (update u i (coord a)) i (-step a),hw,update_self, update_idem,hy]; rfl
   have ht a: plantern F j (update u i (coord a)) x=F (Fin.cons (stone (z,a) (j i)) y):= by rw [plantern,hw,hy]
   have hz:= congr_fun (w z (j i)) y
   rw [windsL,Finset.sum_apply] at hz; simp_rw [Pi.sub_apply,prune] at hz
   simp_rw [he,ht,Finset.sum_sub_distrib]; rw [Finset.sum_sub_distrib] at hz; exact sub_eq_zero.mpr (sub_eq_zero.mp hz).symm
lemma roller {v : Fin (t+1)} (r:Corn (Keys t)) (i : Haze G (t+1))(j:Run (t+1))(a:Axis): mode (plotted (axes r) v) (step a) * pictures F i j (axes r)= ∑' x, mode (axes r) x * (plantern F i j (x+deltaP v (-step a)):ℂ):=by
   let b:= -step (S:=ℤ) a; let Y:= deltaP v b; let W:= Equiv.addRight Y
   conv_lhs=> arg 2; rw [pictures,readable,Laurent.read,← W.tsum_eq]
   rw [← tsum_mul_left]; refine tsum_congr fun i=>?_
   rw [show W i=i+deltaP v (-step a) from rfl,mode_shift,mode_delta,mode_opposite,smul_eq_mul]; field_simp
lemma contracts (h:Amber terrain s A F)(he:0<s)(hp:Blue.Smooth F)(hb:stroll F)(w:∀ x i,windsL x i F=0)(i): Contractible (pictures F i):=by
   intro p j v
   let Q (a:Axis):= update v j (coord a)
   let x (a:Axis) (r):= mode (axes p) r * (plantern F i (Q a) r:ℂ)
   let y (a:Axis)(r :Shift (Keys t)):= mode (axes p) r * (plantern F i (Q a) (r+deltaP j (-step a)):ℂ)
   have hh a : Summable (x a):= sums_read h he p i (Q a)
   have ht a: Summable (y a):= by
       let g := Equiv.addRight (deltaP j (-step a))
       apply Summable.of_norm
       change Summable fun i=> ‖mode (axes p) i * (↑(plantern F _ _ (g i)):ℂ)‖
       have H :∀ p':Shift (Keys t), ‖mode (axes p) p'‖=1:= fun i=> mode_real _ _ (axes_real p)
       have h' := g.summable_iff.mpr ((hh a).norm)
       simpa only [Function.comp_apply,x,H,norm_mul,one_mul] using! h'
   rw [← Equiv.sum_comp axisEquiv]; simp_rw [coord_map,zeroth,sub_mul,one_mul,roller];
   change ∑ a, ((∑' r,y a r)- pictures F i (Q a) (axes p))=0
   have hF a: pictures F i (Q a) (axes p)=∑' r,x a r:=rfl
   simp_rw [hF,← Summable.tsum_sub (ht _) (hh _)]; rw [← Summable.tsum_finsetSum (f:=fun a i=>y a i-x a i) (fun a _=> (ht a).sub (hh a))]; refine Eq.trans (tsum_congr (g:=fun _=>0) ?_) (by simp); intro b
   simp_rw [x,y,←mul_sub,← Complex.ofReal_sub,← Finset.mul_sum, ← Complex.ofReal_sum]; unfold Q; rw [drift_real hb hp w j b i v, Complex.ofReal_zero, mul_zero]

-- palette projection by scalar stencil; no sign enforcement in packet
lemma paintedZ (h:mural F)(x:Shift (Keys t))(v:Run (t+1)) : (fun i=>plantern F i v x)∈ paints G (t+1):=by
   intro u xs
   let L:= Fin (t+1)
   let Q i:=plantern F i v x
   let f i: Edge Cover:= (feetP x i,axisEquiv.symm (v i))
   have hw i: Q i=∑ j,(∏ b,gammaC u (j b) (i b)) • Q j:= by
       have hp:= h u f i; have he (i:Haze G (t+1)): (fun j=>stone (f j) (i j))=goose x i v:=by funext j; unfold f stone goose; rw [← coord_map,Equiv.apply_symm_apply]
       change plantern F _ _ _=_; simp_rw [he] at hp; exact hp
   have hh j i: G.adjoint u (xs j) i=∑ a,gammaC u i a*xs j a:= (show _= (gammaC u *ᵥ ((coatC G).symm (xs j))) i by rw [gammaC, LinearMap.toMatrix'_mulVec]; rfl)
   change ∑ i,Q i * ∏ j,G.adjoint u (xs j) (i j)=∑ i,Q i *∏ j, xs j (i j)
   conv_rhs=> arg 2; intro i; arg 1; rw [hw i]
   simp_rw [hh, Fintype.prod_sum,Finset.mul_sum,Finset.sum_mul]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro i _; simp only [Finset.prod_mul_distrib,smul_eq_mul]; ring
lemma hues (h:Amber terrain s A F)(he:0<s)(ht:Blue.Smooth F)(p:stroll F)(hp:∀ x i,windsL x i F=0)(hb:mural F): Features (pictures F) (hingeZ s t) (A*hinges s t):= by
   have hg := hinge_paid he t
   refine ⟨fun i j=> Firm.of_series (wages h he i j) hg, contracts h he ht p hp,?_,?_⟩
   · intro x i p H; unfold pictures readable Laurent.read; rw [tsum_star]; apply tsum_congr; intro j
     simp only [smul_eq_mul,star_mul,Complex.star_def]; rw [Complex.conj_ofReal];
     have hh := mode_adjoint (star (-p)) j; rw [star_star,star_neg,H] at hh; simp only [mode_inverse,mode_opposite, inv_inv] at hh; rw [←Complex.star_def,mode_inverse,hh]; ring
   intro p i
   let K j z:=plantern F j i z
   have hC j: Width (hingeZ s t) (A*hinges s t) (K j):=by simpa only [Width, Complex.norm_real] using wages h he j i
   have hu j z : K j z=(picker G (t+1)*ᵥ (fun i=>K i z)) j:= congr_fun (keeps _ (paintedZ hb z i)).symm j
   have hv j: pictures F j i (axes p)=(approached (picker G (t+1)) *ᵥ (fun j=>pictures F j i (axes p))) j:= by
       change readable (K j) _=(approached _ *ᵥ (fun j=> readable (K j) (axes p))) j; conv_lhs=> rw [show K j=(fun z=>(picker G (t+1)*ᵥ (fun i=>K i z)) j) from funext fun z=>hu j z]
       exact reserve_read hC hg _ _ p
   constructor
   · convert picks (fun x=>(pictures F x i (axes p)).re) using 1; ext1 x; dsimp only; conv_lhs=> rw [hv x]
     simp [Matrix.mulVec,dotProduct,approached]
   convert picks (fun x=>(pictures F x i (axes p)).im) using 1; ext1 x; dsimp only; conv_lhs=> rw [hv x]
   simp [Matrix.mulVec,dotProduct,approached]
end YM.WilsonCoeffUV.Bank.Mosaic
