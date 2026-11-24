import YM.X.Braid.Steps
/-!
# Pixel integration by parts. Apply K Ward with real χ, incl non-harmonic longitudinal allowed (bloom). Cutoff in initial *corner*, not necessarily centered. Aliases hypothesis discharged where invoked (later).
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Braid
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter MeasureTheory Metric
open Reed Interval Hinge PertExtension LatticePT CellsInt
open Stems hiding X
open scoped Topology ContDiff BigOperators Classical Pointwise
variable {G:Gauge} {k d m:ℕ}
local notation "R"=> Hair G →₀ ℝ
local notation "H"=> Hair G
local notation "V"=> Curly G
variable (p:Word G)(χ: Lane)(δ:Cover→G.Color)
lemma fire_power : stroke (raised δ) (fireMask (G:=G) χ)= -groundS χ δ - cutoffShell χ δ:= by
    apply snap_ext; intro A; let B:= θ δ A
    rw [plus_maskR,map_sub,map_neg, shell_mask,full_maskK];
    let Q(b c:G.Color) := Complex.ofReal (inner ℝ b c)
    let x (i j:Axis)(t: Cover):= curlL i j A t
    let y(j:Axis)(t:Cover):=B (t,j)
    let f (z:Cover)(i j:Axis):=Q (x i j z) (stepValue (y j) i z)
    have hx(i j:Axis)(t:Cover): x j i t= - x i j t:= congr_fun ((trot_secure A).ax ..) t
    have HH (i j:Axis)(t): Q (x i j t) (curlL i j B t)= f t i j + f t j i:=by
       change Q _ (stepValue (y j) i t-stepValue (y i) j t)= _; unfold f; nth_rw 1 [hx i j]; simp [Q,inner_add_right,sub_eq_add_neg]; -- rw wrong inside? 
    have hf (i j:Axis)(z:Cover): f z i j= Q (x i j z) (y j (z+step i))- Q (x i j z) (y j z):= by unfold f stepValue Q; rw [inner_sub_right,Complex.ofReal_sub]
    have hv (z:Cover): ∑ i:PlaqAxes,Q (x i.val.1 i.val.2 z) (curlL i.val.1 i.val.2 B z)= ∑ i:Axis,∑ j:Axis,f z i j:= by
       simp_rw [HH]; apply plaq_turn; intro i; unfold f; rw [show x i i z=0 from by change _-_ = (0:G.Color); exact sub_self _]; simp [Q]
    have hb (z:Cover)(j:Axis): Q (orderK j A z) (y j z)=∑ i:Axis,(Q (x i j (z-step i)) (y j z)-Q (x i j z) (y j z)):= by
       have he: orderK j A z=∑ i:Axis,(x i j (z-step i)-x i j z):= by rw [orderK,LinearMap.neg_apply, Pi.neg_apply,LinearMap.sum_apply, Finset.sum_apply, ← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _; change -(x i j (z-step i+step i)-x i j (z-step i))= _; rw [sub_add_cancel]; abel
       unfold Q; simp_rw [he,sum_inner,inner_sub_left,Complex.ofReal_sum,Complex.ofReal_sub]
    let U (i:Axis)(z:Cover):ℂ:=∑ j:Axis,Q (x i j (z-step i)) (y j z)
    change -(beadR χ (fun z:Cover=>∑ i:PlaqAxes,Q _ (curlL _ _ B z))) = -(beadR χ (fun z:Cover=>∑ j:Axis,Q _ (y j z)))-∑ i:Axis,beadR (changed χ i) (U i)
    apply neg_inj.mp; rw [neg_sub, sub_neg_eq_add,neg_neg];
    -- identity bead shift U(x+i), ∑ ~
    have he (i:Axis): beadR (changed χ i) (U i)= beadR χ (fun z=> U i (z+step i) - U i z):= by rw [show (fun z=>_ - _)= (fun z:Cover=>U i (z+step i))-U i from rfl, bead_sub, ← sendB]; exact (map_sub (Finsupp.linearCombination ℝ (U i)) ..)
    simp_rw [he, ← bead_sum]; rw [← bead_add]; refine congr_arg _ (funext fun z=>?_); dsimp only [Pi.add_apply];
    rw [hv];simp only [hf,hb, U,← Finset.sum_sub_distrib,sub_add_cancel,add_sub_cancel_right]; rw [Finset.sum_comm (f:=fun j i:Axis=>Q (x i j (z-step i)) (y j z)-Q (x i j z) (y j z))]; simp_rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>?_ ; abel

def hearth (G:Gauge)(χ:Lane): Finset (Hair G):= (χ.support ×ˢ Finset.univ) ×ˢ Finset.univ
lemma ground_set : groundS χ δ=∑ i∈hearth G χ, (χ i.1.1:ℂ) • groundV δ i:= by
   unfold groundS beadR hearth; rw [Finset.sum_product,Finsupp.linearCombination_apply,Finsupp.sum]; rw [Finset.sum_product]; refine Finset.sum_congr rfl fun i _=> ?_; simp_rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun j _=> Finset.sum_congr rfl fun k _=> ?_; exact RCLike.real_smul_eq_coe_smul .. -- name

-- premises eventually for all valuations
variable (n:Side)
structure High (n:Side)(χ:Lane)(p: V):Prop where
  paid : ∀ j∈p.vars, χ j.1.1=1
  twin (x:Hair G)(hx:x∈p.vars)(y:Hair G)(hy:y∈ hearth G χ) (he: place (0:Site n) x=place (0:Site n) y):x=y
lemma leads (h:High (G:=G) n χ (bookMark p 0))(x:Hair G)(hx:x∈hearth G χ): edge (flow G n) (com (keyRow x)) (bookMark p 0)= hair x (bookMark p 0):= by
    let r:= raised (anomaly n x); have he (u t:Brush G)(p:V): stroke (u-t) p=stroke u p - stroke t p:= by rw [sub_eq_add_neg, stroke_add,← neg_one_smul ℝ t, stroke_scale]; push_cast; simp [sub_eq_add_neg] -- simplify smul -1
    rw [palette, pays,he, still_mark,sub_zero]; apply MvPolynomial.derivation_eq_of_forall_mem_vars; intro i hi; rw [stroke,hair,slit_X,slit_X]; apply congr_arg; change Complex.ofReal (text (twin n x) i)=_; unfold twin; by_cases hk:i=x; · subst x; simp [Pi.single_apply,text,textL]
    change Complex.ofReal (if place (0:Site n) i=place 0 x then 1 else (0:ℝ))= _; rw [if_neg (fun he=>hk (h.twin _ hi _ hx he))]; simp only [Pi.single_apply,if_neg hk,Complex.ofReal_zero]

def crisp (p:Word G)(χ:Lane)(n:Side): V:= milk (flow G n) (bookMark p 1)- multi (flow G n) (milk (flow G n) (bookMark p 0)) (fireMask χ)
lemma Ward_power (h:High (G:=G) n χ (bookMark p 0)) : stroke (raised δ) (crisp p χ n)= -tilt (str δ) (milk (flow G n) (bookMark p 0)) + multi (flow G n) (milk (flow G n) (bookMark p 0)) (cutoffShell χ δ):= by
    refine kurot (g:=com ∘ keyRow) (χ:=fun i=> (χ i.1.1:ℂ)) (flow G n) (str δ) _ _ _ (hearth G χ) (still_mark δ p) (first_mark δ p) ?_ ?_ ?_ (leads p χ n h)
    · change stroke (raised δ) _ = _; rw [fire_power, ground_set]; rfl
    · intro i hi; have he:= h.paid i hi; simp [he,hearth]
    exact fun i hi=> by rw [h.paid i hi, Complex.ofReal_one]
end YM.PositionX.Braid
