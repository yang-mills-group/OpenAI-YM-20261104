import YM.X.Braid.Blade
/-!
# Mark and vertex polynomial Ward in θ. Real columns. 
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Braid
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter MeasureTheory Metric
open Stems hiding X
open Reed Interval Hinge PertExtension LatticePT
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {d:ℕ}
local notation "H"=> Hair G
local notation "V"=> Stems.Curly G
variable (δ:Cover→G.Color)
def eta (δ:Cover→G.Color)(i:Pin):= (1/2:ℝ) • (δ (i.1+step i.2) + δ i.1)
def θRow (p:H): Fan G:= ∑ j:G.ColorIndex,Finsupp.single (p.1,j) (G.ad (tan j) (eta δ p.1) p.2)
def str (i:H): Hair G→₀ℂ:= com (θRow δ i)
lemma struck (x:Brush G)(i:H): text (θ δ x) i=flatL x (θRow δ i):= by
   unfold flatL θRow; simp_rw [map_sum,Finsupp.linearCombination_single];
   let F:G.Color→ₗ[ℝ] ℝ:= (EuclideanSpace.proj i.2).toLinearMap ∘ₗ G.ad.flip (eta δ i.1); change F (x i.1)= _; conv_lhs=> rw [restore_tan (x i.1)]
   simp_rw [map_sum,map_smul]; exact Finset.sum_congr rfl fun j _=> mul_comm ..
lemma strokes (x:Brush G)(p:V): snap x (tilt (str δ) p)=snap x (stroke (θ δ x) p):= by
   induction p using MvPolynomial.induction_on with
   | C a=> simp
   | add p q h g=> simp only [map_add,h,g]
   | mul_X p i h=>
       let e:= θ δ x; have he: snap x (tilt (str δ) (X i)) = snap x (stroke e (X i)):= by
          rw [tilt_point,str,com_text,snaps_blade,stroke, slit_X,snap,aeval_C]; exact congr_arg Complex.ofReal (struck δ x i).symm
       rw [(tilt _).leibniz,(stroke _).leibniz]; simp only [map_add,smul_eq_mul,map_mul]; rw [he,h]
lemma still_mark (p:Word G): stroke (raised δ) (bookMark p 0)=0:= by
   rw [bookMark,map_sum]; simp_rw [Derivation.map_smul]; refine Finset.sum_eq_zero fun i _=>?_ ; rw [show stroke (raised δ) (hut 0 p i) = 0 from still δ (HS:=opt i p.sound p.chosen) (n:=(p.F.grades i).2) (by intro j hj x; exact no_under x i p.sound p.chosen hj) (fun v y=>congr_arg Complex.re (p.sound.gaugeInvariant (Pi.single i 1) v y)),smul_zero]
lemma first_mark (p:Word G): stroke (raised δ) (bookMark p 1)= -tilt (str δ) (bookMark p 0):= by
   apply snap_ext; intro x; rw [map_neg,strokes]; unfold bookMark; simp_rw [map_sum,← Finset.sum_neg_distrib,Derivation.map_smul,map_smul]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [← smul_neg]; exact congr_arg _ (high_price δ x (opt i p.sound p.chosen) (by intro j hj x; exact no_under x i p.sound p.chosen hj) (fun v y=> congr_arg Complex.re (p.sound.gaugeInvariant (Pi.single i 1) v y))) -- adjust sign

def flashVertex (p:Face ℤ): V:= mark (Log.flame (G:=G) p) (Log.brief _) 3
def powerB (p:Face ℤ)(k:G.ColorIndex): Fan G:= sun p.1 p.2.val.1 p.2.val.2 k
lemma paint_norm (v t:G.Color): inner ℝ v t=∑ i:G.ColorIndex,v i * t i:= by nth_rw 1 [restore_tan v]; rw [sum_inner]; simp_rw [real_inner_smul_left]; exact Finset.sum_congr rfl (fun i _=> congr_arg _ (EuclideanSpace.basisFun_inner ..))
lemma flame2 (p:Face ℤ) : mark (Log.flame (G:=G) p) (Log.brief _) 2= (1/2:ℂ) • ∑ i:G.ColorIndex,glyph (com (powerB p i))*glyph (com (powerB p i)):= by
    apply snap_ext; intro x; rw [mark_test,Log.flame_root _ _ (by omega),if_pos rfl, ← real_inner_self_eq_norm_sq,map_smul,map_sum];simp_rw [powerB,map_mul,com_text,snaps_blade,sun,arc_eq]; simp only [paint_norm,Complex.ofReal_sum,Complex.ofReal_div,Complex.ofReal_mul]; push_cast; change _= (1/2:ℂ)*_; ring
lemma flash_rose (p:Face ℤ)(x:Brush G) : snap x (stroke (raised δ) (flashVertex p))= Complex.ofReal (-inner ℝ (curlL p.2.val.1 p.2.val.2 x p.1) (curlL p.2.val.1 p.2.val.2 (θ δ x) p.1)):= by
    rw [flashVertex, high_price δ x (HS:=Log.brief p) (n:=2) (by intro j hj y; rw [Log.flame_root _ _ (by omega), if_neg (by omega),if_neg (by omega)]) ?_]; swap; · intro t A; rw [Log.flame,face_gauge,G.price_conj]; rfl -- inspect
    rw [flame2,Derivation.map_smul,map_smul, paint_norm]; push_cast; rw [map_sum,map_sum]; let y:= θ δ x; let t (i:G.ColorIndex):= powerB p i;
    have he (i:G.ColorIndex)(v x:Brush G) : snap v (stroke x (glyph (com (powerB p i))))= Complex.ofReal (flatL x (powerB p i)):= by rw [stroke,link_g, snap, com_read (text x) (powerB p i), aeval_C]; rfl
    change -((1/2:ℂ)*(∑ i:G.ColorIndex,snap x (stroke y (_*_))))=_; rw [Finset.mul_sum]; apply congr_arg; apply Finset.sum_congr rfl; intro i _; simp_rw [Derivation.leibniz, smul_eq_mul,map_add,map_mul, he i x y];
    simp_rw [com_text,snaps_blade,powerB, sun_at,sun, arc_eq,curling]; unfold y; ring

end YM.PositionX.Braid
