import YM.MS.Alps.Mountain
/-!
# Continuing Θ scaling (no analogy to φ), cancellations exact

Exponents Φ; affine D rotations independent. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Alps
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum
open Momentum Metric
open scoped Topology ContDiff
variable {G:Gauge}{I A B E P:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup P][NormedSpace ℝ P]
  {m n:ℕ}
lemma net_sr (t:ℝ)(w:Legs (Mode A P)): net (sr t w)=exp t • net w:= by induction w with| nil=>simp [sr,net]| cons i l ih=> unfold sr at *; simp only [List.map_cons,net_cons, ih, smul_add]
lemma degree_sr (p:Sector A)(t:ℝ)(w:Legs (Mode A P)): degree (field p) (sr t w)=degree (field p) w:= by induction w with| nil=>rfl| cons i l ih=> unfold sr at *; rw [List.map_cons,degree_cons,degree_cons (x:=i),ih]; -- rfl
lemma scatter_sr (p:Sector A)(t:ℝ)(v:Legs (Mode A P))(K:Shared (Mode A P) ℂ): scatter (field p) (sr t v) K=scatter (field p) v (fun l r=> K (sr t l) (sr t r)):= by
    induction v generalizing K with| nil=>rfl| cons i l ih=> rw [show sr t (i::l)=(i.1,exp t • i.2)::sr t l from rfl,scatter_cons, ih,scatter_cons]; congr 1; funext x y; rw [degree_sr]; rfl
lemma price_mag_split {u v w:Legs (Shore G m)}(H:Split u v w): mass u+mass v=mass w:= split_sum _ H
-- arbor algebra, easier for reversible
lemma a_rev {U:Rip G}(t:ℝ)(a:ℂ)(hp:reverseF U): reverseF (pulse a t U):= by intro n i j p; unfold pulse; rw [smul_neg,hp,show a-_= a-(wfield i:ℂ) from rfl, show a-(wfield i:ℂ)-(wfield j:ℂ)=_ from sub_right_comm ..]; ring -- last check
variable (a b c z:ℂ)(t:ℝ)
lemma mulc (x y k s:ℂ): amount a t * amount b t * amount c t * (x*y*k*s)=(amount (a+b+c) t) * (x*y*k*s):= by simp only [amount_add]
variable {U: Rip G} {F H: Mob G}
lemma air_tree (he:reverseF U): arbor (pulse a t U) (plow b t F) (plow c t H)=plow (a+b+c) t (arbor U F H):= by
   ext n l; unfold arbor plow tree; dsimp only; rw [scatter_sr];
   let e(t):= amount t -- maybe implicit fail
   refine Eq.trans ?_ (map_smul (allocate (field Landau.parity) l) (amount (a+b+c+(mass l:ℂ)) t) (fun x y=> attaches Landau.parity (U n) (F n) (H n) (sr t x) (sr t y))) -- calc orientation
   refine scatter_congr _ _ _ _ (fun x y hp=>?_); rw [show ∀ (k:ℂ)(p:Shared (Shore G n) ℂ),(k • p) x y=k*p x y from fun k p=> rfl, convertR (a_rev t a he n),convertR (he n)]; simp_rw [Finset.mul_sum];
   apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; unfold radius; simp only [pulse,Price_cons,net_sr,degree_sr,neg_neg]; -- unfolding sr too early
   unfold sr; simp only [List.map_cons,smul_neg]; have he:= price_mag_split hp; simp only [Int.cast_add]; rw [← he]; simp only [Int.cast_add]
   let Y:= a-wfield i- wfield j; let A:=b+(wfield i+(mass x:ℂ)); let Z:= c+(wfield j+(mass y:ℂ)); rw [show amount (a+b+c+ ((mass x:ℂ)+(mass y:ℂ))) t= amount Y t * amount A t*amount Z t by rw [← amount_add,← amount_add]; congr 1; unfold Y A Z; ring]; unfold Y A Z; ring
-- ∆ scale W
lemma we_sc (i j:Cfield G m) (l: Legs (Shore G m))(p:Momentum (L m)):
   let q:= exp t • p; pulse a t U m i j p * plow b t F m ((i,p)::(j,-p)::l)= amount (a+b+(mass l:ℂ)) t * (U m i j q * F m ((i,q)::(j,-q)::sr t l)):= by
   intro q; unfold pulse plow; simp only [sr,List.map_cons,smul_neg,Price_cons]; simp only [Int.cast_add]; unfold q; rw [mul_mul_mul_comm,← amount_add, show a- ↑(wfield i)- ↑(wfield j)+(b+ _)=a+b+(mass l:ℂ) from by ring]
lemma n_track (l:Legs (Shore G m))(p:SectorP m): Wtr z (pulse a t U) (plow b t F) p l=amount (a+b+ (mass l:ℂ)) t * Wtr z U F (exp t • p) (sr t l):= by
   have he s f c d : token (pulse a t U) (plow b t F) s f c d p l=amount (a+b+(mass l:ℂ)) t* token U F s f c d (exp t • p) (sr t l):= by unfold token fleck; rw [we_sc,mass_lift,lift_sr,map_smul]
   simp only [Wtr, Pi.add_apply,Pi.smul_apply,yeast,smul_eq_mul,at_trc, we_sc a b t,he, ← Finset.mul_sum] -- needed factoring
   ring
end YM.MS.Alps
