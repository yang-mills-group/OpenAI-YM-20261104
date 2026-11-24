import YM.X.Charting.Trim
/-!
# Periodic versus Inversion covariance entries. Explicit axes.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Hinge
open Function Filter Set Metric MeasureTheory Lattice Wilson PertExtension PertExtension.Series PertExtension.Series.Radial
open Source ProjectorNext.Calibration Gauss Next.Rank Normal MvPolynomial
open Feyn Gauge LatticePT PertExtension.Orb Chart Stems PertExtension.Series.Tested Finset Interval
open Pert.Orb (formElem covar image takeDiv gZ positiveLinks wilson Potential form formL curL dLin bridgeEquiv)
open scoped Topology ContDiff BigOperators Classical RealInnerProductSpace
variable {G:Gauge} {n:Side} (q:ℕ+)(hq:1<q.val)
local notation "E"=> Potential G n
local notation "J"=> Jam n G
variable (x y:Jam n G)

def dev (x y:J):ℝ:= if y.1.2=x.1.2 ∧ y.2=x.2 then green (y.1.1-x.1.1) else 0
lemma green_neg (x:Site n): green (-x)=green x:= by rw [green,Pert.Full.toroid_even];rfl
def sale : Symmetric J where
   cov x y:= (dev x y:ℂ)
   symm x y:= by apply congr_arg; by_cases h:y.1.2=x.1.2∧y.2=x.2; rw [dev,dev,if_pos h,if_pos ⟨h.1.symm,h.2.symm⟩,← green_neg, neg_sub];rw [dev,dev,if_neg h,if_neg (fun h'=> h ⟨h'.1.symm,h'.2.symm⟩)]

def reverseK (x:J):J:= (Pert.Orb.image x.1,x.2)
def east (x y:J):ℝ:= dev (reverseK x) y
lemma water_dev (x y:J): water.cov x y=(↑(dev x y - east x y):ℂ):= by
   change (↑(cost.wick (pier x) (pier y)):ℂ)= _; apply congr_arg; let A:= fun i:J=>LatticePT.colorBasis i.2; have he (i:J): pier i=formElem i.1 (A i):= by
      ext1 v; change v.val i.1 i.2=inner ℝ (v.val _) _; rw [real_inner_comm]; exact (EuclideanSpace.basisFun_inner ..).symm
   rw [covar_eq,he,he,Pert.Orb.covar_link] -- edit
   have hy : inner ℝ (A x) (A y)= if y.2=x.2 then 1 else 0:= (real_inner_comm ..).trans ((EuclideanSpace.basisFun _ ℝ).inner_eq_ite ..)
   unfold east dev reverseK; rw [hy]; simp only [Pert.Orb.image,Prod.fst,Prod.snd]; have ht:y.1.1 - (-x.1.1-step x.1.2)= y.1.1 + x.1.1 + step x.1.2:= by abel
   rw [ht]; by_cases h:x.2=y.2 <;> by_cases v:y.1.2=x.1.2<;> simp [h,v,Ne.symm,green]

abbrev innerFace (p:Face (Per n)):= PertExtension.LatticePT.Projection.fold n p -- check namespace

def follow (z : Site n)(x:J):J:= ((x.1.1+z,x.1.2),x.2)
lemma follow_place (u: Site n) {o:Site n}(p:Hair G): follow u (place o p)=place (o+u) p:= by unfold place follow west; congr 2; exact add_assoc ..
lemma sale_follow (u:Site n): sale.cov (follow u x) (follow u y)= sale.cov x y:= by simp [sale,dev,follow]
def thermal (Q:Symmetric J) (o p:Site n)(x y:Hair G):= Q.cov (place o x) (place p y)
lemma self_thermal (K:Symmetric J)(o : Site n)(x y:Hair G): thermal K o o x y=(scopedK K o).cov x y:= (match_name (place o) _ x y).symm
lemma sale_self (j : Site n): scopedK sale j=scopedK (sale (G:=G) (n:=n)) 0:= by
   ext1; funext x y; simp_rw [←self_thermal]; unfold thermal; nth_rw 1 [←zero_add j]; rw [← follow_place, ← show follow j (place 0 y)= place j y from Eq.trans (follow_place j y) (congr_arg (fun v=>place v y) (zero_add _)), sale_follow]

end YM.PositionX.Hinge
