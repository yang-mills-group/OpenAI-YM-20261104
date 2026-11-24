import YM.X.Braid.Gamma
/-!
K row seam identity in the lifted Haar covariance (sale). Constant removed INCLUDED as a cover gradient so horizontal contraction pays alias token exactly. Lattice units.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Braid
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter MeasureTheory Metric Finsupp
open Stems Reed Interval Hinge CellsInt
open scoped Topology ContDiff BigOperators Classical
variable {V:Type} {n:Side}{k m:ℕ}{G:Gauge}
local notation "P"=> Normal.poly V
local notation "R"=> Hair G →₀ ℝ
local notation "H"=> Hair G
local notation "Q"=> scopedK (sale (n:=n) (G:=G)) (0:Site n) -- deck
variable (x y:Hair G) (g f:Fan G)(A:Brush G)
abbrev flow (G:Gauge)(n:Side):= scopedK (sale (n:=n) (G:=G)) (0:Site n)
def cane (n:Side)(x y:Cover):ℝ:= green (wrap n x-wrap n y)
def tau (n:Side)(x y:Hair G):ℝ:= if x.2=y.2∧ x.1.2=y.1.2 then cane n x.1.1 y.1.1 else 0
lemma rτ (n:Side): (flow G n).cov x y=Complex.ofReal (tau n x y):= by rw [← self_thermal,thermal]; rw [sale.symm]; change Complex.ofReal (dev (place (0:Site n) y) (place (0:Site n) x))=_; unfold dev tau cane; simp [place,west,and_comm] -- by_cases h:x.2=y.2∧x.1.2=y.1.2; rw [if_pos h,if_pos (show (place (0:Site n) y).1.2=(place 0 x).1.2∧ _ from ⟨h.2.symm,h.1.symm⟩)]; simp [place,west,← neg_sub (wrap n x.1.1) (wrap n y.1.1),green_neg]; rw [if_neg h,if_neg (fun h'=> h ⟨h'.2.symm,h'.1.symm⟩)]
lemma tau_swap (n:Side): tau n x y=tau n y x:= Complex.ofReal_injective ((rτ x y n).symm.trans (((flow G n).symm ..).trans (rτ y x n)))
def paints (n:Side) : R →ₗ[ℝ] Brush G:= textL.symm.toLinearMap ∘ₗ Finsupp.linearCombination ℝ (tau n)
lemma text_paints (n:Side)(x:H): text (paints n g) x=Finsupp.linearCombination ℝ (tau n x) g:= by
   change (linearCombination ℝ (tau n) g x)=_; induction g using Finsupp.induction_linear with
   | zero=> simp
   | add g p hg hp=> simp [_root_.map_add, hg,hp]
   | single x' c=> rw [linearCombination_single,linearCombination_single, Pi.smul_apply,tau_swap]
lemma pencil (n:Side): linearCombination ℂ (flow G n).cov (com g)= Complex.ofReal ∘ text (paints n g):= by
   funext x; change LinearMap.proj («R»:=ℂ) x (linearCombination ℂ _ _)= _; rw [LinearMap.map_finsupp_linearCombination]; rw [comp_apply,text_paints];
   rw [show ((LinearMap.proj («R»:=ℂ) x) ∘ (flow G n).cov)=Complex.ofReal ∘ tau n x from funext (fun y=> ((flow G n).symm y x).trans (rτ x y n))]; exact com_read _ _
lemma palette (n:Side): edge (flow G n) (com g)= stroke (paints n g):= by rw [edge,pencil];rfl
lemma cornered : treats (flow G n) (com g) (com f)= ↑(flatL (paints n g) f:ℂ):= by rw [treats,pencil]; exact com_read ..
lemma commute (n:Side):flatL (paints n g) f= flatL (paints n f) g:= Complex.ofReal_injective ((cornered g f).symm.trans ((treats_comm ..).trans (cornered f g)))
def sun (p:Cover)(i j:Axis)(k:G.ColorIndex): Fan G:= arc k p i j
lemma sun_at (p:Cover)(i j:Axis)(k:G.ColorIndex): flatL A (sun p i j k)= Reed.curlL i j A p k:= by rw [sun,flatL,arc_eq, Reed.curling]
def keyRow (i:Hair G): Fan G:= ∑ a:Axis,(sun (i.1.1-step a) a i.1.2 i.2 - sun i.1.1 a i.1.2 i.2)
lemma reading (x:Hair G): flatL A (keyRow x)= orderK x.1.2 A x.1.1 x.2:= by
    let i:=x.1.1; let F:=fun a: Axis=> curlL a x.1.2 A
    rw [keyRow,map_sum]; simp only [map_sub, sun_at]; rw [orderK, LinearMap.neg_apply,LinearMap.sum_apply, Pi.neg_apply, Finset.sum_apply,PiLp.neg_apply];
    rw [show ∀ f:Axis→G.Color,(∑ i,f i).ofLp x.2= ∑ i,(f i).ofLp x.2 from fun f=> map_sum (EuclideanSpace.proj x.2:G.Color→L[ℝ] ℝ) f Finset.univ, ← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro a _; change _= -(stepValue (F a) a (i-step a) x.2); unfold stepValue; rw [sub_add_cancel]; rw [PiLp.sub_apply];change (F a (i-step a) x.2) - (F a i x.2)=_; ring

-- K output as minus scalar Lap plus grad.
omit x y g f
private lemma backward {V:Type}[NormedAddCommGroup V](f:Cover→V)(i:Axis)(z:Cover): rewind f i z=f z-f (z-step i):= by unfold rewind stepValue; rw [sub_add_cancel]
private lemma rewind_commute(i j:Axis){V:Type}[NormedAddCommGroup V](z:Cover)(f:Cover→V): rewind (stepValue f j) i z= stepValue (rewind f i) j z:= by
   change stepValue (stepValue f j) i (z-step i)=_; rw [hop]; unfold stepValue rewind; rw [show z-step i+step j=z+step j-step i by abel]; rfl
lemma key_split (z:Cover)(j:Axis):orderK j A z = -(∑ i:Axis, rewind (stepValue (raising j A) i) i z)+ ∑ i:Axis, stepValue (rewind (raising i A) i) j z:= by
    rw [orderK,LinearMap.neg_apply,LinearMap.sum_apply, Pi.neg_apply, Finset.sum_apply]; simp only [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _; change -(rewinds i (stepValue (raising j A) i-stepValue (raising i A) j) z)= _; rw [map_sub,Pi.sub_apply]; change - (rewind _ _ _-rewind _ _ _)= _; rw [rewind_commute i j]; abel
end YM.PositionX.Braid
