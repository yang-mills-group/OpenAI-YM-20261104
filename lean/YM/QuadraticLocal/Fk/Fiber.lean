import YM.Comparison.RG02.Order.Vacancy
/-!
# Coefficient powers & common normalization under mark-algebra mapping

Keep coupling-order polarization Board, change names and budgets.Maybe project on new
assignment of markers per root/site, with multiplicity if the owner Census permits it.
General lemma: choose before generating any coefficient data.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Morph
open YM.Marker YM.Multi YM.Primitives.GCC.Anchor
open YM.Extra.Trajectories (connected connected_quiet pass_connected)
open YM.Comparison.RG02
open YM.Comparison.RG02.Cumulants
open Finset Function Order Order.Join
open scoped BigOperators Classical
variable {V W : Type} [DecidableEq V] [DecidableEq W] [Fintype V] [Fintype W]
variable {R : Census V} {S : Census W} {k:ℕ}
set_option quotPrecheck false
variable (F:Poly R →ₐ[ℂ] Poly S) (h:∀x,(F x).part S.quiet=x.part R.quiet)
variable (P : Grade R k)
abbrev Observe (i:Index k) : Poly R:= Poly.inject (fun x=> P.part (Join.pair x i))
local notation "A"=> Grade R k
local notation "K"=>Grade S k
local notation "Q" p:max i:max => Morph.Observe p i
lemma shows {a b:Grade R k}(he:∀ i:Index k,Morph.Observe a i=Morph.Observe b i):a=b:= both_parts fun x i=> congr_arg (fun p=> Poly.part p x) (he i)
variable (k)
def baseL : Grade R k →ₗ[ℂ] Grade S k where
   toFun x:= Poly.inject fun i=>( F (Morph.Observe x (Join.right i))).part (Join.left i)
   map_add' a b:= by apply Poly.ext; intro i; exact congr_arg (fun x:Poly S=>x.part (Join.left i)) (F.map_add (Morph.Observe a (Join.right i)) (Morph.Observe b (Join.right i)))
   map_smul' c a:= by apply Poly.ext; intro i; exact congr_arg (fun x:Poly S=>x.part (Join.left i)) (map_smul F c (Morph.Observe a (Join.right i)))
variable {k}
local notation "U"=> baseL k F
variable (i:Index k)
lemma crest : Morph.Observe (U P) i= F (Morph.Observe P i):= by ext x; change (F (Morph.Observe P (Join.right (pair x i)))).part (Join.left (pair x i))= _; rw [Join.left_pair,Join.right_pair]
lemma neutral : Morph.Observe (1 : Grade R k) i= if i=(indices k).quiet then 1 else 0:= by
 ext x; change (1 : Grade R k).part (pair x i)=_; rw [one_pair]; by_cases h:i=(indices k).quiet <;> simp [h, Poly.one_part]
local notation "P!"=> Index k
local notation "B"=> Board R k
variable (Y : Grade R k)
local notation "ℓ"=> (P! × P!)
local notation "yℓ"=> Poly.merges
lemma convolution : Morph.Observe (P*Y) i=∑ j:Index k,∑ v:Index k, if Poly.merges j v i then Morph.Observe P j*Morph.Observe Y v else 0:= by
 ext1 s; change (P*Y).part (Join.pair s i)= _; rw [Join.pair_product,Finset.sum_comm]; simp_rw [Poly.part_sum]; refine Finset.sum_congr rfl (fun j _ => ?_); -- regroup pl.PHysical.L
 -- order: currently ∑ xPhysical∑yPhysical∑ l. gather
 simp_rw [Finset.sum_comm (s:= Finset.univ (α:=R.Mode)) (t:= Finset.univ (α:=Index k))]; refine Finset.sum_congr rfl fun k₁ _=>?_ ; by_cases h:Poly.merges j k₁ i;
 · rw [if_pos h,Poly.part_mul]; simp_rw [h,and_true]; rfl
 simp_rw [h,and_false,ite_false,sum_const_zero,Poly.part_nil] -- `and_false` syntax
variable (k)
def liftH : Grade R k →ₐ[ℂ] Grade S k:= AlgHom.ofLinearMap (baseL k F)
    (shows fun i=> by rw [crest,Morph.neutral,Morph.neutral]; split <;> simp) (fun a b=> by
           apply shows; intro i; rw [crest,Morph.convolution,Morph.convolution,map_sum]; apply Finset.sum_congr rfl; intro j _; rw [_root_.map_sum]; apply Finset.sum_congr rfl; intro u _; by_cases h:Poly.merges j u i <;> simp [*,crest])
-- authorize threshold, projection.
variable {k}
local notation "L"=> (liftH k F)
lemma issue (u : Index k): Morph.Observe (liftH k F P) u= F (Morph.Observe P u):= crest F P u
lemma even (p:PTable R) : (liftH k F) (Order.series R k p)= Order.series S k (PowerSeries.map F.toRingHom p):= by
 let he {V:Type} [Fintype V][DecidableEq V] (J:Census V) (v:PTable J)(j:Index k) : Morph.Observe (Order.series J k v) j= ((j.val.card.factorial:ℂ)) • PowerSeries.coeff j.val.card v:= Poly.ext (fun x=> Order.polarization J k v x j); apply Morph.shows; intro i'; rw [issue,he, he, map_smul, PowerSeries.coeff_map]; rfl -- instance he.Type universes and factor signatures.
lemma wire (j:ℕ): Order.observe S k ((liftH k F) P) j= F (Order.observe R k P j):= by
 unfold Order.observe; split; next hi=> rw [map_smul]; exact congr_arg _ (issue F P _)
 next=> rw [_root_.map_zero F]
include h
lemma quiet : (liftH k F P).part (Board S k).quiet=P.part (Board R k).quiet:=by
 let i:= (Order.indices k).quiet; have hx: (Observe (liftH k F P) i).part S.quiet= (Observe P i).part R.quiet:= (congr_arg (fun x:Poly S=> x.part S.quiet) (issue F P i)).trans (h (Observe P i)); change _= _; rw [← show Join.pair S.quiet i=(Board S k).quiet from pair_quiet, ← show Join.pair R.quiet i=(Board R k).quiet from pair_quiet]; exact hx
lemma den : Order.denominator (liftH k F P)=liftH k F (Order.denominator P):= by
 let f {V:Type}[DecidableEq V][Fintype V] (J:Census V)(a: Grade J k)(i:Index k): Observe (Order.denominator a) i= Poly.bead J ((Observe a i).part J.quiet):= by apply Poly.ext; intro j; change (Order.bottom J k a).part (pair j i)= (Poly.send J.quiet _).part _; rw [Order.bottom_value,Poly.part_send]; rfl
 apply Morph.shows; intro i; rw [issue F (Order.denominator P),f S,f R,issue,h]; exact (F.commutes _).symm -- projection
include h
lemma heading (hh: Order.UnitLeading P): Order.UnitLeading (liftH k F P):=(quiet F h P).trans hh
lemma rent (hh: Order.UnitLeading P): Order.ratio (liftH k F P)=liftH k F (Order.ratio P):= by
 symm; apply Order.ratio_unique (heading F h P hh); rw [den F h P, ← map_mul, Order.recovers hh]
lemma logarithm (hh: Order.UnitLeading P): Order.logMarked (liftH k F P)=liftH k F (Order.logMarked P):= by unfold Order.logMarked; rw [log_map (liftH k F) (fun y=> quiet F h y) (Order.ratio_quiet hh),← rent F h P hh]
end YM.QuadraticLocal.Morph
