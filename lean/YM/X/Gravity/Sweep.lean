import YM.X.Local.Oar
import YM.X.Shelf.Finite
import YM.X.Grow.GaugeJet
/-!
# Remote gradient prices separate modulo actual curvature shell lift on open Book space.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Gravity
open Lattice Wilson Next.Rank Normal Interval PertExtension LatticePT Filter Set Function Metric MeasureTheory Asymptotics Reed Size Braid
open MvPolynomial Hinge Clove Haze Grow Shelf Ocean Fielding Crystal Perch LiftMark
open Stems hiding X
open scoped Topology ContDiff BigOperators Classical
variable {q: ℕ+}(hq:1<q.val){V:Type*}{k m n d l:ℕ}{G:Gauge}{R r:ℝ}
local notation "X"=>MvPolynomial.X
local notation "K"=> Book G
def sleet (G:Gauge)(d:ℕ):Submodule ℂ (Book G):= restrictSupport ℂ {a| Finsupp.weight (vapor G) a≤d} -- all cost profiles
private lemma exhaust_wind (G:Gauge)(d:ℕ): Set.Finite {b: Valves G→₀ℕ| Finsupp.weight (vapor G) b ≤ d}:= by
   let A:= {b: Valves G→₀ℕ| Finsupp.weight (vapor G) b ≤ d}; let f:= vapor G
   let I:= Sigma (fun i:Fin d=> Grow.Pick (Okay G) i.val); let u(x:I): Valves G := ⟨x.1.val,x.2⟩
   have H(i:Valves G)(b:A): b.val i*f i ≤ d:= by
       refine le_trans (b:= Finsupp.weight (vapor G) b.val) ?_ b.property
       by_cases hx:b.val i=0
       · rw [hx]; simp
       rw [Finsupp.weight_apply,Finsupp.sum]; exact Finset.single_le_sum (f:=fun x=> b.val x • vapor G x) (fun _ _=> Nat.zero_le _) (Finsupp.mem_support_iff.mpr hx)
   have he(i): 1≤ f i:= by unfold f vapor gear; omega
   have ht(i)(b:A): b.val i≤ d:= (le_mul_of_one_le_right (Nat.zero_le _) (he i)).trans (H i b)
   let e (b:A)(i:I):Fin (d+1):= ⟨b.val (u i),Nat.lt_succ_of_le (ht _ _)⟩; apply (Finite.of_injective e ?_ : Finite A); intro b c h; apply Subtype.ext; apply Finsupp.ext; intro x; by_cases hx:x.1<d; · exact congr_arg Fin.val (congr_fun h ⟨⟨x.1,hx⟩,x.2⟩)
   have hg (b:A): b.val x=0:= by by_contra! hk; have hz : f x ≤ d:= ((le_mul_of_one_le_left (Nat.zero_le _) (Nat.one_le_iff_ne_zero.mpr hk)).trans (H x b)); unfold f vapor gear at hz; omega
   rw [hg,hg]
instance (G:Gauge)(d:ℕ): FiniteDimensional ℂ (sleet G d):= by
   haveI : Finite {b : Valves G→₀ℕ | Finsupp.weight (vapor G) b ≤ d}:= exhaust_wind G d; exact Module.Finite.of_basis (MvPolynomial.basisRestrictSupport ℂ {b : Valves G →₀ℕ| Finsupp.weight (vapor G) b ≤ d})
def watch (G:Gauge)(d:ℕ):Module.End ℂ (Book G):= (localMap (E:=Okay G) (F:=Okay G) (rightCur (G:=G))).toLinearMap -- use d?
@[simp] lemma watch_twice (p:Book G)(d:ℕ):watch G d (watch G d p)=watch G d p:=by
   change localMap (E:=Okay G) rightCur (localMap (E:=Okay G) rightCur p) = _; rw [← slots,← slots p]; change rich (lessJob (rich (lessJob p)))=localMap (E:=Okay G) rightCur p; rw [strict,slots]
abbrev partX (G:Gauge)(n:ℕ):= MvPolynomial.weightedHomogeneousSubmodule ℂ (vapor G) n
def saddleX (G:Gauge)(n:ℕ):Submodule ℂ (Book G):= partX G n ⊓ LinearMap.ker (watch G n)
lemma rings_hom (p:Book G): p∈partX G n↔IsWeightedHomogeneous (vapor G) p n:= by exact Iff.rfl
lemma part_le (G:Gauge)(n:ℕ): partX G n ≤ sleet G n:= fun p hp=> (level_ok _ _).mpr (trimmer_hom (le_refl n) ((rings_hom p).mp hp))
instance (G:Gauge)(n:ℕ): FiniteDimensional ℂ (partX G n):= FiniteDimensional.of_injective (Submodule.inclusion (part_le G n)) (Submodule.inclusion_injective _)
instance (G:Gauge)(n:ℕ): FiniteDimensional ℂ (saddleX G n):=FiniteDimensional.of_injective (Submodule.inclusion (show saddleX G n≤partX G n from inf_le_left)) (Submodule.inclusion_injective _)
set_option maxHeartbeats 600000 in
lemma leaf_watch (d:ℕ)(p:Book G): leaf (vapor G) k (watch G d p)=watch G d (leaf (vapor G) k p):= by let F:= localMap (E:=Okay G) (F:=Okay G) (rightCur (G:=G)); have he:= local_hom (E:=Okay G) (F:=Okay G) (rightCur (G:=G)); have hz:= Maxwell.Free.commuting (vapor G) (vapor G) F he p k; exact hz
end YM.PositionX.Gravity
