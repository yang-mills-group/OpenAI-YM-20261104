import YM.AllOrder.Plateau.Reflex
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Plateau.Slim
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure PhysicalNext Repeat Lapis Bid Planned.JetPort
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush Poll ConnectedActivityE6.Coat
open Song AbsoluteSums Fare Shellac Work.G05
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Sienna
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G: Gauge} {n m: Side} {k j w N : ℕ}
variable {σ C Z β x₀:ℝ} (p:BudgetPoint)
local notation "E"=>Positions (Primary n G)
open Animals Trio Slide Marlin
section compressed
variable (W:ℕ)(f:Offer G n)
abbrev turnS (u:Seat n):Equiv.Perm (Site n):= Push.Local.turnSites u.1 u.2
def paid (f:Offer G n): Offer G n:= fun x=> ∑ θ:Seat n, choir f (θ,(turnS θ).symm x)
local notation "P"=>paid f
local notation "Q"=>sea (c:=n) W
abbrev tagS (θ: Seat n)(i:Site n):Door n:= (θ,(turnS θ).symm i)
abbrev θdoor (θ : Seat n)(i:Site n):= tagS θ i
lemma scene (i:Site n)(s:Seat n): s.spread (neighbors W i)= neighbors W (turnS s i):= by ext1 p; obtain ⟨x,hx⟩:= (turnS s).surjective p; rw [← hx]; change turnS s x∈ (neighbors W i).image (turnS s) ↔_; simp only [mem_image,neighbors_mem,EmbeddingLike.apply_eq_iff_eq]; change (∃ a,separation i a ≤ W ∧ a=x) ↔ separation _ _ ≤ W; simp [turnS]
lemma placed (i:Site n)(s:Seat n): Q (θdoor s i)= Marlin.leap W i:= by
 cases ha: θdoor s i with | mk j i' =>
 have h : j=s ∧ i'=(turnS s).symm i:= by injection ha with h h'; exact ⟨h.symm,h'.symm⟩ -- injection order
 rcases h with ⟨h,rfl⟩; subst j; unfold sea Song.revolve Song.line Marlin.leap; simp only; change ({ site:= turnS s _, support:= _,anchor:= _ } : RegularAddress n) = _; congr; · exact (turnS s).apply_symm_apply i
 rw [scene, (turnS s).apply_symm_apply]
include W f
lemma whirl_s (x: Site n)(s:Signed)(b:Site n)(u:Seat n): whirl s b (θdoor u x)=θdoor (Seat.move s b u) (affine s b x):= by
 let t:= Seat.move s b u; refine Prod.ext rfl ?_; have hh := (Song.spirit (G:=G) (Marlin.leap (c:=n) W) f s b (θdoor u x)).1; change turnS t _=affine s b (turnS u ((turnS u).symm x)) at hh; rw [Equiv.apply_symm_apply] at hh; exact (Equiv.eq_symm_apply (turnS t)).mpr hh -- typo
include W
lemma paid_turn : Mirrors P:= by intro x s b V; unfold paid; rw [Finset.sum_apply,Finset.sum_apply]; symm; rw [← Equiv.sum_comp (Seat.move s b) (fun v:Seat n=> choir f (tagS v (affine s b x)) V)]; apply Finset.sum_congr rfl; intro i _; rw [show tagS _ _= _ from (whirl_s W f x s b i).symm, (spirit (Marlin.leap (c:=n) W) f s b (θdoor i x)).2.2]; rfl -- `W` parameter appears unused block binder? need include
-- one-piece cost orientation independent of θ.count (true early), no further area expense.
lemma rooted (H: Meadow.Budget p (Marlin.leap (c:=n) W) f C): Meadow.Budget p (Marlin.leap (c:=n) W) P (turnFee p*C):= by
 obtain ⟨b,h,hb⟩:= H; obtain ⟨hc,hB⟩:= spiral (Marlin.leap (c:=n) W) f b (fun i=>(hb i).1) (fun i=>(hb i).2) h
 let c(i:Site n)(θ:Seat n):= Song.Rim n*(turnFee p*b ((turnS θ).symm i)); let P' (i:Site n):=P i; let Z (x:Site n):= ∑ θ: Seat n,c x θ
 have hz(x:Site n): p.Regular (Marlin.leap W x|>.support) (P' x)∧ p.supBounds (Marlin.leap W x|>.site) (Marlin.leap W x|>.support) (P' x) (Z x):= by
    have h(i:Seat n):= hc (tagS i x); have ht(i:Seat n): Q (tagS i x)= Marlin.leap W x:=placed W x i;
    refine ⟨Meadow.regularA _ fun i _=> ?_,Trio.sup_S p _ _ univ _ _ (fun i _=>?_) fun i _ =>?_⟩; exact congr_arg (fun q:RegularAddress n=>p.Regular q.support (choir f (tagS i x))) (ht i) ▸ (h i).1; -- maybe use show
    · rw [← ht i] -- W binder cope; check
      exact (h i).1
    rw [← ht i]; exact (h i).2
 refine ⟨Z,fun x=>budget_finite ?_ ?_,hz⟩;
 · intro i; split; exact mul_nonneg ((hz i).2.1) (Real.exp_pos _).le; rfl
 rw [Finset.sum_eq_single x]; rw [if_pos (show (Marlin.leap W x).site=x from rfl)];
 · have he : Injective (fun θ:Seat n=> tagS θ x):= fun i j h=>congr_arg Prod.fst h
   have ht := budget_pull (fun θ:Seat n=> tagS θ x) he (hB x); apply le_trans _ (budget_sum ht univ); unfold Z; rw [Finset.sum_mul]; apply Finset.sum_le_sum; intro v hv; change c x v * _ ≤ if (Q (tagS v x)).site=x then c x v * Real.exp (_*coverNumber p.B (Q (tagS v x)|>.support)) else 0; rw [placed, if_pos rfl]
 · exact fun i _ he=>if_neg he
 simp
lemma masked_slim (U:Config G n): (∑ i:Site n, masked p.threshold (neighbors W i) (paid f i) U)= ∑ i:Door n, masked p.threshold (Q i|>.support) (choir f i) U:= by
 unfold paid; have h (i: Site n): masked p.threshold (neighbors W i) (∑ θ:Seat n, choir f (tagS θ i)) U=∑ θ:Seat n, masked p.threshold (Q (tagS θ i)|>.support) (choir f (tagS θ i)) U:= by
    simp_rw [placed W i]; change masked p.threshold (neighbors W i) _ U= ∑ θ:Seat n, masked p.threshold (neighbors W i) (choir f (tagS θ i)) U; by_cases he:Healthy p.threshold (neighbors W i) U; · simp_rw [masked_eq _ _ _ _ he]; rw [Finset.sum_apply]
    simp_rw [masked_ne _ _ _ _ he]; rw [sum_const_zero]
 change (∑ i:Site n, masked p.threshold (neighbors W i) (∑ θ:Seat n, choir f (tagS θ i)) U)=_; simp_rw [h]; rw [Finset.sum_comm]; conv_rhs=> rw [Fintype.sum_prod_type]
 refine Finset.sum_congr rfl fun v _=> Equiv.sum_comp (turnS v).symm (fun i=>masked p.threshold (Q (v,i)|>.support) (choir f (v,i)) U)
lemma pocket (U:Config G n) : (Trio.froth (paid f)) U= Patch.average fun θ: Seat n=> (Trio.froth f) (θ.view U):= by
 unfold Trio.froth paid; simp_rw [Finset.sum_apply]; rw [Finset.sum_comm,Patch.average, Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; unfold Song.choir; simp_rw [Pi.smul_apply,smul_eq_mul,← Finset.mul_sum]; exact congr_arg (Song.Rim n*·) (Equiv.sum_comp (turnS i).symm (fun v=> f v (i.view U)))
end compressed
end YM.AllOrder.Plateau.Slim
