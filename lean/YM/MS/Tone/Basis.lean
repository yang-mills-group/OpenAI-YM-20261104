import YM.MS.Tone.CoreSphere
import YM.MS.PlaneSimple
/-!
# Actual master-QME at origin of cover flow

For both marked and unmarked. Terms per order-n. Use scaled initial action from a run
 Tape `p`. Kernel polynomials of native positions. Still need estimative cost propagation
 after solving high. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Tone.Frame
open Function Filter Set Finset Plane Koszul Cylinder Lab Taylor Lattice Native Bare Focus Landau Momentum Orient Draft Sew Native.Chart
open Book Convolve Program Flux Native.Wilsonian
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge} (p:Team) (x:ℝ) (F: T (Dot G Cover)) {k:ℕ} {q:ℤ}

lemma Vin (F: Score G Axis QP) (h:Symm (field parity) F): tree parity (Kzone G) (s₀ G) F= (send wave).raise F:= singleFac (s₀ G) core_rank F _ (fun i k=> put_in F k i.1 i.2) h

lemma commute_roles (F H: Dot G Cover) (h:Tuned F 0) (hh:Tuned H 0) (l:List (LightMode G QP)) (he:net l=0): tree parity (Kzone G) (run F) (run H) l= tree parity (Kzone G) (run H) (run F) l:= by
    rw [← touching,← touching]; apply consent _ _ _ l he
    filter_upwards [dutyBV_root (Spectrum G) F H true,dutyBV_root (Spectrum G) H F true] with n hv hm; change duty true n _=duty true n _; rw [hv,hm]; refine link_commute _ ?_ ?_
    · change Pure (field parity) false (sumHome (shown n F)).val; rw [total_uses]; exact (Tune.sum _ (fun i _=> ((h.move (wrap n)).move (fun z=> i+z)))).parity ghostParity
    change Pure (field parity) false (sumHome (shown n H)).val; rw [total_uses]; exact (Tune.sum _ (fun i _=> Tune.move (fun z=>i+z) (hh.move (wrap n)))).parity ghostParity
-- account path. Want I<n from d.
lemma canon_sub {E : Type}[AddCommGroup E] (f :ℕ→ℕ→E) (k:ℕ) : (∑ i∈antidiagonal k, f i.1 i.2)= f 0 k+∑ j∈Domain.paths k 0,f (k-j) j := by
    rcases k with _|k; simp [Domain.paths]
    rw [Finset.Nat.sum_antidiagonal_succ]; congr 1;
    rw [← Finset.Nat.sum_antidiagonal_swap]; unfold Domain.paths; change (∑ p∈antidiagonal k, f (p.2+1) p.1)=_; rw [← Finset.range_eq_Ico, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun p q=> f (q+1) p)] -- paths
    refine Finset.sum_congr rfl fun j hj=> ?_; congr! 1; simp only [Finset.mem_range] at hj; omega
lemma canon_corner {E: Type}[AddCommGroup E](f:ℕ→ℕ→E) (k:ℕ) (h:0< k): ∑ i∈antidiagonal k, f i.1 i.2=f 0 k+f k 0+∑ j∈Domain.paths k 1,f (k-j) j:= by rw [canon_sub, show Domain.paths k 0=insert 0 (Domain.paths k 1) by ext; simp only [Domain.paths, Finset.mem_Ico,Finset.mem_insert]; omega,Finset.sum_insert]; simp [add_assoc]; simp [Domain.paths]

lemma plane_core (h:G.Simple) (l:List (LightMode G QP)) (he:net l=0) (hi:0<k):
     let A:= promote run (style G p x)
     (send wave).raise (A k) l+cycle (Kzone G) μzone (A k) l+ (1/2:ℂ)*(∑ j∈Domain.paths k 1, tree parity (Kzone G) (A (k-j)) (A j) l)=0:= by
    intro A; let Q := style G p x; have ht i : Tuned (Q i) 0:= (core_circle G p).actual i x
    have hM : run (masterE (Spectrum G) (style G p x) k) l=0:= by rw [consent _ _ ((main_law G p x h) k) _ he]; simp
    change run ((Spectrum G).Lap (Q k)+(1/2:ℂ) • (∑ i∈antidiagonal k,(Spectrum G).touch (Q i.1) (Q i.2))) l=0 at hM
    have hc : Symm Draft.DotFlip (A k):= tied.sym (Q k) (ht k).symm; have hf : A 0=s₀ G:= congr_arg run (whoZero ..)
    simp only [map_add,map_smul,map_sum,Pi.add_apply,Pi.smul_apply,Finset.sum_apply,smul_eq_mul, lapC (Q k) (ht k).symm,touching] at hM
    change cycle _ _ (A k) l+(1/2:ℂ)*(∑ i∈antidiagonal k,tree parity (Kzone G) (A i.1) (A i.2) l)=0 at hM
    rw [canon_corner (fun a b=>tree parity (Kzone G) (A a) (A b) l) _ hi,show tree parity (Kzone G) (A k) (A 0) l = tree parity (Kzone G) (A 0) (A k) l from commute_roles _ _ (ht k) (ht 0) l he, hf, Vin _ hc] at hM
    linear_combination hM
lemma plane_mark (H0:Weightless (Spectrum G) (style G p x) F) (hp:∀ i,Tuned (F i) q) (l:List (LightMode G QP)):
     let A:= promote run (style G p x); let B:= promote run F
     (send wave).raise (B k) l+ cycle (Kzone G) μzone (B k) l+ (∑ j∈ Domain.paths k 0, tree parity (Kzone G) (A (k-j)) (B j) l)=0:= by
    intro A B; have hv : ((Spectrum G).Lap (F k))+∑ i∈antidiagonal k,(Spectrum G).touch (style G p x i.1) (F i.2)=0:= congr_fun H0 k;
    replace hv := congr_arg (fun v=> run v l) hv; simp only [map_zero,Pi.zero_apply, map_add,map_sum, Finset.sum_apply,Pi.add_apply,touching,lapC (F k) (hp k|>.symm)] at hv
    rw [canon_sub (f:=fun i j=> tree parity (Kzone G) (run (style G p x i)) (run (F j)) l),show style G p x 0=core G 0 from whoZero ..,show tree parity (Kzone G) (run (core G 0)) (run (F k))= _ from Vin _ (tied.sym _ (hp k|>.symm))] at hv
    unfold B A; simp_rw [promised]; linear_combination (norm:=abel) hv
end YM.MS.Tone.Frame
