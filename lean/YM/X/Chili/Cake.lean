import YM.X.Chili.Bounty
/-!
# Cost algebra for local dynamic symbols at variable frames. Ext gets actual shell admissible direction. Thick grade estimates, no limit required at z≈origin. Uses normalized ∗actual-subtract* residual Visa.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Clove
open Lattice Wilson Next.Rank CellsInt Beamer Interval PertExtension LatticePT Normal Filter Set Function Metric MeasureTheory Asymptotics
open Reed Stems Fielding Print Braid Grow Haze MvPolynomial Finset LiftMark
open scoped Topology ContDiff BigOperators Classical
variable {q : ℕ+} (hq:1<q.val) {k m n d:ℕ} {G:Gauge} {R:ℝ}
local notation "Fℕ"=>(atTop:Filter ℕ)
/-! 
# cost algebra multiplication.
-/
variable {A:ℕ→Brush G}{f B:Rich G}{p s:Deck G}
private lemma heat_ceil {i j k:ℕ}{m:ℤ}{x y:Mist ℂ}(h:Visa q R (i:ℤ) (i-m:ℤ) x)(he:Visa q R (j:ℤ) (j-(n:ℤ)) y)(ht:k ≤ i + j)(hr:0≤R)(hq:1<q.val): Visa q R (k:ℤ) ((k:ℤ)-(m+n)) (x*y):= Visa.stretch hq (h.mulC he) hr (by omega) (by omega)
include hq in
private lemma cake_step (hr:0≤R)(hb:Grasp B)(h:Grove q R A B d m p) {f:Mist ℂ}(he:Visa q R ↑(d+1) (((d+1:ℕ):ℤ)-n) f) : Visa q R ↑(d+1) (((d+1:ℕ):ℤ)-(m+n:ℕ)) (cake d (emerge q B) p*f):= by
   rw [cake_id,Finset.sum_mul, Nat.cast_add m n]; apply Visa.counts; intro j hj; exact heat_ceil (impression h hb (by simpa using hj : j≤d)) he (by omega) hr hq
include hq in
lemma Grove.mul (hr:0≤R)(hb:Grasp B)(h:Grove q R A B d m p)(ht:Grove q R A B d n s): Grove q R A B d (m+n) (p*s):= by
    constructor
    · intro f hf i hi; rw [wreath_mul _ _ _ hi, Nat.cast_add m n]; apply Visa.counts; intro j hj; apply Visa.counts; intro k hk; split
      next hy=> exact Visa.stretch hq (Visa.mulC (imprint h hf (by simpa using hj : j≤d)) (imprint ht hf (by simpa using hk : k≤d))) hr (by omega) (by omega)
      exact Visa.zero
    let x:= exitP A p; let y:= exitP A s; let f:=emerge q B; let a:= cake d f p; let b:=cake d f s; let c:= cake d f (p*s); let w:= (m+n :ℕ); let U(v: Mist ℂ):= Visa q R ↑(d+1) (((d+1:ℕ):ℤ)-(w:ℤ)) v; rw [exit_mul]; have hx : U (a*b-c):= by
         change Visa q R _ _ (cake d f p * cake d f s - cake d f (p*s)); rw [exit_high]; unfold w; rw [Nat.cast_add m n]; apply Visa.counts; intro i hi; apply Visa.counts; intro j hj; split
         next he=> exact heat_ceil (impression h hb (show i≤d from by simpa using hi)) (impression ht hb (show j≤d from by simpa using hj)) he hr hq -- sum i+j
         exact Visa.zero
    change U (x*y-c); rw [show x*y-c= (x-a)*(y-b) + b*(x-a)+a*(y-b)+(a*b-c) by ring]; refine Visa.add (Visa.add (Visa.add ?_ ?_) (cake_step hq hr hb h ht.2)) hx
    · unfold w; rw [Nat.cast_add m n]; exact heat_ceil h.2 ht.2 (by omega) hr hq
    unfold w; rw [Nat.add_comm m n]; exact cake_step hq hr hb ht h.2
lemma Grove.constant {f:Mist ℂ}(h:Visa q R 0 (-(m:ℤ)) f): Grove q R A B d m (fun i z=> C (f i z)):= by
    constructor; intro y hy i hi
    · have he(x:ℂ): leaf (vapor G) i (trumpet (Okay G) (valP (G:=G)) d (C x))= if i=0 then C x else 0:= by
          rw [(show trumpet (Okay G) valP d (C x)= C x from by unfold trumpet; rw [MvPolynomial.aeval_C,MvPolynomial.algebraMap_eq])]; split
          next h=> exact (h.symm ▸ (show IsWeightedHomogeneous (vapor G) (C x) 0 from isWeightedHomogeneous_C ..)).weightedHomogeneousComponent_same
          next h=> exact (isWeightedHomogeneous_C (vapor G) x).weightedHomogeneousComponent_ne _ h
      by_cases hk:i=0; · subst i; unfold wreath; simp only [he, ↓reduceIte]; simp only [probeL,aeval_C,Nat.cast_zero,zero_sub]; exact h
      unfold wreath; simp_rw [he, if_neg hk,map_zero]; exact Visa.zero
    have hp(x:ℂ): bloom d (C x)=C (σ:= Valves G) x:= by
        change level (vapor G) d (trumpet _ (valP (G:=G)) _ _) = _; rw [(show trumpet (Okay G) valP d (C x)= C x from by unfold trumpet; rw [MvPolynomial.aeval_C,MvPolynomial.algebraMap_eq])]; exact trimmer_hom (Nat.zero_le _) (isWeightedHomogeneous_C ..)
    have he : cake d (emerge q B) (fun i z=> C (f i z))=f:= by funext i z; rw [cake,hp]; exact (probeL _).commutes _
    rw [he,show exitP A (fun i z=> C (f i z))=f from funext fun i=> funext fun z=> (snap (A i)).commutes _,sub_self]; exact Visa.zero
end YM.PositionX.Clove
