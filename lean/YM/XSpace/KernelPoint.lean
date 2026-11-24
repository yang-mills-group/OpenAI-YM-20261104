import YM.XSpace.Lodges

/-!
# Covariance after scaling (unpositioned). Rate to the Maxwell leg convention.

Compare the **same** finite-regulator graphs at `ConstantCoeff`; no tautology
using a Maxwell reference as order zero. Distinct arities/horizons. SOME moving
profile tests come later; `points` here records shape vectors, not derivatives.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Price
open Lattice Filter Function Set Top Labels Source Source.Drops
open Next.Rank Normal Contraction Finsupp MvPolynomial Configuration Beamer Expense
open Cross (lag extra Centered far Rout Blank readKey)
open scoped Topology BigOperators
variable {G : Gauge} {n : ℕ} (d : Fin n→ℕ)

def ceiling (d : ℕ) (k : Key G): Maxwell.Slot G →₀ ℂ:= if h:generation k≤d then mapper (⟨k,h⟩: KeyIn G d) else 0
lemma roof {d : ℕ} (p : Labels.Label G d): exchange (ceiling d) p.val= Maxwell.observable G d p:=by
  rw [← gathered]; nth_rw 1 [← returns p]
  suffices h : (exchange (ceiling d (G:=G))).comp (rename (Subtype.val : KeyIn G d → _))= exchange mapper from DFunLike.congr_fun h _
  ext1 i; rw [AlgHom.comp_apply,rename_X,exchange_x,exchange_x,ceiling,dif_pos i.property]
lemma roofs {d : ℕ} (p : On.Grade G d): exchange (ceiling d) (preparedL p).val=p.val:=by rw [roof]; exact On.recovers _

def target {z : Points n} (h : z∈conf _) : Cov (Tag G n):= scope (perSlot fun i: Fin n=> ceiling (d i)) (frameX h)
open scoped Classical in
def price (z : Points n) : Cov (Tag G n):= if h:z∈conf _ then target d h else 0
lemma pays {z : Points n} (h : z∈conf n): price (G:=G) d z = target d h:= by rw [price,dif_pos h]

lemma priced (p : ∀ i, On.Grade G (d i)) {z : Points n} (h : z ∈ conf _): Maxwell.Wick.moment G z (fun i=> (p i).val)= Normal.blend (price d z) 0 (output d p):= by
  let f i:= preparedL (p i); let M:= perSlot (fun i : Fin n => ceiling (G:=G) (d i))
  rw [pays d h, Wick_reads h]; simp_rw [← roofs]
  rw [show (∏ i, rename (fun y => (i,y)) (exchange (ceiling (d i)) (f i).val))=exchange M (output d p) from ?_, wets, show reads M 0=0 from funext fun _=> linearCombination_zero_apply ..]; rfl
  unfold output pot; rw [map_prod]; exact Finset.prod_congr rfl fun i _=> (posts (fun i:Fin n=> ceiling (d i)) i _).symm

def Active (p : Tag G n): Prop:= generation p.2≤ d p.1
instance : DecidablePred (Active (G:=G) d) := fun p=> by unfold Active; infer_instance
lemma inactive {z : Points n} (h : z∈conf _) (i j : Tag G n) (hi : ¬Active d i): (price d z).cov i j=0:= by
  rw [pays _ h]; unfold target scope perSlot; unfold Active at hi; dsimp only; rw [ceiling,dif_neg hi]; simp [treats]
lemma cap_test {z : Points n} (hz : z∈conf n) (i j : Tag G n) (hx : Active d i) (hy : Active d j):
    (price d z).cov i j = if i.1=j.1 then 0 else (Maxwell.legKernel (Prayer.scans i.2) (Prayer.scans j.2) (z i.1-z j.1):ℝ):=by
  let k := max (d i.1) (d j.1)
  let a : KeyIn G k:= ⟨i.2,le_trans hx (le_max_left ..)⟩; let b : KeyIn G k:= ⟨j.2,le_trans hy (le_max_right ..)⟩
  have h : (price d z).cov i j=(currentX hz G k).cov (i.1,a) (j.1,b):= by rw [pays _ hz]; unfold target scope perSlot; unfold Active at hx hy; dsimp only; rw [ceiling,dif_pos hx, ceiling,dif_pos hy]; rfl
  rw [h]; split
  next he=> apply Eq.trans _ (Prayer.dies hz j.1 a b);
            rw [show (i.1,a)=(j.1,a) by exact Prod.ext he rfl]
  next h=> exact Prayer.pays hz _ _ h a b

section estimates
variable {ι : Type*} {g : ι→Mesh} (A : Initialize G) {u : Filter ι} (S : Stretched u g) (x : ι → Fin n→Cover) (z : ι → Points n)

def ear (s : Price.Tag G n):= readKey (A.surveys (d s.1)) s.2
include S in
private lemma blank_diag (a b : Key G) (j : Fin n) (h : Centered u g (fun i=> x i j)) :
    Blank u g (fun i =>
      mourn (ear d A (j,a)) (ear d A (j,b)) (lag (g i).p (x i j) (x i j) + extra (g i).p (x i j) (x i j)) -
        mourn (ear d A (j,a)) (ear d A (j,b)) Cross.self):=by
  let P:= ear d A (j,a); let Q:= ear d A (j,b)
  simp_rw [← map_sub]
  refine Cross.pull_blank P Q (Cross.blossoms ..) (Cross.blossoms ..) _ fun p q=>?_
  intro m; refine ((Cross.contact S (fun i=> x i j) p q m).add (Cross.img S h h p q m)).congr_left (fun i=> by simp only [Pi.add_apply, Pi.sub_apply]; abel)

include S in
lemma blends (hx : ∀ i j : Fin n, i ≠ j→ Rout u (fun k=> z k i-z k j)) (hi : ∀ j, Centered u g (fun i=> x i j))
    (he : ∀ (i j : Fin n), far g (fun k=> x k i) (fun k=>x k j) = fun k=> z k i-z k j) (hv : ∀ᶠ i in u,z i∈conf _)
    (i j : Fin n) (a b : Key G):
    Rate u g (fun k=> (season (g k) A d (x k)).cov (i,a) (j,b)) (fun k=> (price d (z k)).cov (i,a) (j,b)):= by
  let I:Tag G n:=(i,a); let J:Tag G n:=(j,b); let A':= A.surveys (d i); let B':=A.surveys (d j); let x' k:= x k i; let y' k:= x k j
  let d₀:= generation a+generation b
  simp_rw [pair_position];
  have hu (x y : Fin n) (a b : Key G) (h : ¬generation a ≤ d x): ∀ i:Bridge G,
    mourn (readKey (A.surveys (d x)) a) (readKey (A.surveys (d y)) b) i=0:=fun i=> by rw [Cross.unused _ _ (lt_of_not_ge h)]; rfl
  by_cases hu' : generation a≤d i; swap
  · simp_rw [hu _ _ _ _ hu']; simp only [ite_self,sub_self,mul_zero, Complex.ofReal_zero]; refine (Rate.refl _ g (fun _=>(0:ℂ))).congr (EventuallyEq.refl ..) (hv.mono fun k hk=> (inactive d hk I J hu').symm)
  by_cases hw' : generation b≤d j; swap
  · have hh (V : Bridge G) : mourn (readKey (A.surveys (d i)) a) (readKey (A.surveys (d j)) b) V=0:= (moves _ _ _ (Cross.blossoms ..)).trans (hu _ _ _ _ hw' _)
    simp_rw [hh]; simp only [ite_self,sub_self,mul_zero, Complex.ofReal_zero]; refine (Rate.refl _ g (fun _=>(0:ℂ))).congr (EventuallyEq.refl ..) (hv.mono fun k hk=> ?_); dsimp only; rw [← show (price d (z k)).cov (j,b) (i,a)=_ from (price _ _).symm _ _]; exact (inactive d hk J I hw').symm
  have hp : ∀ᶠ k in u,(price d (z k)).cov (i,a) (j,b)= if i=j then 0 else (Maxwell.legKernel (Prayer.scans a) (Prayer.scans b) (z k i-z k j):ℝ):=hv.mono fun k hk=> cap_test d hk I J hu' hw'
  split_ifs with hy; swap
  · let f k:= mourn (readKey A' a) (readKey B' b) (extra (g k).p (x k i) (x k j)); let F k:= mourn (readKey A' a) (readKey B' b) (lag (g k).p (x k i) (x k j)); let K k:=Maxwell.legKernel (Prayer.scans a) (Prayer.scans b) (z k i-z k j); let t (k : ι) := (g k).spacing⁻¹^d₀
    simp only [sub_zero]; apply Rate.congr (r:=_) (Rate.real (show Rate u g (fun k=> t k*(F k+f k)) K from ?_)) ?_ ?_
    · let X:= Cross.blend (j:=a.1) (l:=b.1) S (x:=x') (y:=y') (show Rout u (far g x' y') from (he i j).symm ▸ hx i j hy) (readKey A' a) (readKey B' b) (Cross.blossoms ..) (Cross.blossoms ..) (Cross.startsKey _ a hu') (Cross.startsKey _ b hw')
      have hu : Rate u g (t*F) K:= X.congr (EventuallyEq.of_eq ?_) (EventuallyEq.of_eq ?_)
      · let B : Blank u g f := Cross.pull_blank (readKey A' a) (readKey B' b) (Cross.blossoms ..) (Cross.blossoms ..) _ fun u v=> Cross.img S (hi i) (hi j) u v
        have hq : Rate u g (t*f) 0:= (B.anyPower d₀).first_order; simpa only [show (fun k=> t k*(F k+f k))= t*F+t*f from funext fun k=> mul_add .., add_zero] using (hu.add hq)
      · exact funext fun k=> by change (Expense.a _ _)⁻¹ ^ _ * _=(Expense.a _ k)⁻¹^d₀ * _; rw [show 4+a.1+b.1=d₀ by unfold d₀ generation; omega]
      exact funext fun k=> by rw [Cross.on_shell _ _ hu',Cross.on_shell _ _ hw', he]
    · filter_upwards with k; rw [map_add]
    simp only [if_neg hy] at hp; exact hp.mono fun k hk=> hk.symm
  subst j; simp only [↓reduceIte] at hp; exact ((Rate.real ((blank_diag d A S x _ _ _ (hi i)).anyPower (generation a+generation b)).first_order).congr (EventuallyEq.refl ..) (hp.mono fun k hk=> hk.symm))
end estimates
end YM.XSpace.Price
