import YM.RegulatorIR.Uniform.Leases
import YM.RegulatorIR.Uniform.RelaxVac

/-!
Specifically finite-top: a page goes from a finer regulator/page to the
next coarser one. Bounds however run *uniformly* over a family of lists of
possibly unbounded lengths, counting the number of skipped steps towards the
polynomial budget. Variables `w` can pack external tests, center locations,
etc. in addition to a scale sequence and structural and analytic supplies.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Ledger
open Budget Uniform Function
open scoped Topology ENNReal NNReal BigOperators Classical
variable {W Z:Type} {M:W→ℕ}
structure Page {W : Type}(M:W→ℕ) where
 bindW : W
 downW : ℕ
 good : downW ≤ M bindW
structure Flap {W:Type}(M:W→ℕ) where
 volW : W
 offset : ℕ
 ok : offset < M volW

def Flap.prev (i:Flap M) : Page M:=⟨i.volW,i.offset,i.ok.le⟩
def Flap.next (i:Flap M): Page M:= ⟨i.volW,i.offset+1,i.ok⟩
def Page.opening (M:W→ℕ)(w: W): Page M := ⟨w,0,Nat.zero_le _⟩
def Page.finallyW (M:W→ℕ) (w:W) : Page M := ⟨w,M w, le_rfl⟩

lemma Page.proves {g:Page M→Prop}(ht:∀ w,g (Page.opening M w))(h:∀ f:Flap M,g f.prev → g f.next) : ∀ j, g j:=by
 rintro ⟨w,n,p⟩; induction n with
 | zero=> exact ht w
 | succ n ih => exact h ⟨w,n,p⟩ (ih (Nat.le_of_succ_le p))

variable {L : Meter W}

def coverL (M:W→ℕ) (L:Meter W) : Meter (Page M) := L.us Page.bindW
def flapL (M:W→ℕ)(L:Meter W):Meter (Flap M) := L.us Flap.volW

/-- No multiplicative loss each recurrence on a *diagonal* component.
Smaller components pay polynomial cost via carrying. -/
lemma turning (C:Page M→ℝ≥0∞) {F: Flap M→ℝ≥0∞} {v : W→ℝ≥0∞}
   (hp:Carry (flapL M L) (fun f=> v f.volW) F) (h: ∀ f:Flap M,C f.next≤ C f.prev + F f) (hL: Poly L (fun w=>(M w:ℝ≥0∞)))(hh: Carry L v fun w=>C (Page.opening M w)): Carry (coverL M L) (fun i=>v i.bindW) C := by
 obtain ⟨a,⟨d,p,hd,H⟩,hf⟩:=hp
 have h₁ : ∀ i: Page M,C i ≤ C (Page.opening M i.bindW)+i.downW*(d*L.val i.bindW^p*v i.bindW):= by
   apply Page.proves
   · intro w; simp [Page.opening]
   intro j hJ; rcases j with ⟨w,n,e⟩; let X : Flap M:= ⟨w,n,e⟩; let k:= d*L.val w^p*v w
   change C _ ≤ C (Page.opening M w)+ n*k at hJ
   change C X.next≤ C (Page.opening M w)+ (↑(n+1):ℝ≥0∞)*k
   have hx:F X ≤ k := (hf X).trans (mul_le_mul_left (H X) _)
   apply (h X).trans ((add_le_add hJ hx).trans_eq ?_); simp [add_mul,add_assoc]
 let f i:= d*L.val i^p*v i
 have hx: Carry L v f:= Carry.mul_left ((Poly.standard L hd).mul ((Poly.roof L).powQ p)) (Carry.unit L v)
 have hm:Carry L v fun w=>C (Page.opening M w)+(M w:ℝ≥0∞)*f w:= hh.add (Carry.mul_left hL hx)
 exact Carry.mono (Carry.us hm Page.bindW) (fun w=> (h₁ w).trans (add_le_add_right (mul_le_mul_left (Nat.cast_le.mpr w.good) _) _))

/-- Triangular entropy occurs on at most finitely many steps on each path
charged to a fixed finite demand. No dependence on polynomial norms of all
orders assumed. -/
lemma editions {e:ℕ}(d:ℕ→ℕ) (m:ℕ){P:ℕ→ℕ→Prop} (h:∀ i ≤ e,∀ j,m≤j → j ≤ d i → (∀ p q, Earlier i j p q → m≤q → P p q) → P i j)(hh:∀ i ≤ e,∀ j, d i < j → m ≤ j → P i j): ∀ i ≤ e,∀ j,m ≤ j → P i j:=by
 intro i he; induction i using Nat.strong_induction_on with
 | _ i ih=>
   have hP t : ∀ j,m≤j→d i+1 - j=t → P i j:=by
      induction t using Nat.strong_induction_on with
      | _ t ht =>
        intro j hj hJ
        by_cases hy: d i < j
        · exact hh i he j hy hj
        apply h i he j hj (by omega)
        rintro p q (hp | ⟨rfl,hp⟩) hq
        · exact ih _ hp (by omega) q hq
        exact ht _ (show d p+1-q<t from by omega) q hq rfl
   intro j hj; exact hP _ j hj rfl
end YM.RegulatorIR.Ledger
