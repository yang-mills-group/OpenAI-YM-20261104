import YM.FVA2.Position.Trial
/-!
# `register` orientation for the mark prescription

Price & sum algebra for the `TaylorOKF` build.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Position.Favors
open Function Set Filter Finset MeasureTheory Lattice
open MS MS.Plane MS.Tone MS.Koszul MS.Heat MS.Book MS.Landau MS.Landau.Detect MS.Momentum MS.Plane.Wire
open MS.Native MS.Native.Wilsonian MS.City MS.Tone.Frame MS.Arts MS.Outlook MS.Color MS.Native.Paint
open MS.Book.Program MS.Book.Convolve MS.Cylinder.Lab MS.Cylinder
open Brass MS.Wind MS.Wind.Leading MS.High MS.High.Knobs MS.Logarithm MS.Menus MS.Land Axes Wheel
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace Classical
variable {m n d:ℕ}{J:Type}{G:Gauge}{u:ℤ}(s:Signed)
variable {p:Team}{ F H: Dec G}{ S:MS.Land.Booked (Press.portDeck G) }
local notation "B"=> Press.portDeck G
local notation "𝓜"=> Glyph B d
variable (Y:XSpace.Initialize G)
local notation "ℳ"=> Press.wickInput Y
open Native.Orient
-- charge with valuation rank allowance. In particular the orientation remains in the same budget.
def goH (s:Signed)(T:Power G) : Power G where
   input:= pose s ∘ T.input
   polyn:= T.polyn.linear ((pose s).restrictScalars ℝ)
   actual x:= stampB s (T.actual x)
   calm x:= Color_w s (T.calm x)
   allowance:=T.allowance
   ranks x:= limits_p s (T.ranks x)
-- Combine all the witness data on mark rank.
def bigH (s:Finset J)(f:J→ℝ)(X:J→Power G): Power G where
   input:=∑ i∈s,f i • (X i).input
   polyn:= Ready.sums s (fun i _=> (X i).polyn.scale _)
   actual (x:ℝ) := by simp_rw [Finset.sum_apply,Pi.smul_apply]; exact Tune.sum _ (fun i _=> (( X i).actual x).cash ( ( f i:ℝ ):ℂ) (by simp))
   calm (x:ℝ) := by simp_rw [Finset.sum_apply,Pi.smul_apply]; exact Paint.Colorless.csum _ (fun i _=> (( X i).calm x).smul ( ( f i:ℝ ):ℂ))
   allowance:=s.sup fun i=> (X i).allowance
   ranks (x:ℝ) := by rw [Finset.sum_apply,sum_stack]; exact Limit.sum s (fun i hi=>((X i).ranks x).up ( Nat.cast_le.mpr ( Finset.le_sup (f:=fun i=> (X i).allowance ) hi ))|>.smul ( ( f i:ℝ ):ℂ))
def stepF (s:Finset J)(f:J→ℝ)(X:J→ Acts B d) : Acts B d:= fun n=> ⟨ ∑ i∈s, f i • (X i n).register, bigH s f (fun i=> (X i n).proof) ⟩
local notation "κ"=> markS s G
-- oriented transformation on register. Row label `i` output all `a` in its own bidegree basis
-- as Roll frames. Keep this exact, not opaque.
def erect {E:Type}[AddCommMonoid E][Module ℝ E](f:Glyph (Press.portDeck G) d→ E)(x:𝓜) : E:= ∑ i:Case G x.size x.grade, markS s G x.size x.grade i x.2.2 • f (Axes.take x i)
lemma erect_t {E:Type}[AddCommMonoid E][Module ℝ E](t:Signed)(f:Glyph (Press.portDeck G) d → E)(x:𝓜) : erect (s*t) f x = erect s (erect t f) x:=by
   unfold erect; simp_rw [ pack, Finset.sum_smul, Finset.smul_sum, smul_smul ]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; refine Finset.sum_congr rfl (fun j _=>?_ ); rw [mul_comm]
lemma erect_sum {E:Type}[AddCommMonoid E][Module ℝ E](F:Finset J)(f:J→ℝ)(X:J→Glyph B d→ E) : erect s (∑ i∈F,f i • X i)= ∑ i∈F,f i • erect s (X i):= by
    funext i; unfold erect; simp_rw [Finset.sum_apply,Pi.smul_apply,Finset.smul_sum]; nth_rw 1 [Finset.sum_comm]; refine Finset.sum_congr rfl (fun x _=> Finset.sum_congr rfl (fun k _=> smul_comm .. ))
-- proof-slot supplied too. needed `rent`. physical frame uses register only.
def lifted (s:Signed)(A: Acts B d): Acts B d := fun i=> ⟨ erect s (A i).register, goH s (A i).proof ⟩

lemma stepCost (S:Finset J)(f:J→ℝ)(X:J→ Acts B d)(w:𝓜)(x:ℝ): oil (stepF S f X) w n x=∑ i∈S,f i • oil ( X i ) w n x :=by unfold oil stepF; simp only [ Finset.sum_apply,Pi.smul_apply,Polynomial.eval_finsetSum, Polynomial.eval_smul, smul_eq_mul,Complex.ofReal_sum,Complex.real_smul,Complex.ofReal_mul]
lemma costW (A:Acts B d)(w:𝓜)(x:ℝ): oil (lifted s A) w n x= erect s (fun w=>oil A w n x) w:= by unfold oil lifted erect; simp only [Polynomial.eval_finsetSum, Polynomial.eval_smul, smul_eq_mul,Complex.ofReal_sum,Complex.real_smul, Complex.ofReal_mul]
-- sum over `Glyph` components
lemma transpose {E P T:Type}[AddCommMonoid E][AddCommMonoid P][AddCommMonoid T][Module ℝ E][Module ℝ P][Module ℝ T] (f: Glyph B d→ E)(x:Glyph B d→ P)(K:E→ₗ[ℝ]P→ₗ[ℝ]T) : (∑ i:𝓜,K ( erect s f i) (x i))=∑ i:𝓜,K (f i) (rotateField s x i):= by
    rw [ Fintype.sum_sigma, Fintype.sum_sigma ]; refine Finset.sum_congr rfl (fun i _=>?_ ); rw [ Fintype.sum_sigma,Fintype.sum_sigma ]; -- first order? rw all occurrences by rw repeats? check
    apply Finset.sum_congr rfl; intro j hj; unfold erect rotateField; simp_rw [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply]; exact Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ) (f:=fun (a b:Case G i.val j.val)=> markS s G i.val j.val b a • K (f ⟨ i,j,b⟩) (x ⟨i,j,a⟩))
private def player (X:Type)[AddCommGroup X][Module ℂ X][Module ℝ X][IsScalarTower ℝ ℂ X] : ℂ →ₗ[ℝ] X→ₗ[ℝ] X:={ toFun x:= ((LinearMap.lsmul ℂ X) x).restrictScalars ℝ, map_add':= fun _ _=> LinearMap.ext fun _=> add_smul ..,map_smul':= fun a x=> LinearMap.ext fun y=> smul_assoc a x y }
-- Book exact mode
lemma vent_service (A:Acts B d)(p:Team)(x:ℝ): rentF (ℳ) p (lifted s A) x n= pose s (rentF ℳ p A x n):= by
   unfold rentF; rw [map_sum]; simp_rw [map_sum,map_smul,costW,show ∀ (j:𝓜) i,pose s (Glyph.preambleF ℳ p j x i)= _ from fun j i=> congr_fun (preamble_s s Y j p x) i]; nth_rw 1 [Finset.sum_comm]; nth_rw 2 [Finset.sum_comm]; -- RHS RotateField unfolds inside
   apply Finset.sum_congr rfl; intro j _; have he(i:𝓜): rotateField s (fun i=>Glyph.preambleF ℳ p i x) i j.2= rotateField s (fun i=> Glyph.preambleF ℳ p i x j.2) i:= by simp only [rotateField, Finset.sum_apply, Pi.smul_apply]
   exact (transpose s (fun v:𝓜=>oil A v j.1 x) (fun i=>Glyph.preambleF ℳ p i x j.2) (player _)).trans (Finset.sum_congr rfl (fun i _=> congr_arg (fun z:Dot G Cover=> oil A i j.1 x • z) ( he i ).symm))
lemma crosses (A:Acts B d)(p:Team) (x:ℝ) : motto p (lifted s A) x n= pose s (motto p A x n):= by
   rw [sky,sky]; simp only [map_add,map_sum, cone_pts ]; refine congr_arg₂ _ rfl (Finset.sum_congr rfl (fun i _=>?_ )); exact Eq.symm (wind_t s («B»:= (A i.2).proof.input x) ( (core_circle G p).stance0 x i.1 rfl ))
lemma m_read (A: Acts B d)(p:Team): scoreF ℳ p (lifted s A)=fun x=> pose s ∘ scoreF ℳ p A x:= by funext x i; simp_rw [comp_apply,scoreF,Pi.add_apply,map_add, vent_service,crosses]
lemma several (S:Finset J)(f:J→ℝ)(X:J→ Acts B d)(p:Team)(x:ℝ): rentF ℳ p ( stepF S f X ) x n=∑ i∈S,f i • rentF ℳ p (X i) x n:= by
   unfold rentF; simp_rw [stepCost, Finset.sum_smul, smul_assoc, Finset.smul_sum ]; nth_rw 2 [Finset.sum_comm]; exact Finset.sum_congr rfl (fun i _=> Finset.sum_comm)
lemma stellar (S:Finset J)(f:J→ℝ)(X:J→ Acts B d)(p:Team)(x:ℝ): motto p ( stepF S f X ) x n=∑ i∈S,f i • motto p (X i) x n:= by
   simp only [sky, stepF,bigH,map_sum,Finset.sum_apply, Pi.smul_apply,smul_add,Finset.smul_sum,Finset.sum_add_distrib]; simp_rw [show ∀ (x:ℝ) (L: Dot G Cover→ₗ[ℂ] Dot G Cover ) (K:Dot G Cover), L (x • K )= x • L K from fun x L K=> map_smul (L.restrictScalars ℝ) x K]; rw [ Finset.sum_comm ]; -- choose source
lemma forecast (S:Finset J)(f:J→ℝ)(X:J→ Acts B d)(p:Team): scoreF ℳ p (stepF S f X)= ∑ i∈S,f i • scoreF ℳ p (X i):= by funext x m; simp only [scoreF, Pi.smul_apply,Finset.sum_apply, Pi.add_apply, smul_add, Finset.sum_add_distrib, stellar, several]
-- exact interpolation of mark:b
local notation "Z" => Crosswind.α
lemma stairs (A: Acts B d)(p:Team): horizonF ℳ p (lifted s A)= fun j x=> Z s⁻¹ ∘ ( horizonF ℳ p A j x ):= by
    have hm := Crosswind.saturated s (skyPC G p) (aquaF ℳ p A); have he : ∀ i, ( horizonF ℳ p (lifted s A) ) i= (fun x=> Z s⁻¹ ∘ horizonF ℳ p A i x) := by
        intro i; apply mark_birth (aquaF ℳ p _) hm (fun j hj x=>?_ ) i (Nat.lt_succ_self i); rw [m_read]
    exact funext he
lemma total_H (S:Finset J)(f:J→ℝ)(X:J→ Acts B d)(p:Team): horizonF ℳ p (stepF S f X) = ∑ i∈S,f i • horizonF ℳ p (X i):= by
   have he := Crosswind.pm_sweep (A:=fun i=> scoreF ℳ p ( X i )) S (fun j _=> aquaF ℳ p ( X j)) f; funext i; exact mark_birth (forecast Y S f X p ▸ aquaF ℳ p (stepF S f X)) he (fun _ _ _=>rfl) _ (Nat.lt_succ_self i) -- may rewrite horizon by dependent notation. inspect

end YM.FVA2.Position.Favors
