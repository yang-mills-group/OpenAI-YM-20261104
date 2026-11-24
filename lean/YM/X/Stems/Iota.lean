import YM.X.Gauss.Hook
import YM.X.Gauss.Milk
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Empirical
/-!
## Ordinary cover polynomials in Exponential Potential legs. Jets of bona fide local mark stencils.
Here physical factor weights not yet applied. Finset topology of coordinates comes from authentic Wilson cover/signed actions.
Real tests of incoming polynomials; cost normalized by inverse factorial.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Stems
open Function Filter Set Metric MeasureTheory Lattice Wilson PertExtension PertExtension.Series PertExtension.Series.Radial
open Source ProjectorNext.Calibration Jet Gauss Next.Rank.Normal MvPolynomial Finsupp
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius

abbrev Pin:= Edge Cover
abbrev Hair (G:Gauge):= Pin × G.ColorIndex
abbrev Brush (G:Gauge):= Pin→G.Color
abbrev Curly (G:Gauge):= poly (Hair G)
variable {G:Gauge} {s:Finset Cover}
variable (U : Brush G) (e:Pin) 
-- Hair projections real

def text (x:Brush G) : Hair G → ℝ:= fun i=> (x i.1) i.2
def textL : Brush G≃ₗ[ℝ](Hair G→ℝ):= { toFun:= text, invFun p i := WithLp.toLp 2 (fun j=> p (i,j)),left_inv _:= rfl,right_inv _:= rfl,map_add' _ _:= rfl,map_smul' _ _:=rfl}
def snap (x:Brush G) : Curly G→ₐ[ℂ] ℂ:= aeval fun i=> (text x i:ℂ)
lemma snap_ext {p q:Curly G}(h:∀ x:Brush G,snap x p=snap x q) : p=q:= by
   let A (i:Hair G):= Set.range Complex.ofReal
   apply MvPolynomial.funext_set A (fun _=>Set.infinite_range_of_injective Complex.ofReal_injective)
   intro x hx; choose y hy using fun i=> show ∃ t :ℝ,(t:ℂ)=x i from hx i (Set.mem_univ i)
   rw [← funext hy]; exact h (textL.symm y)

-- arity, support independent; Taylor circle
variable {S: CoverConfig G→ℝ}

def posit (x : Brush G):CoverConfig G:= fun i=>G.lieExp (x i)
def along (S: CoverConfig G→ℝ)(x:Brush G):ℝ→ℝ:= fun r=> S (posit (r • x))
lemma curves_pos {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E] {X : E→Brush G} (hS:Small G S) {x:E}(h : ∀ i,ContDiffAt ℝ ω (fun v=> X v i) x) : ContDiffAt ℝ ω (S ∘ posit ∘ X) x:=
 let ⟨s,hs⟩:= hS; hs.substituted (fun i=> (G.exp_jet.contDiffAt).comp x (h i.val))
lemma along_zero (hS:Small G S)(x : Brush G):ContDiffAt ℝ ω (along S x) 0:= curves_pos hS (fun i=> contDiffAt_id.smul contDiffAt_const)

abbrev Fine (G:Gauge)(s:Finset Cover):= UsedEdges s → G.Color

def comb (x:Brush G):Fine G s:= fun i=> x i.val
def extensionL (s:Finset Cover) : Fine G s →ₗ[ℝ] Brush G where
   toFun v i:= if h:i.1∈s ∧ i.1+step i.2∈s then v ⟨i,h⟩ else 0
   map_add' a b := by funext i; simp only [Pi.add_apply]; split <;> simp only [*,↓reduceDIte, add_zero]
   map_smul' a b:= by funext i; simp only [RingHom.id_apply, Pi.smul_apply]; split <;> simp only [*,↓reduceDIte, smul_zero]
lemma take_extension (x:Fine G s): comb (s:=s) (extensionL s x)=x:= by funext i; exact dif_pos i.property
lemma extend_eq (h:Empirical s S)(x:Brush G)(y:Fine G s)(he:comb x=y): S (posit x)= S (posit (extensionL s y)):= by
   subst y; apply h.supported; intro i hx hx'; exact congr_arg G.lieExp (congr_fun (take_extension (comb (s:=s) x)) (⟨i,hx,hx'⟩:UsedEdges s)).symm

def blade : (Hair G →₀ ℝ) → Curly G := fun b=> linearCombination ℝ (MvPolynomial.X (R:=ℂ)) b
-- notation (need parentheses)
lemma snaps_blade (b : Hair G →₀ ℝ)(x:Brush G): snap x (blade b)= (linearCombination ℝ (text x) b:ℂ):= by
   induction b using Finsupp.induction_linear with
   | zero=> simp [blade]
   | add a b h g=> unfold blade at *; rw [map_add,map_add,h,g,map_add,Complex.ofReal_add]
   | single i c=> simp only [blade, linearCombination_single]; rw [show c • X i= (c:ℂ) • X (R:=ℂ) i from (by simpa [Complex.real_smul] using (IsScalarTower.smul_assoc c (1:ℂ) (X (R:=ℂ) i)).symm),map_smul]; simp [snap]
lemma Xvalued  (f: Module.Dual ℝ (Fine G s)) : ∃ b:Hair G→₀ ℝ,∀ x:Brush G, linearCombination ℝ (text x) b=f (comb x):= by
   let Q(i:UsedEdges s × G.ColorIndex): Fine G s:= Pi.single i.1 (EuclideanSpace.basisFun G.ColorIndex ℝ i.2)
   refine ⟨∑ i:UsedEdges s,∑ j, Finsupp.single (i.val,j) (f (Q (i,j))),fun x=>?_⟩
   have he (v:Fine G s): v=∑ i: UsedEdges s, ∑ j, v i j • Q (i,j):= by
      ext1 i; simp only [Finset.sum_apply]; unfold Q; classical
      rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]; simp only [Pi.smul_apply,Pi.single_eq_same]; exact ((EuclideanSpace.basisFun _ ℝ).sum_repr ..).symm
      intro j hj h; simp_rw [Pi.smul_apply,Pi.single_eq_of_ne (Ne.symm h),smul_zero,Finset.sum_const_zero]
   conv_rhs => rw [he (comb x)]
   simp_rw [_root_.map_sum,Finsupp.linearCombination_single,map_smul]; apply Finset.sum_congr rfl; intro i hi; apply Finset.sum_congr rfl; intro j _; exact mul_comm ..

lemma snaps_plausible {f: Fine G s → ℝ}(h:Plausible f):∃ b : Curly G, ∀ x:Brush G,snap x b=(f (comb x):ℂ):= by
   induction h with
   | atom v=> exact ⟨MvPolynomial.C _,fun x=> (snap x).commutes _⟩
   | times a v _ ih=> obtain ⟨b,hb⟩:=ih; obtain ⟨p,hp⟩:= Xvalued v; exact ⟨b*blade p,fun x=>by rw [map_mul,hb,snaps_blade,hp]; exact (Complex.ofReal_mul ..).symm⟩
   | add _ _ h g=> obtain ⟨a,ha⟩:=h;obtain ⟨p,hp⟩:=g;exact ⟨a+p,fun x=>by rw [_root_.map_add,ha,hp];exact (Complex.ofReal_add ..).symm⟩

def kind (s:Finset Cover)(S:CoverConfig G→ℝ): Fine G s→ℝ:=S ∘ posit ∘ extensionL s
lemma kinds (h:Empirical s S):ContDiffAt ℝ ω (kind s S) 0:= curves_pos (X:=extensionL s) ⟨s,h⟩ (fun i=> (((LinearMap.proj i).comp (extensionL (G:=G) s)).toContinuousLinearMap).contDiff.contDiffAt)
lemma along_kind (h:Empirical s S)(x:Brush G): along S x= fun t :ℝ => kind s S (t • comb x):= funext fun t=> extend_eq h _ _ rfl
lemma stamp_at (h:Empirical s S)(x:Brush G)(j:ℕ): someJ (along S x) j= jet (kind s S) j (comb x):= by rw [along_kind h,homogeneous_derivative (kind s S) (comb x) _ ((kinds h).of_le le_top)];rfl
lemma jets (S:CoverConfig G→ℝ)(h:Small G S)(j:ℕ):∃ p:Curly G,∀ x:Brush G,snap x p=(↑(someJ (along S x) j:ℝ):ℂ):= by
   obtain ⟨s,h⟩:=h; obtain ⟨b,hb⟩:= snaps_plausible (Plausible.stamp (kind s S) j); exact ⟨b,fun x=>by rw [stamp_at h,hb]⟩

def mark (S:CoverConfig G→ℝ) (h:Small G S)(j:ℕ) := (jets S h j).choose
lemma mark_test (h:Small G S)(j:ℕ)(x:Brush G) : snap x (mark S h j) = (↑(someJ (along S x) j:ℝ) :ℂ):= (jets S h j).choose_spec x

end YM.PositionX.Stems
