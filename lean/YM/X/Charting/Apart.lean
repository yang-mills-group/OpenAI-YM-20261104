import YM.X.Charting.Dew
/-!
## Mixed Wick coproduct contractions from ordinary product to position split. One self projection freeze.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Hinge
open Function Filter Set Metric MeasureTheory Lattice Wilson PertExtension PertExtension.Series PertExtension.Series.Radial
open Source ProjectorNext.Calibration Gauss Next.Rank Normal MvPolynomial Finsupp
open Feyn Gauge LatticePT PertExtension.Orb Chart Stems PertExtension.Series.Tested Finset Interval Size Asymptotics
open Pert.Orb (positiveLinks wilson Potential)
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {n:Side} {q:ℕ+}(hq:1<q.val)
local notation "X'"=> MvPolynomial.X
variable {α β V:Type*}
variable (P:poly α)(S:poly V)(Q : Symmetric (α⊕V))
def co : poly α→ₐ[ℂ] poly (α⊕ V):= MvPolynomial.rename Sum.inl
def coda : poly V→ₐ[ℂ] poly (α⊕ V):= MvPolynomial.rename Sum.inr
-- only on V side; inl α family unbounded but still finite support projections.
variable (R:Symmetric V)
def sweep (y z:α⊕V):ℂ:= match y,z with
    | .inr y,.inr z=> R.cov y z
    | _,_=>0
def swept (R:Symmetric V):Symmetric (α⊕V):=⟨sweep R,(fun a b=>by cases a <;> cases b <;> (first | rfl|apply R.symm ..))⟩
lemma glows_left (R:Symmetric V) (f:poly (α⊕ V)): milk (swept R) (co P * f) = co P * milk (swept R) f:= by
   induction P using MvPolynomial.induction_on with
   | C x=> rw [co,rename_C,drink]
   | add x y h g=> simp only [_root_.map_add,add_mul,h,g]
   | mul_X p i ih => rw [mul_comm p, map_mul co,mul_assoc,mul_assoc,show co (X' i)=_ from rename_X Sum.inl i,feeds, show (swept (α:=α) _).cov (.inl i)=_ from funext fun j:α⊕V=>show (swept R).cov (.inl i) j=(0:α⊕V→ℂ) j by cases j <;> rfl,slit_zero]; simp [ih]
lemma full_swept : milk (swept R) (co P*coda S)=co P*coda (milk R S):= by
   have ht : remap (.inr : V→α⊕V) (swept R)=R:= Normal.Symmetric.ext (funext fun i=> funext fun j=> remap_cov (.inr : V→α⊕V) (swept R) i j)
   rw [glows_left, coda,renative, ht]

def peel (Q:Symmetric (α⊕V)):= remap Sum.inr Q
def noHome (Q:Symmetric (α⊕ V)):= Q + -swept (peel Q)
lemma peel_l (i:α)(j:α⊕V): (noHome Q).cov (.inl i) j=Q.cov (.inl i) j:= by cases j <;> (change _+(-(0:ℂ)) =_; rw [neg_zero,add_zero])
lemma peel_r (i j:V): (noHome Q).cov (.inr i) (.inr j)=0:= by change _ + (-(peel Q).cov i j) = _;rw [peel, remap_cov, add_neg_cancel]
lemma decap : milk Q (co P*coda S)= milk (noHome Q) (co P * coda (milk (peel Q) S)):= by
  rw [← full_swept,warms]; apply congr_arg (fun v:Symmetric (α⊕V)=> milk v _); ext1; change Q.cov = (Q.cov + -(swept (α:=α) (peel Q)).cov)+(swept (peel Q)).cov ; abel
lemma result : shock Q (co P*coda S)=shock (noHome Q) (co P*coda (milk (peel Q) S)):= by unfold shock; rw [blend_components, decap, blend_components]

-- helper for 3-legs
variable (D:Symmetric (Hair G))
lemma triple (a b c:Hair G)(h₁:D.cov a b=0)(h₂:D.cov b c=0)(h₃:D.cov a c=0): milk D (X' a*(X' b*X' c)) = X' a*(X' b* X' c):= by
    have h (p:Hair G): milk D (X' p)=X' p:= by simpa only [Normal.pure, Derivation.map_one_eq_zero,add_zero,mul_one] using! Normal.feeds D p 1 -- typo
    simp [feeds, h, slit_prod,h₁,h₂,h₃]
-- command for using linear combinations along distinct-color triple space. need span result instead.
local notation "J"=> Hair G
local notation "K"=> G.ColorIndex

def tripleSpan (G:Gauge): Submodule ℂ (Curly G):= Submodule.span ℂ {p|∃ a b c:Hair G, a.2≠b.2 ∧ b.2≠c.2 ∧ c.2≠ a.2 ∧ p= X' a*(X' b* X' c)}
lemma generated (a b c:Hair G) (h₁:a.2≠b.2)(h₂:b.2≠c.2)(h₃:c.2≠a.2): X' a*(X' b * X' c)∈ tripleSpan G:= Submodule.subset_span ⟨_,_,_,h₁,h₂,h₃,rfl⟩ -- infer

lemma group_face (p:PlaqAxes)(k i j:K) (a b:Pin)(h:k≠ i ∧ i≠ j ∧ j ≠k): faceText p k*(X' (a,i)*X' (b,j))∈ tripleSpan G:= by
   unfold faceText arc blade; simp only [map_add,map_sub,linearCombination_single,one_smul,add_mul,sub_mul]; exact (tripleSpan _).sub_mem ((tripleSpan _).sub_mem ((tripleSpan _).add_mem (generated _ _ _ h.1 h.2.1 h.2.2) (generated _ _ _ h.1 h.2.1 h.2.2)) (generated _ _ _ h.1 h.2.1 h.2.2)) (generated _ _ _ h.1 h.2.1 h.2.2)
lemma group_tan (p:PlaqAxes)(k i j:K) : (iv k i j:ℂ) • (faceText p k * shiftProduct p i j)∈ tripleSpan G:= by
   by_cases ht:k≠i ∧ i≠j ∧ j≠k
   · refine (tripleSpan G).smul_mem _ ?_; unfold shiftProduct; dsimp only; simp only [mul_sub,add_mul, sub_mul,mul_add]; repeat (first| apply Submodule.sub_mem|apply Submodule.add_mem| exact group_face p k i j _ _ ht)
   rw [skip_tan k i j ht]; simp
lemma vertex_triples (p:PlaqAxes): vertex p∈tripleSpan G:= by rw [trinity]; exact (tripleSpan G).sum_mem fun i _=> (tripleSpan G).sum_mem fun j _=> (tripleSpan G).sum_mem fun k _=> group_tan p i j k
lemma freezes (h:∀ i j:Hair G,i.2≠ j.2→ D.cov i j=0){p:Curly G}(hp:p∈ tripleSpan G) : milk D p=p:= by
    apply sub_eq_zero.mp; change p∈ LinearMap.ker (milk D-LinearMap.id); apply Submodule.span_le.mpr ?_ hp; rintro q ⟨a,b,c,ha,hb,hc,rfl⟩; exact sub_eq_zero.mpr (triple D a b c (h a b ha) (h b c hb) (h a c hc.symm))
    -- edit
end YM.PositionX.Hinge
