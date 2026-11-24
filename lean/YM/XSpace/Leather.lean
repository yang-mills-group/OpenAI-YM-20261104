import YM.XSpace.NormalTools
import YM.XSpace.Charge

/-!
# First-order stencil proof — kit for polynomials even with infinitely many potentials

On the link colors in one fixed image metric, φ x = ⟪basis, x⟫_ℝ. Polynomial
basis only on bonds; constructive witnesses not claimed computational. Reality of
stencils on real arrays. Bounded stencil size when reexpressed across regulators by
rename etc, proved separately (takes exact stencil receipt). Aim regulator convergence.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Chart2
open RG Wilson Labels Lattice Filter Function Drift Finsupp MvPolynomial Next.Rank.Normal
open scoped Topology BigOperators
variable {G : Gauge} {Z Y: Type*}
abbrev Rollers (Z : Type*) (G : Gauge):=Z × G.ColorIndex
abbrev Kit (Z : Type*) (G : Gauge):=poly (Rollers Z G)
abbrev basisC (G : Gauge) := EuclideanSpace.basisFun G.ColorIndex ℝ

def numbers (A: Z→G.Color) (e:Rollers Z G):ℂ:= A e.1 e.2
def pit (A:Z→G.Color):Kit Z G →ₐ[ℂ] ℂ:=aeval (numbers A)
theorem same {k l:Kit Z G} (h : ∀ A:Z→G.Color,pit A k=pit A l):k=l:=by
  classical
  apply MvPolynomial.funext_set (fun _ => Set.range (fun x : ℝ => (x : ℂ))) (fun _=> Set.infinite_range_of_injective Complex.ofReal_injective)
  intro x hx; choose y hy using fun i=> hx i (Set.mem_univ i)
  let f (e:Z):G.Color:=WithLp.toLp 2 fun i=> y (e,i)
  have p : x=numbers f:= funext fun i=> (hy i).symm
  rw [p]; exact h _
lemma renamed (f:Z→Y) (A:Y→G.Color) (k:Kit Z G):pit A (MvPolynomial.rename (Prod.map f id) k)=pit (A ∘ f) k:=by
  suffices H : (pit A).comp (MvPolynomial.rename (Prod.map f id))=pit (A ∘ f) from DFunLike.congr_fun H k
  ext1 i; simp [pit,numbers]

abbrev D (v:Z→G.Color) := slit (numbers v)
lemma slit_shift {ι : Type*} (f: ℝ→ι→ℂ) (x:ℝ) (d:ι→ℂ) (h : ∀ i, HasDerivAt (fun t=> f t i) (d i) x) (k:poly ι): HasDerivAt (fun t=> aeval (f t) k) (aeval (f x) (slit d k)) x:=by
  induction k using MvPolynomial.induction_on with
  | C a=> simp only [slit_C,map_zero,aeval_C,Algebra.algebraMap_self,RingHom.id_apply]; exact hasDerivAt_const _ _
  | add p q hp hq=> simp only [map_add]; exact hp.add hq
  | mul_X p i h'=> rw [mul_comm p, slit_prod]; simp only [map_add,map_mul,aeval_X,aeval_C,Algebra.algebraMap_self,RingHom.id_apply]; convert! (h i).mul h' using 1; ring
lemma directional (A v: Z→G.Color) (k:Kit Z G): HasDerivAt (fun t:ℝ=> pit (A+t • v) k) (pit A (D v k)) 0:=by
  let f (t:ℝ):= numbers (A+t • v)
  have hh (i:Rollers Z G): HasDerivAt (fun t=> f t i) (numbers v i) 0:= by
    set z : ℂ:= numbers v i
    have hi : ∀ t:ℝ, f t i=numbers A i+t • z:=by intro t; simp [numbers,f,z,Complex.real_smul]
    simp_rw [hi]; simpa only [zero_add, one_smul] using! ((hasDerivAt_const (0:ℝ) (numbers A i)).add ((hasDerivAt_id' 0).smul_const z))
  have he:= slit_shift f 0 _ hh k; simp only [f,zero_smul,add_zero] at he; exact he
lemma d_all (A v: Z→G.Color) (k:Kit Z G) (f d: (Z→G.Color)→ℂ) (p: ∀ x, pit x k=f x)
    (h : ∀ x: Z→G.Color, HasDerivAt (fun t:ℝ=> f (x+t • v)) (d x) 0) : pit A (D v k)= d A:= (by simp_rw [← p] at h; exact (directional A v k).unique (h _))

-- polynomial builder with cheap coordinate-free finite sums
variable {E F X : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F] [AddCommGroup X] [Module ℝ X]

def Reads (G : Gauge) (f : (Z→G.Color)→ℝ): Prop:= ∃ K, ∀ A, pit A K=(f A:ℂ)
def Record (G : Gauge) (f : (Z→G.Color)→E): Prop:= ∀ p : Module.Dual ℝ E, Reads G (fun A=> p (f A))
namespace Reads
variable {v w : (Z→G.Color)→ℝ}
def pol (p : Reads G v) := Classical.choose p
lemma value (p : Reads G v) (A) : pit A p.pol=(v A:ℂ):=p.choose_spec A
lemma mul (p : Reads G v) (q : Reads G w): Reads G (fun A=>v A*w A):=⟨p.pol*q.pol,fun A=>by rw [map_mul,p.value,q.value,Complex.ofReal_mul]⟩
lemma add (p : Reads G v) (q : Reads G w): Reads G (fun A=>v A+w A):=⟨p.pol+q.pol,fun A=>by rw [map_add,p.value,q.value,Complex.ofReal_add]⟩
lemma neg (p : Reads G v): Reads G (fun A=> -v A):=⟨-p.pol,fun A=>by rw [map_neg,p.value,Complex.ofReal_neg]⟩
lemma const (t:ℝ): Reads (Z:=Z) G (fun _=>t):=⟨C (t:ℂ),by simp [pit]⟩
lemma smul (r:ℝ) (p : Reads G v) : Reads G (fun A=>r • v A):= (Reads.const r).mul p
lemma sum {ι : Type*} (s:Finset ι) (w:ι→(Z→G.Color)→ℝ) (p : ∀ i∈s, Reads G (w i)): Reads G (fun A=>∑ i∈s, w i A):=by
  classical induction s using Finset.induction_on with
  | empty => simp; apply Reads.const
  | insert i s h ih => simp only [Finset.sum_insert h]; exact (p i (by simp)).add (ih fun j hj=> p _ (by simp [hj]))
lemma proj (i : Z) (j : G.ColorIndex): Reads G (fun A=>A i j) :=⟨MvPolynomial.X (i,j),fun _=>aeval_X ..⟩
end Reads
namespace Record
variable {a b : (Z→G.Color)→E} {w:(Z→G.Color)→F}
lemma move (L:E→ₗ[ℝ] F) (p : Record G a) : Record G fun A=>L (a A):= fun q=> p (q ∘ₗ L)
lemma const (x:E): Record (Z:=Z) G (fun _=>x):= fun _=> Reads.const _
lemma add (p:Record G a) (q:Record G b): Record G (fun A=> a A+b A):=by intro r; simp only [map_add]; apply (p r).add (q r)
lemma smul (t:ℝ) (p:Record G a): Record G (fun A=> t • a A):=by intro r; simp only [map_smul]; apply (p r).smul
lemma pol_extend {ι: Type*} [Fintype ι] (L:Module.Basis ι ℝ E) : (∀ i, Reads G (fun A=>L.repr (a A) i)) → Record G a:=by
  intro p t; rw [show (fun A=>t (a A))=(fun A=> ∑ i, L.repr (a A) i • t (L i)) from funext fun A=> by rw [← (L.sum_repr (a A)),map_sum]; simp only [map_smul]; rw [L.sum_repr]]; exact Reads.sum _ _ (fun i _=> (p i).mul (Reads.const _))
lemma entry (e : Z): Record G (fun A=>A e):= by apply pol_extend (basisC G).toBasis; intro i; simp only [OrthonormalBasis.coe_toBasis_repr_apply,EuclideanSpace.basisFun_repr]; apply Reads.proj
lemma pairing [FiniteDimensional ℝ F] (Q:E→ₗ[ℝ] F→ₗ[ℝ] X) (p:Record G a) (q:Record G w):Record G (fun A=> Q (a A) (w A)):=by
  intro t; let L:= Module.finBasis ℝ F
  have h (A): t (Q (a A) (w A))= ∑ i,L.repr (w A) i * t (Q (a A) (L i)):=by
    conv_lhs => rw [← L.sum_repr (w A)]; simp only [map_sum,map_smul,smul_eq_mul]
  simp_rw [h]; apply Reads.sum; intro i _; exact (q (L.coord i)).mul (p (t ∘ₗ Q.flip (L i)))
lemma pi {ι : Type*} [Fintype ι] [FiniteDimensional ℝ F] (z:(Z→G.Color)→ι→ F) (p : ∀ i, Record G (fun A=> z A i)): Record G z:=by
  classical
  apply pol_extend (Pi.basis (fun _ : ι=>Module.finBasis ℝ F)); rintro ⟨i,k⟩; simp only [Pi.basis_repr]; exact p i ((Module.finBasis ℝ F).coord k)
end Record
end YM.XSpace.Chart2
