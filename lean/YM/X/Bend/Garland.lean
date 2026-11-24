import YM.X.Sage.Arb
/-!
# tlabels. sqrt-unit quaternion basis, genuine smooth kernels Φ. marker orientation args ∈ Pure.Label.E. Scaled exact combo coefficient.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Bend
open Lattice Wilson Next.Rank Normal LiftMark Crate Porch Rays Shelf Tot
open MvPolynomial Labels Pert.Position Pert.RawLabels
open Filter Function MeasureTheory Set Reed Stems Haze Fielding PertExtension LatticePT Chir Sage Bare
open scoped Topology BigOperators Classical
variable {G:Gauge}{F:Labels.Frames G} {d k:ℕ} {q:ℕ+} {V I:Type*} {r R:ℝ}
local notation "U"=> G.ColorIndex
local notation "T"=>Tet
local notation "Q"=>PlaqAxes
local notation "K"=> (atTop:Filter ℕ)
open Real (sqrt)
def rayS : ℝ:=(sqrt 2)⁻¹
lemma spark : rayS>0:= by unfold rayS; positivity
lemma spark₂ : rayS^2=1/2:= by unfold rayS; rw [inv_pow,Real.sq_sqrt (by norm_num : (2:ℝ)≥0)];norm_num
-- curvature spin components, normed. explicit form ⇒ complementary duality (+1 etc).
def eMode (r:ℝ)(p:Tet)(x:PlaqAxes):ℝ:=rayS* dataF r p x
lemma form_weight (i j:Tet)(s t:ℝ):∑ x:Q,eMode s i x *eMode t j x=if i=j then (1+s*t)/2 else 0:= by
     simp_rw [eMode,mul_mul_mul_comm,←sq, ←Finset.mul_sum, spark₂, Sage.finsum]; fin_cases i<;>fin_cases j<;> simp only [dataF,plaq,form, ←Fin.val_inj, Fin.isValue,Fin.val_zero,Fin.val_one] <;> norm_num [form]<;> ring
lemma ortho_pair (i j:Tet)(h:r^2=(1:ℝ)): ∑ x:Q,eMode r i x *eMode r j x= if i=j then (1:ℝ) else 0:= by rw [form_weight]; split_ifs; rw [← sq,h]; norm_num; rfl
lemma ortho_other (i j:Tet)(h:r^2=(1:ℝ)): ∑ x:Q,eMode r i x *eMode (-r) j x=0:= by rw [form_weight]; split_ifs; rw [mul_neg,←sq,h]; ring; rfl
-- τ-input exact labels, including triple area alt. redefines as normed poly via Price.Tensor.
open Tri
local notation "P"=> Normal.poly (CoverC G)
def nor (s:ℝ)(p:Tet)(i:G.ColorIndex): P:= Complex.ofReal rayS • Sage.Emitter s p i
lemma nor_decks (s:ℝ)(p:Tet)(a:G.ColorIndex): nor s p a= ∑ v:Q,(eMode s p v:ℂ) • MvPolynomial.X (v,a):= by unfold nor Emitter eMode; simp_rw [Finset.smul_sum,smul_smul,Complex.ofReal_mul]
def Bpol (G:Gauge): Normal.poly (CoverC G):= ∑ i:Tet,∑ j:Tet,∑ k:Tet,(↑(Chir.η i j k):ℂ) • cubicP (nor 1 i) (nor 1 j) (nor 1 k)
def Upol (G:Gauge): Normal.poly (CoverC G):= (1/2:ℂ) • ∑ i:Tet,∑ a:G.ColorIndex, nor (-1) i a *nor (-1) i a
def boostB := 6*rayS^3
def boostU := (1/2:ℝ)* rayS^2
lemma beta_posible : 0<boostB:= by unfold boostB; have h:=spark; positivity
lemma u_posible : 0<boostU:= by unfold boostU; have h:=spark; positivity
section
variable (f t g: G.ColorIndex→V) [CommRing V][Algebra ℂ V]
lemma grow (c:ℂ):cubicP (c • f) (c • t) (c • g)= c^3 • cubicP f t g:= by
   unfold cubicP; simp_rw [Pi.smul_apply, smul_mul_assoc,mul_smul_comm,Finset.smul_sum,smul_smul]; apply Finset.sum_congr rfl; intro i _; refine Finset.sum_congr rfl fun j _=> Finset.sum_congr rfl fun k _=> ?_; congr 1;ring
lemma rotates (F:Tet→G.ColorIndex→V): ∑ i:T,∑ j:T,∑ k:T,(↑(Chir.η i j k):ℂ) • cubicP (F i) (F j) (F k)= (6:ℂ) • cubicP (F 0) (F 1) (F 2):= by
   have h0 : loop 0=1:= rfl; have h1 : loop 1=2:=rfl; have h2 : loop 2=0:=rfl; have h: (2:T)≠0:= by decide
   have hp:(1:T)≠2:=by decide
   norm_num [sum3,Chir.η,h0,h1,h2,Chir.ℓ,h,h.symm,hp,hp.symm]
   rw [cubic_minus (f:=F 0) (g:=F 2),cubic_minus (f:=F 1) (g:=F 0),cubic_minus (f:=F 2) (g:=F 1), ← Sage.crest (F 0) (F 1) (F 2), Sage.crest (F 2) (F 0) (F 1)]; let x:= cubicP (F 0) (F 1) (F 2); module
end
lemma Bsp : Bpol G=Complex.ofReal boostB • ward G:= by unfold Bpol; rw [rotates (fun i:Tet=>nor 1 i)]; simp_rw [show ∀ i:Tet,(nor 1 i)=(rayS:ℂ) • Emitter (G:=G) 1 i from fun _=>rfl,grow]; unfold boostB ward; push_cast; rw [smul_smul]
lemma Usp : Upol G=Complex.ofReal boostU • tune G:= by unfold Upol tune nor boostU; simp_rw [smul_mul_assoc,mul_smul_comm,smul_smul,Finset.smul_sum,Complex.ofReal_mul,Complex.ofReal_pow]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> ?_; rw [smul_smul, ← sq]; push_cast; rfl
end YM.PositionX.Bend
