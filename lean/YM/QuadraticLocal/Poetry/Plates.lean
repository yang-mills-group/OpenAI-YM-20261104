import YM.QuadraticLocal.Poetry.Helmet
import YM.QuadraticLocal.Sunrise.Plaza
/-!
# Symbolic acacia: later grades needs licensed stencil estimates in cover norm.
Produce together with Vernal for reuse.S.Loir. any side.
 **Physical basis already chosen**: this geometry width rep from true Atom.q. λ.Sumes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Poetry.Dais
open Function Filter Lattice Laurent Wilson RG Gauge Precision Tree Exterior
open Matrix Finset Push Uniform
open AbsoluteSums AllOrder AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Fire PertExtension.Series Radial
open AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Money
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open Sunrise Sunrise.Focus Stationary
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {V G0:Type} {ι α M: Type}[Fintype M][Fintype α][DecidableEq M] {G:Gauge} {a C D b:ℝ} {n m:Side}{k d N:ℕ}
local notation "Ω" => (Coarse G ⊕ M)
local notation "Z"=> Point M
local notation "E"=> Point (Coarse G⊕M)
open Picket Rovers
variable (p:Atom G k)(x:Site n)(x':Site m)(r:ℕ)
-- explicit LOCAL lookup projection already exactly at Life.Ledger.
def field (d:ℕ)(G:Gauge): Finset (Point (Coarse G)):= Lattice.box d ×ˢ Finset.univ
local notation "H" d:max=> Dais.field d G
omit [Fintype M] [Fintype α] [DecidableEq M] -- no includes.When namespace ends
-- power.Clock.C.D
lemma plaza (d:ℕ): (field d G).card=(2*d+1)^4*(Fintype.card (Coarse G)):=by rw [field,card_product,← Fintype.card_coe,Audience.portrait_card,card_univ]
lemma seat (x:Cover)(hx:size x≤d)(i:Coarse G): (x,i)∈field d G:=by
 refine Finset.mem_product.mpr ⟨?_,mem_univ _⟩; rw [Lattice.box_test]; have h(i:Axis):(x i).natAbs≤d:= (Finset.single_le_sum (f:=fun i=>(x i).natAbs) (fun i _=>Nat.zero_le _) (Finset.mem_univ i)).trans hx; dsimp only; exact ⟨fun i=>by have hh:= h i; omega,fun i=>by have hh:=h i; omega⟩
lemma width (h:8*d<n.val): Set.InjOn (stood (α:=Coarse G) x) (field d G):= by
 intro i hi j hj he; have hx : wrap n i.1= wrap n j.1:= add_left_cancel (congr_arg Prod.fst he); have hh(i:Point (Coarse G))(hi:i∈field d G): lift (wrap n i.1)=i.1:= FreeResolvent.size_centers n i.1 (FreeResolvent.Lifted.fit_box i.1 d (mem_product.mp hi).1) (by omega); exact Prod.ext (((hh i hi).symm.trans (congr_arg lift hx)).trans (hh j hj)) ((show (AllOrder.Ink.stood x i).2=(AllOrder.Ink.stood x j).2 from congr_arg Prod.snd he))
lemma talk (hx:p.length≤ d){V:Link G n}{W:Link G m}(he:∀ i∈H d, V (stood x i)= W (stood x' i)) : Helmet.frame p x V=Helmet.frame p x' W:= by
 unfold Helmet.frame Atom.unmasked; apply congr_arg p.poly; ext1 i; apply (p.leg i).covered; intro e he' hE'; let a:=e.2; let z:=e.1; have hh : size z≤ d:=by have h:= Extra.Iteration.Derivs.stencil_length (p.leg i) _ he'; let hm : (p.leg i).length≤ p.length:= Finset.single_le_sum (f:=fun i=>(p.leg i).length) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i); exact h.trans (hm.trans hx)
 change input G n V _=input G m W _; rw [encode_link, encode_link]; apply congr_arg G.lieExp; ext1 j; simpa [z,a,Ink.stood,arm_apply,Lattice.expandAt,add_comm] using he (z,Exterior.coord a,j) (seat _ hh (Exterior.coord a,j)) -- note z let.Materialize equality.
open Comparison.Density.Render AnalyticBridge.SectorAffine.Offset
-- Law no need Infinity.Fib count outside Fame.Le.Weed.
def colorL (G:Gauge)(n:Side) : Link G n →L[ℝ] Directions G n:= ContinuousLinearMap.pi fun i=> ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:Exterior.Body 1 n => G.Color) (i.1,Exterior.coord i.2) ∘L (arm G n 1).toContinuousLinearMap
local notation "Ct"=> Fintype.card G.ColorIndex
lemma normC : ‖colorL G n‖ ≤ Ct+1:= by
 apply ContinuousLinearMap.opNorm_le_bound _ (by positivity); intro f; apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro i; let q:= (arm G n 1 f) (i.1,Exterior.coord i.2); change ‖(q:G.Color)‖≤ _; rw [← Texture.baseC (G:=G) q]; refine (norm_sum_le ..).trans ((Finset.sum_le_sum (s:=univ) (g:=fun _=> ‖f‖) (fun j _=>?_)).trans ?_); · rw [norm_smul,OrthonormalBasis.norm_eq_one,mul_one]; exact norm_le_pi_norm f (i.1, Exterior.coord i.2,j)
 simp; gcongr; simp -- syntax
lemma spends (r:ℕ) : Allows r (Helmet.frame p x) 0 ((Ct+1:ℝ)^r* Comparison.Density.Render.fareAt p r):= by
 let K₀:= colorL G n; let C:ℝ:= Ct+1; have hh:Through r (fun y: Directions G n=> p.unmasked (increment 1 y) x) 0 (fareAt p r):= Comparison.Density.Render.reserved p x (by simp); let f:=fun y:Directions G n=>p.unmasked (increment 1 y) x; have h₀:1≤C:= le_add_of_nonneg_left (Nat.cast_nonneg _)
 refine ⟨(Helmet.frameGrade p x).smooth,fun i hi=>?_⟩; change ‖iteratedFDeriv ℝ i (f ∘ K₀) 0‖ ≤ _; rw [Next.Foundations.jets_linear K₀ _]; swap; · exact hh.smooth.of_le (by exact_mod_cast hi)
 rw [mul_comm ((Ct+1:ℝ)^r)]; apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans; refine mul_le_mul (hh.pay i hi) ?_ (prod_nonneg (fun _ _=>norm_nonneg _)) hh.nonneg; rw [prod_const,card_univ,Fintype.card_fin]; exact (pow_le_pow_left₀ (norm_nonneg _) normC _).trans (pow_le_pow_right₀ h₀ hi)
end YM.QuadraticLocal.Poetry.Dais
