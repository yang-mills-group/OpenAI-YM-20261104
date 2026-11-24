import YM.RegulatorIR.Quadratic.Plains
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Reconstruct charge $Q_r$ from genuine Wilson predictor branch
Local response independent of coupling scale. No assuming quotient/cutoff limit
formula in stiffness bind. `fringe` is the native-cover version. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Quadratic
open Lattice Function Budget Motion Budget.Layer Budget.Packet Budget.Deck Step Diagram RG Binding Filter Tree Tree.Forest Metric Set Geometry Geometry.Field PertExtension Chart Laplace GaussianScore Matrix Wilson Orb Series PertExtension.Series.Radial Diagram.Formal Exterior Push
open scoped NNReal ENNReal Topology Real Classical BigOperators ContDiff PowerSeries Matrix Matrix.Norms.Frobenius
variable {G:Gauge}{X Y I J:Type}{P:ℝ}{f c:Side}
variable {S: StepData c f}{A:Deck P I X}{B:Deck P J Y}

def bridge (A: Deck P I X)(x:X→ℝ)(w:I):= A.orient w*x (A.orbit w)
def finer (Q : I→J→₀ ℝ) : Layer I J:= fun x y=> Q x y
abbrev combo (w:X→ℝ):= Finsupp.linearCombination ℝ w
lemma frontier [Fintype Y] (Q : I→ J→₀ ℝ)(w:Y→ℝ)(x:X): ((fmat A B (finer Q)) *ᵥ w) x = combo (bridge B w) (Q (A.place x)):=by
 let V:= Q (A.place x); let T (u:J):= V u*B.orient u*w (B.orbit u)
 have hx i (hi:i∉V.support): T i=0:=by rw [show T i= _ from rfl]; unfold T; rw [Finsupp.notMem_support_iff.mp hi];ring
 have He:HasSum T (combo (bridge B w) V):=by
    convert hasSum_sum_of_ne_finset_zero (L:=SummationFilter.unconditional _) (s:=V.support) hx using 1
    rw [combo,Finsupp.linearCombination_apply]; exact Finset.sum_congr rfl fun i _=>by unfold T; change V i*(B.orient i* w (B.orbit i))=_;ring
 have hz:= He.tsum_fiberwise B.orbit; rw [← hz.tsum_eq, tsum_fintype]; apply Finset.sum_congr rfl; intro i _
 change (∑'v:Stalk B.orbit i, paint A B (finer Q) (A.place x) v.val) * _= _; rw [← tsum_mul_right]; apply tsum_congr;intro a; change _*w i= T a.val; unfold T paint;rw [a.property, A.north,one_mul];rfl

abbrev Carto (G:Gauge)(l P:ℝ)(H: Even f.val)(hc:l*f.val=P):Deck P (Long G.ColorIndex) (Book G f) :=Geometry.Cart l P G.ColorIndex H hc

section Paths

def spineK (i: X) (x:Cover) : Walk→ Long X→₀ ℝ
 | []=>0
 | a::l=>(let t:=Finsupp.single (a.used x,i) (1:ℝ); if a.neg then -t else t) + spineK i (x+a.vec) l
lemma spinal (i:X) (x:Cover)(w:Walk)(g:Long X→ℝ): combo g (spineK i x w)=linkSum (fun z=>g (z,i)) x w:=by
 induction w generalizing x with
 | nil=>rw [spineK, map_zero]; rfl
 | cons a w ih=> rw [linkSum,spineK,map_add,ih];dsimp only;split_ifs <;> simp [combo]
lemma walks_cover (g: Edge (Site f) →ℝ)(i:Cover)(w:Walk): linkSum (g ∘ around f) i w= linkSum g (wrap f i) w:=by
 induction w generalizing i with
 | nil=>rfl
 | cons a w ih=> rw [linkSum, linkSum, ih,map_add, wrap_vec]; unfold Function.comp;
                   congr 2 <;> cases a <;> unfold Lattice.Step.used around <;> split <;> simp
lemma firebrand {l : ℝ}(H:Even f.val)(hz:l*f.val=P)(x:Horizon G f) i t: bridge (Carto G l P H hz) (paper G f x) (t,i) = (fire x (around f t)) i:=by
 change Geometry.shade f t * x _ i=_; unfold Geometry.shade fire; split
 · rw [one_mul]; rfl
 rw [neg_one_mul]; rfl

-- response as Path derivative. `probe` matrix literal weights and centering.
variable (S:StepData c f)

def tex (S:StepData c f)(x : Cover) (a : S.patch.Points) := a.val + S.ratio.count.val • x

def tauK (x:Cover)(a:S.patch.Points)(i:X) : Long X →₀ ℝ := -((Fintype.card S.patch.Points:ℝ)⁻¹ • ∑ b:S.patch.Points, (Fintype.card Lattice.Order:ℝ)⁻¹ • ∑ j:Lattice.Order, spineK i (tex S x a) (route a.val b.val j))
def anchorK (x:Cover)(i:X) : Long X→₀ ℝ := tauK S x S.patch.center i - ∑ b, S.patch.weight b • tauK S x b i

def fringe (S:StepData c f) : Long X→Long X→₀ ℝ := fun p=> let i:=p.2; let v:=p.1.2; let x:=p.1.1; (∑ b,S.patch.weight b • spineK i (tex S x b) (S.repath v)) + (anchorK S (x+step v) i -anchorK S x i)

lemma tex_wrap (x:Cover)(a:S.patch.Points) : wrap f (tex S x a)=Precision.atPoint S (wrap c x) a := by rw [tex,map_add,← Ratio.embed_wrap];rfl
variable {l:ℝ}(H:Even f.val)(hc:l*f.val=P)(x:Horizon G f)(i:G.ColorIndex)
local notation "g" => bridge (Carto G l P H hc) (paper G f x)
local notation "L" => parts G 1 (canvas x) i
lemma there (u:Cover) (a : S.patch.Points) (w:Walk): combo g (spineK i (tex S u a) w) = Precision.integralLink (Precision.atPoint S (wrap c u) a) w L:=by
 rw [spinal]; simp_rw [firebrand
 ]; apply Eq.trans (walks_cover (fun j=>(fire x j) i) (tex S u a) w); rw [tex_wrap]; change _= linkSum (fun j=>(canvas x (j.1,coord j.2)) i) _ _; simp only [canvas, show ∀ k:Axis,axisEquiv.symm (coord k)=k from fun j=>axisEquiv.symm_apply_apply _]
lemma fiscal (u:Cover) (a : S.patch.Points) : combo g (tauK S u a i) = Precision.tau S (wrap c u) a L:=by
 unfold Precision.tau tauK; simp only [map_neg,map_smul,map_sum, LinearMap.sum_apply,LinearMap.neg_apply,LinearMap.smul_apply]; simp_rw [there]
lemma landed (u:Cover): combo g (anchorK S u i)=Precision.adjusted S (wrap c u) S.patch.center L:= by unfold anchorK Precision.adjusted; simp only [map_sub,map_sum,map_smul,LinearMap.sub_apply,LinearMap.sum_apply,LinearMap.smul_apply]; simp_rw [fiscal]
lemma chime (e: Edge Cover) : combo g (fringe S (e,i))=(Precision.probe S *ᵥ L) ((around c e).1,coord e.2):=by
 rcases e with ⟨z,v⟩;unfold fringe around Precision.probe; simp only [add_mulVec, Pi.add_apply, ← Matrix.mulVec_mulVec,d_sites,Precision.fixRoot,LinearMap.toMatrix'_mulVec,Precision.mean,LinearMap.toMatrix'_mulVec,LinearMap.pi_apply,LinearMap.sum_apply,LinearMap.smul_apply]; simp_rw [map_add,map_sum,map_smul,map_sub,landed]; rw [map_add,wrap_step]
 simp_rw [show axisEquiv.symm (coord v)=v from axisEquiv.symm_apply_apply _]; simp_rw [there]
-- Jacobian calculation actual
variable (V:S.patch.Branches S.kernel G)
attribute [local instance] Gauge.frobInner
include V
lemma chainO (e:OEdge c)(x:Horizon G f): ((rod G S x) e) i=(Precision.probe S *ᵥ parts G 1 (canvas x) i) (e.val.1,coord e.val.2):=by
 have hp:= Binding.bend S V x e
 simp_rw [Geometry.predictor,mat_expanded,canvas_rate] at hp
 have hh:= (hp.unique (Push.prices S V e.val (directive S) (canvas x))); exact congr_arg (fun v:G.Color=>v i) (G.colorMat_injective hh)

lemma steering {ρ:ℝ}(hp: Even c.val)(h:ρ*c.val=P) : fmat (Carto G ρ P hp h) (Carto G l P H hc) (finer (fringe S)) *ᵥ paper G f x= paper G c (rod G S x):=by
 ext1 i; rw [frontier]; rcases i with ⟨a,i⟩
 change combo _ (fringe S (Geometry.position a,i))=_; rw [chime,position_edge]; exact (chainO S i V a x).symm
end Paths
end YM.RegulatorIR.Quadratic
