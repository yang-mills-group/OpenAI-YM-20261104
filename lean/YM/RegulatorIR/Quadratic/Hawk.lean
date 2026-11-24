import YM.RegulatorIR.Quadratic.Nymph
import YM.RegulatorIR.Binding.Rosette

/-!
# Joint orbit law transported from cover
Orthogonal coordinates on color. Curve and bend on common t plan. The inverse
is only at fixed regulator on its actual tree, no zero-mode assumption. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Quadratic
open Lattice Function Budget Motion Budget.Layer Budget.Packet Budget.Deck Step Diagram RG Binding Filter Tree Tree.Forest Metric Set Geometry Geometry.Field PertExtension Chart Laplace GaussianScore Matrix Wilson Orb
open scoped NNReal ENNReal Topology Real Classical BigOperators ContDiff PowerSeries Matrix
variable {G:Gauge}{X Y:Type}{P:ℝ} {f c:Side}
variable {A:Deck P X (Book G f)}{B:Deck P Y (Book G c)}
section Ortho
variable {E:Type}
def paper (G:Gauge)(f:Side): Horizon G f ≃ₗ[ℝ] (Book G f→ℝ):={
 toFun:=tint G f
 invFun:=fun x i=> WithLp.toLp 2 (fun z=> x (i,z))
 left_inv _:=rfl
 right_inv _:=rfl
 map_add' _ _:=rfl
 map_smul' _ _:=rfl }
lemma squared (x:Horizon G f): paper G f x ⬝ᵥ paper G f x=∑ i,‖x i‖^2:=by
 unfold dotProduct; rw [Fintype.sum_prod_type]; apply Finset.sum_congr rfl; intro i _; rw [EuclideanSpace.real_norm_sq_eq];apply Finset.sum_congr rfl;intro j _; rw [sq];rfl
-- poster row orientation is COARSE/FINE on announcement
variable [Fintype X][Fintype Y][DecidableEq Y]
def lamber (N:Matrix X Y ℝ):Matrix (X⊕Y) (X⊕Y) ℝ:= Matrix.transpose (glued 0 N 0 (1:Matrix Y Y ℝ):Matrix _ _ ℝ)
lemma hose_read (N:Matrix X Y ℝ)(v:Y→ℝ): announce (lamber N) (dilute Embedding.inr v)= Sum.elim (N *ᵥ v) v:=by
 let M:=lamber N; let D:=dilute (I:=Y) (J:=X⊕Y) Embedding.inr v -- wrong name
 ext1 i; unfold announce; rw [Fintype.sum_sum_type]; cases i with
 | inl a=>
    change (∑ x:X,(0:ℝ)*D (.inl x))+(∑ y:Y,N a y * D (.inr y)) = (N *ᵥ v) a
    simp only [zero_mul,Finset.sum_const_zero,zero_add]
    exact Finset.sum_congr rfl fun j _=>congr_arg (N a j * ·) (dilute_here ..)
 | inr b=>
    change (∑ x:X,(0:ℝ)*D (.inl x))+(∑ y:Y,(1: Matrix Y Y ℝ) b y * D (.inr y)) = v b
    simp only [zero_mul,Finset.sum_const_zero,zero_add];simp_rw [show ∀ y:Y,D (.inr y)=v y from fun y=> dilute_here ..]; exact congr_fun (Matrix.one_mulVec v) b
end Ortho
section Strip
variable (S:StepData c f)(F:Forest S.ratio)
def awake (S:StepData c f)(F:Forest S.ratio)(x:Book G f):Prop:= ¬ Field.branch F x.1
def Vertex (K:Horizon G f→ ℝ):Prop:=∀ x,0≤K x∧(K x=0→GradientSite x)

def foresh (G:Gauge) : Meadow G (Wind F) →ₗ[ℝ] (Book G f→ℝ):= (paper G f).toLinearMap.comp (injectX F)
def panes (x:Book G f→ℝ): Meadow G (Wind F):=fun i=> (paper G f).symm x i.val
lemma foresh_p (x:Meadow G (Wind F)) : StripQ (awake S F) (foresh S F G x):= by intro i h; change injectX F x i.1 _=0; rw [show injectX F x i.1=0 from inject_others F x ⟨_,Classical.not_not.mp h⟩]; rfl
lemma foresh_v {x:Book G f→ℝ}(h:StripQ (awake S F) x): foresh S F G (panes S F x)=x:=by
 ext1 i
 by_cases hv:awake S F i
 · change injectX F _ i.1 _=_; rw [show injectX F (panes S F x) i.1=panes S F x ⟨_,hv⟩ from inject_access F _ ⟨i.1,hv⟩]; rfl
 exact (foresh_p S F (panes S F x) i hv).trans (h i hv).symm
end Strip

variable {S:StepData c f}{F: Forest S.ratio}{K N: Matrix (Book G f) (Book G f) ℝ} {L:Matrix (Book G c) (Book G c) ℝ}
variable {Q : Matrix (Book G c) (Book G f) ℝ}{D: Matrix (Book G f) (Book G c) ℝ}
variable (C:GridQ S.kernel.penalty (awake S F) K L Q D N)
variable (hT:∀ x:Horizon G f, Q *ᵥ paper G f x= paper G c (rod G S x))

-- quote current before Haar. Orbit Q term. No reduced sqrt-2.

def beneath (K:Matrix (Book G f) (Book G f) ℝ)(x:Horizon G f):= phase K (paper G f x)

include C hT
omit C in
lemma wages (x:Horizon G f) (y: Horizon G c): heatPay S.kernel.penalty Q (paper G f x) (paper G c y)=feeO S x y:=by rw [heatPay,hT,← map_sub,squared]; unfold feeO;rw [← Finset.sum_div, mul_div_assoc]

omit hT in
lemma stripped (v:Horizon G c):foresh S F G (panes S F (G:=G) (D *ᵥ paper G c v))=D *ᵥ paper G c v:=foresh_v S F (C.clipped _)
variable (Z:Vertex (beneath K))(h:Field.Square F)(hc : Even c.val) (hf:Even f.val) (V:S.patch.Branches S.kernel G)

lemma age (v:Horizon G c)(x:Meadow G (Wind F)) :
 let z:=x+panes S F (G:=G) (D *ᵥ paper G c v)
 beneath K (injectX F z)+feeO S (injectX F z) v=beneath L v+ phase (diagStiff S.kernel.penalty K Q) (foresh S F G x):=by
 intro z; rw [← wages hT]; have hp: paper G f (injectX F z)=foresh S F G x+D *ᵥ paper G c v:=by change foresh S F G (x+_)= _;rw [map_add,stripped C]
 unfold beneath; rw [hp]; exact C.grade _ (foresh_p S F x)
lemma age_low (x:Meadow G (Wind F)): beneath K (injectX F x)+feeO S (injectX F x) 0=phase (diagStiff S.kernel.penalty K Q) (foresh S F G x):=by simpa [show panes S F (G:=G) 0=0 from funext (fun i=> congr_fun ((paper G f).symm.map_zero) i.val),beneath,phase] using age C hT 0 x
lemma age_high (v: Horizon G c) :
 let z:=panes S F (G:=G) (D *ᵥ paper G c v); beneath K (injectX F z)+feeO S (injectX F z) v=beneath L v:=by
 intro z; simpa [phase] using age C hT v 0
include Z h hc hf V
lemma proper (x:Meadow G (Wind F))(hx:x≠0):0<phase (diagStiff S.kernel.penalty K Q) (foresh S F G x):=by
 rw [← age_low C hT]; have he:= feeO_nonneg S (injectX F x) (0:Horizon G _); obtain ⟨hh,h'⟩:=Z (injectX F x)
 by_contra! ht; exact hx (fiber_core V (Q:=h) x (h' (by linarith)) hf hc (feeO_eq S _ _ (show feeO S (injectX F x) 0=0 by linarith)).symm)
omit h hc hf in
lemma aged : Vertex (beneath L):=by
 intro x; let y:= panes S F (G:=G) (D *ᵥ paper G c x); let z:=injectX F y
 have hx:beneath K z+feeO S z x=beneath L x:= age_high C hT x
 rw [← hx]; obtain ⟨hh,h'⟩:= Z z
 have hp:= feeO_nonneg S z x;exact ⟨add_nonneg hh hp,fun ht=> (feeO_eq S _ _ (show feeO S z x=0 by linarith)).symm ▸ gradie_zone S V (h' (by linarith))⟩

-- pose

def stepLaw : Law (Meadow G (Wind F)):= nymph (foresh S F G) _ C.style (proper C hT Z h hc hf V)

omit C hT Z h hc hf V in
def qualify (S:StepData c f) (F:Forest S.ratio) (i:Book G f⊕Book G c):Module.Dual ℝ (Meadow G (Wind F)):=Sum.elim (wing (foresh S F G)) 0 i
lemma believer : Diagram.Gaussian.bond (stepLaw C hT Z h hc hf V) (qualify S F) = petals N:=by
 let M:= stepLaw C hT Z h hc hf V
 have ht i j : M.wick (wing (foresh S F G) i) (wing (foresh S F G) j) = N j i:=by
    exact GridQ.wickN C (proper C hT Z h hc hf V) (foresh_p S F) (fun j=>⟨_,foresh_v _ _ (C.alive j)⟩) _ _ -- check
 ext1 x; ext1 y; cases x <;> cases y <;> rename_i i j
 · rw [Diagram.Gaussian.bond_cross]; exact ht j i
 · rfl -- not defeq Linear 0 reduction check
 · change (qualify S F (.inl j)) (M.inverse 0)=0;rw [map_zero,map_zero]
 rfl

omit Z h hc hf V hT in
lemma qualifies (x:Meadow G (Wind F))(v:Horizon G c):
 let z:=x + panes S F (G:=G) (D*ᵥ paper G c v)
 announce (lamber D) (dilute Embedding.inr (paper G c v)) + (fun i=>qualify S F i x)=Sum.elim (foresh S F G z) (paper G c v):=by
 intro z; rw [hose_read,show foresh S F G z= _ from (foresh S F G).map_add _ _,stripped C v]
 ext1 i;cases i with
 | inl i=> exact add_comm ..
 | inr i=> exact add_zero _
end YM.RegulatorIR.Quadratic
