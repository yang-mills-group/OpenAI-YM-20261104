import YM.RegulatorIR.Skein.Vary

/-!
# Funding W1 Γ on vacuum. Both payload choices allowed; no signed
 averaging prerequisite. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Skein
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Gradient Train Pupil Cluster
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries
variable {G:Gauge}{X Y Z I:Type} {P:ℝ} {c f:Side}{e i r b j k:ℕ}

section Columns
variable {L M l:ℝ}{d c:ℝ≥0∞}
-- combined
structure Merit (D:Layer (Foot G) (Foot G))(V:Gain.Bride G)(ℓ:Tariff Room)(l:ℝ)(y:Foot G→Room)(c d:ℝ≥0∞): Prop where
 beam : Layer.row D ℓ (localL l) y c ∧ Layer.row (swap D) ℓ y (localL l) c
 flows : Layer.row V ℓ (Gain.pointS l) y d ∧ Layer.row (swap V) ℓ y (Gain.pointS l) d

def surf (G:Gauge)(b:ℕ)(c d:ℝ≥0∞) := c+2^b*d + (c*Fintype.card G.ColorIndex+d*2^b*(4*Fintype.card G.ColorIndex))
def staff (G:Gauge)(b i:ℕ) (c d:ℝ≥0∞) := (Fintype.card (Tuple (Mood G) (i+1))+1:ℝ≥0∞)*Gain.hatchV G i*(surf G b c d)^(i+1)
lemma staffed (G:Gauge)(i b:ℕ)(hc:c≠⊤)(hd:d≠⊤): staff G b i c d≠⊤:=by unfold staff surf; have hx:=Gain.hatch_fin G i; finiteness

variable {J:Layer (Foot G) (Foot G)}{V:Gain.Bride G}{y:Foot G→Room}(h:0<l)(hk:l≤ L)
local notation "T" => Tariff.native L (h.trans_le hk) b
lemma published (i:ℕ)(H:Merit J V (Tariff.native L (h.trans_le hk) b) l y c d): Curves (halo J V) T (localL l) y i (staff G b i c d):=by
 let v:= surf G b c d
 let K(x:Foot G):= tubeL J V x.1
 have hr: tileS K T (localL l) y v:=by intro w; exact ⟨(fun x=> (stride J V h hk y H.beam.1 H.flows.1 x w).trans le_self_add), fun t=> (colB h hk c d y H.beam.2 H.flows.2 w t).trans le_add_self⟩
 let F(x:Foot G):= pet G x.2 i; have hP(x):quota (F x) 1≤ hatchV G i:= hatch_ge ..
 let c':ℝ≥0∞:=Fintype.card (Tuple (Mood G) (i+1)); let d':= hatchV G i
 constructor
 · intro x; apply le_trans (fabric hr F hP x); change _ ≤ (c'+1)*_ * _; apply mul_le_mul_left; exact (mul_one d').ge.trans ((mul_comm d' 1).le.trans (mul_le_mul_left le_add_self d')) -- eq ge direction
 intro j x; apply le_trans (wool hr j x _ F hP); change c'*d'*_ ≤ (c'+1)* _ * _; exact mul_le_mul_left (mul_le_mul_left le_self_add d') _
end Columns
section Std
variable {T F: Type} (V:T→ G.Color)(i: G.ColorIndex)
-- equivalence multiple costs
lemma stalkCost (h:∀ j:G.ColorIndex, (∑' x, ‖V x j‖ₑ)≠⊤) : (∑' x, ‖V x‖ₑ)≠⊤:=by
 let a(x:T):=∑ j:G.ColorIndex,‖V x j‖ₑ
 have hx:(∑' x,a x)≠⊤:= by unfold a; rw [Summable.tsum_finsetSum (fun j _=> ENNReal.summable)]; exact ENNReal.sum_ne_top.mpr fun i _=>h i
 apply ne_top_of_le_ne_top hx; apply ENNReal.tsum_le_tsum; intro x
 let B:= EuclideanSpace.basisFun G.ColorIndex ℝ
 rw [← (B).sum_repr (V x)]; rw [B.sum_repr] -- rw issue
 calc
    _ = ‖∑ i:G.ColorIndex,(V x i) • (B i)‖ₑ:=by congr 1; exact Eq.symm (B.sum_repr (V x))
    _ ≤ _:=by apply (enorm_sum_le ..).trans; apply Finset.sum_le_sum; intro i _;rw [enorm_smul,← ofReal_norm (B i),B.norm_eq_one, ENNReal.ofReal_one,mul_one]
variable [Fintype I]
lemma spot_cost (E:I↪ Y)(w:I→ℝ)(P:Layer (T×G.ColorIndex) Y)(h:Billed (swap P)): (∑' x:T, ‖(WithLp.toLp 2 (fun i:G.ColorIndex=> scanL P (dilute E w) (x,i)):G.Color)‖ₑ)≠⊤:=by
 apply stalkCost _
 intro i; let a(x:T)(v:I):=P (x,i) (E v)*w v; apply tsum_enorm_ne_top_iff_summable_norm.mpr
 change Summable fun x:T=> ‖scanL P (dilute E w) (x,i)‖; simp_rw [←gated]; apply Summable.norm (summable_sum ?_)
 intro v _; have hf : Summable (fun k=>P k (E v)):= quota_summable (w:=1) (fun _=>le_rfl) (h.rows _); exact (hf.comp_injective (f:=fun k=> P k (E v)) (i:=fun x:T=>(x,i)) (fun i j h=>Prod.mk.inj h |>.1)).mul_right _
end Std
section Along
variable {A:Deck P (Foot G) (Book G f)}{B:Deck P (Foot G) (Book G c)} (D:GridStep A B)(J:Layer (Foot G) (Foot G))(V:Gain.Bride G)
local notation "R" => grain D J V
lemma tourist (hx:Billed (swap J)) : Acres (grain D J V).straight e:=by
 intro i hi x; by_cases ht:i=0
 · subst i; exact hx.rows (x 0) -- iter simpl?
 unfold Strip.straight Step.inert; simp [ht]

variable (hx:Billed (swap J))(ht:Billed (swap V))
include hx ht
lemma tilts {T:Orders (Foot G)} (h:W1 T e)(hT:∀ i≤ e,∀ r,Limits (T i r)): Voice (R).space (R).straight T 2 e:=by
 intro L x i hi;let F:= Cluster.Brief.tile L;rw [stylist,setup]; exact knowsL h _ _ (spot_cost F x _ hx) (spot_cost F x _ ht) hT hi
lemma consort {T:Orders (Foot G)} (h:W1 T e)(hT:∀ i≤e,∀ r,Limits (T i r))(hp:Acres (halo J V) e)(H:Ranks 2 T) (hv:i ≤ e): (R).Way T i:=by -- i implicit nat
    exact (cloister (R).space hp T hT H (tourist (e:=e) D J V hx) (tilts D J V hx ht h hT) hv).symm -- signature check
end Along
end YM.RegulatorIR.Skein
