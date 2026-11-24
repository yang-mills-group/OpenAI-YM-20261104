import YM.MS.Orbit.Mold
/-!
# Site Fourier-plane ordinary covariance. Volume factors reciprocal. Mark periods may differ.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Orbit
open Set Function Filter Finset Metric MeasureTheory
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Snap Native Lattice City Latch Flux
open scoped Topology ContDiff Interval
variable {G:Gauge}{A: Type}{P Q: Latch.Edge G}{n:Side}
abbrev scaleZ (n:Side):ℂ:=(νt n:ℂ)
def iota (G:Gauge)(n:Side): Cog (field parity (A:=BH G) (P:=Site n)) := by
    refine { mode:= fun x : FixedMode G n=> reverseX x,spin:=fun x:FixedMode G n=>switch (addr x), vivid:=fun x=>rfl, perm:=fun x=>?_ ,holo:=?_ }
    · exact Prod.ext rfl (neg_neg x.2)
    intro x; change switch (x.1,Coord x.2)*switch (x.1, Coord (-x.2)) =1; have hh:= switch_pin x.1 (ξ_neg x.2); rw [ ← (show _=switch _ from hh) ]; exact turnβ (addr x)
lemma iota_mode (x: FixedMode G n): (iota G n).mode x=(x.1,-x.2):=rfl
lemma iota_spin (x: FixedMode G n): (iota G n).spin x=switch (addr x):=rfl
-- use b ghost flag
abbrev EdgeV (n:Side)(P: Latch.Edge G): Flux (BH G) (Site n) ℂ:= fun i j p=> scaleZ n * P i j (Coord p)
def SpeaksI (P:Latch.Edge G): Prop:= ∀ i j p, P i j (-p)=P i j p*(switch (i,p) * switch (j,-p))
lemma edge_rev (h:SpeaksK P)(hp:Reverse P parity): Reverse (EdgeV n P) parity:= by intro i j p; unfold EdgeV; rw [ ← h i j (ξ_neg p), hp ]; ring
lemma edge_cl {b:Bool}(hp:closed P parity b): closed ( EdgeV n P ) parity b := fun _ _ _ h=> hp _ _ _ ( right_ne_zero_of_mul h )
abbrev σbranch (i:FixedMode G n):= field parity i
-- bare line.Ext.V. for Pl.Unit
structure Twig (K:Latch.Edge G): Prop where
    pin : SpeaksK K
    t : Reverse K parity
    close : closed K parity false
    gov : SpeaksI K
-- Absolute flow line
abbrev LaceL (G:Gauge)(t:ℝ):= dope (Cpu G t)
lemma foe (G:Gauge)(t:ℝ): Twig (LaceL G t):= ⟨ speak_d ( L_stamp t ),Dk_rev ( Vrev G t ), Dk_cl ( X_even G t ),scoreD t⟩
-- using q=-q.Rel.K
open Cog
variable (n)
def mat (K:Latch.Edge G): Grain (FixedMode G n) := fun x y=> if x.2= -y.2 then EdgeV n K x.1 y.1 x.2 else 0
abbrev Paper (b:Bool)(K: Latch.Edge G):= imageV (iota G n) b (mat n K)
variable {n}
lemma riverOK (h:SpeaksK P)(hk:SpeaksI P): (iota G n).phase (mat n P):= by
    intro i j; rcases i with ⟨i,p⟩; rcases j with ⟨j,q⟩; unfold mat; simp only [iota_mode,iota_spin, neg_inj]; by_cases he:p= -q; swap; · rw [ if_neg he, if_neg he, zero_mul ]; -- hp simp?
    obtain rfl:= he; rw [if_pos rfl, if_pos rfl ]; unfold EdgeV; rw [ ← h i j (ξ_neg (-q)), hk ]; obtain hz:= switch_pin j ( ξ_neg (-q) ); rw [neg_neg] at hz; change scaleZ n*_ = scaleZ n* _ *( _ * switch (j,Coord q)); dsimp only at hz; rw [ ← hz, mul_assoc (scaleZ n) ]
lemma stampL (h:SpeaksK P)(hp: Reverse P parity): Cog.Sym  σbranch ( mat n P ) := by -- wrong binder
   intro x y; unfold mat; by_cases hv:x.2= -y.2; · rw [if_pos hv,if_pos (by rw [hv,neg_neg]),hv,edge_rev h hp ]; -- type rewrite deteriorates
   rw [if_neg hv, if_neg (fun he=> hv (he ▸ neg_neg _|>.symm)),mul_zero]
lemma evenK (hx:closed P parity false): Clear σbranch ( mat n P ):= by
    intro x y he; unfold mat at he; split_ifs at he; swap; · exact False.elim (he rfl)
    obtain hv:= edge_cl (P:=P) hx _ _ _ he; cases h:parity x.1 <;> cases h':parity y.1 <;> ( ( change parity x.1=parity y.1; rw [h,h'] ) <;> (simp only [ h,h' ] at hv; cases hv) )
lemma readsK (hx: closed P parity false)(b:Bool): Clear σbranch ( Paper n b P ):= by cases b; exact evenK hx; exact clearC (S:= iota G n) ( evenK hx )
-- evaluate sums
variable {E:Type}[AddCommMonoid E][Module ℂ E]
abbrev valueI (K:Latch.Edge G) (a b:BH G)(p:QP):= K a b p * switch (b,-p)
abbrev ηbone (b:Bool) (K:Latch.Edge G): Latch.Edge G:= if b then valueI K else K
lemma picture (h:SpeaksK P): SpeaksK ( valueI P ):= fun i j _ _ hp=> congr_arg₂ (· * ·) (h i j hp) ( switch_pin _ (hp.opp)) -- type val coercion curried.
lemma StraightFocus (V: FixedMode G n→FixedMode G n→ E): (∑ i: FixedMode G n, ∑ j: FixedMode G n, mat n P i j • V i j )= ∑ p:Site n,∑ i:BH G,∑ j:BH G, (scaleZ n * P i j (Coord p)) • V (i,p) (j,-p) := by
   have he(i j:BH G)(p:Site n): (∑ q:Site n, mat n P (i,p) (j,q) • V (i,p) (j,q))= (scaleZ n *P i j (Coord p)) • V (i,p) (j,-p):= by
      unfold mat; simp_rw [ ite_smul, show ∀ x:Site n, p= - x ↔ x= -p from (fun q=> ⟨fun h=>by rw [ h,neg_neg ], fun h=>by rw [ h,neg_neg ] ⟩), zero_smul ]; rw [ Finset.sum_ite_eq']; rw [if_pos (Finset.mem_univ _)]; -- Hp
   simp_rw [ Fintype.sum_prod_type (γ:=E) (α₁:=BH G) (α₂:=Site n), he ]; exact Finset.sum_comm -- lhs exact?
lemma ImageFocus (V:FixedMode G n→FixedMode G n→ E): (∑ i:FixedMode G n,∑ j:FixedMode G n, imageW (iota G n) (mat n P) i j • V i j) = ∑ p:Site n,∑ i:BH G,∑ j:BH G, (scaleZ n * valueI P i j (Coord p)) • V (i,p) (j,p) := by
   have he (i j:BH G)(p:Site n):(∑ q:Site n, imageW (iota G n) (mat n P) (i,p) (j,q) • V (i,p) (j,q)) = (scaleZ n * valueI P i j (Coord p)) • V (i,p) (j,p) := by
       unfold imageW; simp only [ iota_mode,iota_spin, mat, neg_neg, ite_mul, zero_mul, ite_smul, zero_smul ]; rw [ Finset.sum_ite_eq , if_pos (Finset.mem_univ _) ]; have hx := switch_pin j (ξ_neg p); unfold EdgeV valueI; rw [mul_assoc]; exact congr_arg ( · • V (i,p) (j,p) ) (congr_arg (scaleZ n * · ) (congr_arg ( P i j ( Coord p ) * · ) hx.symm))
   simp_rw [ Fintype.sum_prod_type (γ:=E) (α₁:=BH G) (α₂:=Site n), he ]; exact Finset.sum_comm
end YM.MS.Orbit
