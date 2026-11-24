import YM.MS.Theater.RakeA
import YM.Labels.Basis
/-!
# Label polynomials in the real-coordinate conventional alphabet and the momentum image
 Before applying color. Bihomogeneous.Emit.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Theater
open Set Function Filter Finset Metric MeasureTheory Real Maxwell Labels
open Analysis Tensor Koszul Plane Landau Detect Detect.Mark Local.BV InnerProductSpace Submodule Momentum Local Woven
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {G:Gauge}{d h n r:ℕ}{p b:Pol G}
local notation "K"=> (field (P:=FourP) ( Landau.parity ( A:=Axis ) ( C:=G.ColorIndex) ) )
local notation "ζ"=> Koszul.mono
local infix:70 " ⋆ "=> product K
abbrev pick (i:Key G): Witness G i.1:= Complex.ofRealCLM.toLinearMap.comp (( Labels.axes G i.1 ).coord i.2 )
abbrev lamp (i:Key G) : Local.BV.Grade G:= RowLeg G i.1 ( pick i )
lemma shadow_ω (i:Key G): Horizontal (lamp i) ( generation i ):= by convert! wholeℓ ( pick i ) using 1
-- Φ image.R.Clock
abbrev hands (G:Gauge):= field (P:=FourP) ( Landau.parity ( A:=Axis ) ( C:=G.ColorIndex) )
abbrev paint (i:Key G): ↥(Dark ( hands G )):= ⟨ ζ ( lamp i ),lying ( shadow_ω i ).1 ⟩
def opA (G:Gauge): Pol G →ₐ[ℂ] ↥(Dark (hands G)):= MvPolynomial.aeval paint
def orbit (G:Gauge): Pol G →ₗ[ℂ] Law G:= (( Dark ( hands G ) ).subtype).comp (opA G).toLinearMap
lemma bag (p:Pol G)(t: Legs ( Lane4 G )): orbit G p t=(opA G p).val t:= rfl
lemma bags (p q:Pol G): orbit G ( p*q )= orbit G p ⋆ orbit G q:= by change (opA G ( p*q )).val=_; rw [map_mul]; rfl
lemma cus (x:ℂ): orbit G ( MvPolynomial.C x )= coin x:= Eq.trans (congr_arg Subtype.val (MvPolynomial.aeval_C (R:=ℂ) (f:= paint) ..)) (cash1 ..) -- args
lemma cusp (i:Key G): orbit G ( MvPolynomial.X i )= ζ ( lamp i ):= congr_arg Subtype.val (MvPolynomial.aeval_X paint i)
lemma band0 (x:ℂ): coin (A:=Lane4 G) x=x • hit:= by rw [unitθ]; ext l; cases l; exact (mul_one x).symm; exact (mul_zero x).symm
-- weighted mono.P induction with cap. all uses p arguments in transitions.
section Bi
local notation "δ"=> (Labels.bidegree (G:=G))
abbrev charge (G:Gauge)(p:ℕ×ℕ): Submodule ℂ ( Pol G ):= MvPolynomial.weightedHomogeneousSubmodule ℂ Labels.bidegree p
abbrev At (p:Pol G)(r:ℕ×ℕ): Prop:= p∈ charge G r
lemma nodeId (f:Pol G)(u:ℕ×ℕ): At f u ↔ Labels.pureDegree f u.1 u.2:= Iff.rfl
-- fiber induction ($m all).
variable {X: ℕ×ℕ}
-- cap later constrain x≤H.V.
lemma measureN (H:ℕ×ℕ→Pol G→Prop) (q: (Key G→₀ℕ)) (z:ℂ) (hc:H 0 ( MvPolynomial.C z ))(hv:∀ x i (f:Pol G),At f x→ H x f→ H (δ i+x) ( MvPolynomial.X i*f )): H (Finsupp.weight δ q) ( MvPolynomial.monomial q z ):= by
    induction q using Finsupp.induction with
    | zero=> rw [map_zero]; exact hc
    | @single_add a e p _ he h=>
        -- assume p.F.Bounds
        have hx (e:ℕ): H ( Finsupp.weight δ ( Finsupp.single a e+p ) ) ( MvPolynomial.monomial ( Finsupp.single a e+p ) z ):= by
            induction e with | zero=> simpa using h | succ e iH=>
                have he : Finsupp.single a (e+1)+p= Finsupp.single a 1+(Finsupp.single a e+p):= by rw [ Finsupp.single_add ]; abel
                rw [he,map_add, Finsupp.weight_apply ]; -- simplify single weight
                obtain ht:= hv _ a _ ( show At ( MvPolynomial.monomial ( Finsupp.single a e+p ) z ) _ from MvPolynomial.isWeightedHomogeneous_monomial δ ( Finsupp.single a e+p ) z rfl ) iH; convert! ht using 1; · simp
                rw [ MvPolynomial.X, MvPolynomial.monomial_mul ]; simp -- names
        exact hx e
lemma axisI (H:ℕ×ℕ→Pol G→Prop)(hp: At p X) (hc:∀ c,H 0 (MvPolynomial.C c))(hz: ∀ i,H i 0)(hv:∀ x i (f:Pol G),At f x → H x f→ H (δ i+x) ( MvPolynomial.X i*f ))(hf: ∀ x (f g:Pol G), At f x→ At g x → H x f→ H x g→ H x ( f+g )): H X p:= MvPolynomial.IsWeightedHomogeneous.induction_on (motive:=fun p _=> H X p) (hz _) ( hf X ) (fun d c he=> he ▸ measureN H d c ( hc c ) hv ) ( nodeId _ _ |>.mp hp ) -- orientation
end Bi
lemma setting_K (hp: At p (d,h)): orbit G p∈ Carry G d h ∧ Woven.sym (orbit G p) := by
   let H(i:ℕ×ℕ)(p:Pol G): Prop:= orbit G p∈ Carry G i.1 i.2∧ Woven.sym ( orbit G p ); apply axisI H hp (fun i=> ?_) ( fun i=>?_) ( fun x i f hx hh=>?_) (fun x q v h hv hq hh=>?_);
   · unfold H; rw [cus]; exact ⟨ by rw [band0]; exact smul_mem _ _ inside0, coin_symm _ ⟩
   · unfold H; rw [map_zero]; exact ⟨ zero_mem _, Koszul.Symm.zero⟩
   · unfold H at *; rw [bags,cusp]; rw [Prod.fst_add,Prod.snd_add,Nat.cast_add, add_comm _ x.2 ]; exact ⟨ continue_C (shadow_ω i) hh.1,symθ.times hh.2⟩
   unfold H at *; rw [map_add]; exact ⟨ add_mem hq.1 hh.1,hq.2.add hh.2 ⟩
end YM.MS.Theater
