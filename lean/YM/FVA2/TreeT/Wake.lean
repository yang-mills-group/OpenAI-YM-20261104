import YM.FVA2.TreeT.Pulse
import YM.FVA2.Lambda.Pure
/-!
# Extracting the top rank

`signature`: no change to the starting stencil on these rays, in `torch`.
(Including all the nonlinear pieces contributing to this evaluation.)
Use with the proof of `treeOK`.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.TreeT.Wake
open Function Filter Set Finset MeasureTheory Real
open Lattice MS MS.Plane MS.Momentum MS.Koszul MS.Native MS.Landau MS.Tone MS.Tone.Frame MS.Native.Wilsonian MS.Book MS.Book.Convolve MS.Book.Program
open MS.City MS.Heat MS.Heat.Signal MS.Wind MS.Menus MS.Landau.Detect MS.Cylinder MS.Cylinder.Lab
open MS.Native.Paint MS.Native.Orient MS.Local.Physical MS.Lifting MS.Land MS.Outlook MS.Emit MS.Wind.Leading
open Teller Graft Capacity Desk Lambda
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{n d k r:ℕ}{b:Bool}{p:Team}{F:T (Dot G Cover)}{t x:ℝ}{l:List (Lane4 G)}
variable {B:Deck G} {j:Glyph B d} (V:FullBook B) {A:Acts B d}
lemma alone (p:Team)(h:l.length=r+n) (he:∀ n, Limit ( F n ).val (r+(n:ℤ))): run (wobble G p x F n) l=run ( F n ) l:= by
 unfold wobble; rw [LinearMap.comp_apply, rolls,map_sum,Finset.sum_apply, Finset.sum_eq_single (0,n),frame_clock]
 · rw [rules,map_sum, Finset.sum_apply, Finset.sum_eq_single n ]; · rw [ show Program.cut ( Program.shift p x ) n n=1 from (Reg.Token.stamp_n _ ( share .. ) n).trans (by rw [ann, one_pow]),one_smul ]
   · intro b hb hi; rw [map_smul, Pi.smul_apply, Tone.oneRank ( he b ) l ( by have hm:= mem_Iic.mp hb; omega ),smul_zero]
   simp
 · intro b hb hi; obtain hm:=mem_antidiagonal.mp hb; have hh:b.2<n:= by contrapose! hi; exact Prod.ext (by dsimp only; omega) (by dsimp; omega)
   change Tone.run ( Program.train (Y p x) _ _) _=_; rw [ Lambda.Finite.funds ];
   rw [ show Tone.run _ l=0 from ?_, mul_zero ]; rw [ rules,map_sum, Finset.sum_apply ]; refine Finset.sum_eq_zero fun i hi=>?_ ; obtain he':= mem_Iic.mp hi; rw [map_smul,Pi.smul_apply, Tone.oneRank (he i) l (by omega),smul_zero]
 simp
local notation "Ω"=> V.toLitBook
lemma natal (h: l.length=j.grade+n): run ( Glyph.preambleF V p j x n ) l=run ( Glyph.lit Ω j ) l := by
    rw [Glyph.pre_listing_coeff,map_sum, Finset.sum_apply, Fintype.sum_sum_type,Fintype.sum_unique]; rw [ Finset.sum_eq_zero (s:=Finset.univ) (f:=fun k:Fin (j.size+1)×Fin j.grade=> _ ) ?_ ]; -- choose
    · rw [add_zero]; change run (wobble G p x (levels (j.grade:ℤ) ( j.lit Ω )) n) l= _; rw [alone (r:=j.grade) p h (fun i=>?_ ),levels,Tone.grade, enough l (by omega)]; exact Limit.up (Limit.mod _ ((_:ℕ)+(j.grade:ℤ))) (by omega)
    intro i _; obtain hz:= Glyph.offer_cost V p j x (.inr i) n; have ht: Glyph.tally j (Sum.inr i)< j.grade:= i.2.isLt; exact Tone.oneRank hz l (by omega)
variable (H:Houses A j true)
include H
lemma root_allow (P:ℝ) (i:ℕ): Limit (( A i ).proof.input P).val ((j.grade:ℤ)+(i:ℤ)-1):= by
    by_cases ht:i=0; · subst i; push_cast; exact ( H 0|>.leading rfl ).Low P
    exact Limit.up ( ( H i|>.strict rfl (Nat.pos_of_ne_zero ht)).moves P ) (by omega)
lemma liftL (n:ℕ)(x:ℝ) (p:Team): Limit (motto p A x n).val ((j.grade:ℤ)+(n:ℤ)-1):= by
    rw [sky,Submodule.coe_add,Cylinder.sum_stack]; refine Limit.add ( Limit.up (lapLimit ( root_allow H x n )) (by omega)) (Limit.sum _ (fun i hi=> Limit.up ( rootLimit ( style_limit p x G i.1 ) (root_allow H x i.2) ) ?_)); obtain hm:=mem_antidiagonal.mp hi; omega
lemma planet (h:l.length=j.grade+n): run (scoreF V p A x n) l=run (j.lit Ω) l:= by
    rw [scoreF,Pi.add_apply,map_add,Pi.add_apply,Tone.oneRank ( liftL H n x p ) l (by omega),add_zero,rentF,map_sum, Finset.sum_apply]; rw [ Finset.sum_eq_single j,_root_.map_sum, Finset.sum_apply, Finset.sum_eq_single (0,n),_root_.map_smul];
    · rw [ show oil A j 0 x=1 from (?_: _ ) ]; rw [one_smul,natal V h];
      unfold oil; rw [ ( H 0 |>.leading rfl ).Single j (le_refl _) ]; simp
    · intro i hi hi'; obtain he:= mem_antidiagonal.mp hi; rw [ map_smul, Pi.smul_apply,Tone.oneRank ( Glyph.pre_costF V p j x i.2 ) l (by have ht:i.2≠n:=fun v=> hi' (Prod.ext (by dsimp only; omega) v); omega), smul_zero ]
    · simp
    · intro c _ hc; rw [map_sum, Finset.sum_apply]; refine Finset.sum_eq_zero (fun i hi=>?_ ); obtain hl:= mem_antidiagonal.mp hi; by_cases ht: i.2+c.grade< l.length; · rw [map_smul, Pi.smul_apply, Tone.oneRank ( Glyph.pre_costF V p c x i.2 ) l (by omega), smul_zero ]
      suffices hz:oil A c i.1 x=0 by rw [hz,zero_smul,map_zero]; rfl
      unfold oil; by_cases h0:i.1=0; · rw [h0, ( H 0|>.leading rfl ).Single c (by omega),if_neg hc,Polynomial.eval_zero,Complex.ofReal_zero ]
      rw [ (( H i.1 ).strict rfl ( Nat.pos_of_ne_zero h0 )).holds c (by omega),Polynomial.eval_zero,Complex.ofReal_zero ]
    simp
lemma signature (h: l.length=j.grade+n) : torch k (run (scoreF V p A x n)) l= torch k (run ( j.lit Ω )) l:= congr_arg (reading k) (funext (fun i:ℝ=> planet (x:=x) V (n:=n) (p:=p) H (by simpa using h: (Wire.sail (Wire.ray l) i).length=j.grade+n ))) -- Wire.ray?
end YM.FVA2.TreeT.Wake
