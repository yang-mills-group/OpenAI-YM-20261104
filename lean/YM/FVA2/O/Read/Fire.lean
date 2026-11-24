import YM.FVA2.O.Read.Sheet
/-!
# Polynomial cost in log scale for `SheetCore` inversion

`budget_Gram`: for `Sheet` inversion itself, each output row of weight h also contributes
one power T^h. No order-dependent growth in the exponent of T.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Read
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick Metric Real TopologicalSpace
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder
open FVA2.Scale MS.Rake MS.Theater Level O.Score LogTime MS.Plane MS.Heat MS.Tone Momentum Rake.Geo
open Equator Facets Dframe O.Enh O.Bind O.Project
variable {G:Gauge}{ I J: Type }{n m k d:ℕ}{ t:ℝ }{ H:ℝ→Frames G }{r:ℝ→Cn}{V:Arenas G}
namespace Slate
variable [Fintype I] [DecidableEq I] { H: ℝ→ Matrix I I Cn }{ T: Matrix I I Cn }{M:Matrix I I ℂ}
abbrev slice (i:ℕ)(T:Matrix I I Cn): Matrix I I ℂ:= fun p q=> coeff i ( T p q )
lemma lead (h:IsUnit M)(he:slice 0 T=M): IsUnit T:= by
    rw [Matrix.isUnit_iff_isUnit_det, PowerSeries.isUnit_iff_constantCoeff,RingHom.map_det ]; rw [ show constantCoeff.mapMatrix T=M from ( by rw [← he]; ext1 i j; exact Eq.symm ( coeff_zero_eq_constantCoeff_apply _ ) ) ]; exact (Matrix.isUnit_iff_isUnit_det _).mp h
omit [DecidableEq I] in
lemma price_mul (H A:Matrix I I Cn): slice n ( H*A )=∑ i∈Finset.range (n+1),slice i H * slice (n-i) A:= by
    ext1 i j; unfold slice; rw [ Matrix.mul_apply,map_sum ]; simp_rw [coeffF, Matrix.sum_apply,Matrix.mul_apply ]; exact Finset.sum_comm
lemma inv_eq (ht:IsUnit M)(hp:slice 0 T=M): slice n ( T⁻¹ )=( slice n (1:Matrix I I Cn)-∑ i∈ Finset.range n,slice i ( T⁻¹ )*slice ( n-i ) T )*M⁻¹:= by
    obtain h:= Matrix.nonsing_inv_mul T (( Matrix.isUnit_iff_isUnit_det _ ).mp ( lead ht hp ) ); obtain H:= Matrix.mul_nonsing_inv M (( Matrix.isUnit_iff_isUnit_det _ ).mp ht ); rw [ ← h,price_mul,Finset.sum_range_succ,Nat.sub_self,hp,add_sub_cancel_left,mul_assoc,H,mul_one ]
lemma inverseCost (h:IsUnit M)(he:∀ t, slice 0 ( H t )= M)(ht:∀ i j:I, ChargeP d 0 ( fun (_:J) t=> H t i j )) (i j:I) : ChargeP d 0 ( fun (_: J) t=> ( H t )⁻¹ i j ):= by
    intro k hk; induction k using Nat.strong_induction_on generalizing i j with| h k ih=>
     have hp(t:ℝ): coeff k (( H t )⁻¹ i j)= ∑ v:I,(coeff k ((1:Matrix I I Cn) i v)-(∑ w∈ Finset.range k,∑ t':I, coeff w ((H t)⁻¹ i t') * coeff (k-w) ((H t) t' v)))*M⁻¹ v j:= by
        change slice k ( H t )⁻¹ i j=_; rw [ inv_eq h ( he t ), Matrix.mul_apply ]; refine Finset.sum_congr rfl fun v _=>?_ ; simp_rw [ Matrix.sub_apply, Matrix.sum_apply, Matrix.mul_apply ]
     simp_rw [ hp ]; refine Rain.sum _ ( fun v _=>?_ ); apply Rain.wig _ ( Rain.fixed _ ); refine Rain.minus ( Rain.fixed _ ) ( Rain.sum _ ( fun w hw=>?_ ) ); rw [Finset.mem_range] at hw; exact Rain.sum _ fun j _=> Rain.wig ( ih w hw _ _ (lt_trans hw hk) ) ( ht _ _ _ (by omega) )
end Slate
variable {P:Geology G d}
abbrev Detected (V:Arenas G) (P:Geology G d): Prop:= IsUnit ( Portfolio ( install V ) P )
local notation "V1"=>SheetCore H r V P
local notation "V0"=> Sheet H ( install V ) P
variable (h:Law V r H)( he:Observed ( install V ))(hp: Regular V)(ht:Detected V P)
include h ht
lemma sold_t (t:ℝ): IsUnit ( SheetCore H r V P t ):= Slate.lead ht ( funext₂ ( leadY h ) )
include he hp
lemma sealed_t : IsUnit ( V0 t ):= by
    rw [ sheet_b h he hp ]; apply IsUnit.mul (sold_t h ht t); exact isUnit_iff_exists_inv.mpr ⟨ Stone d G (-t), above d t ⟩ -- noncomm adjust
lemma back_t : (V0 t)⁻¹= Stone d G (-t) * ( V1 t )⁻¹:= by
    obtain hk:IsUnit ( V0 t ):= sealed_t h he hp ht; obtain hK:= Matrix.nonsing_inv_mul (V0 t) ((Matrix.isUnit_iff_isUnit_det _).mp hk); refine left_inv_eq_right_inv hK ?_; rw [ sheet_b h he hp,mul_assoc ( V1 t ), ← mul_assoc ( Stone d G t ),Read.above d t,one_mul ]; exact Matrix.mul_nonsing_inv _ ( ( Matrix.isUnit_iff_isUnit_det .. ).mp ( sold_t h ht t )) -- lemma
lemma budget_Gram (p q: Toon G d): ChargeP k (-( heft ( flash p ):ℝ) ) (fun (_:I)(t:ℝ)=> ( V0 t )⁻¹ p q ):= by
    simp_rw [ back_t h he hp ht, Stone, Matrix.diagonal_mul ]; exact ChargeP.grow ( ChargeP.joint ( a:=-( heft ( flash p ):ℝ) ) ( b:=0 ) reflectV ( Slate.inverseCost ( H:=V1 ) ht ( fun _=> funext₂ ( leadY h ) ) ( fun i j=> prepaid (I:=I) h he ( P:=P ) i j ) _ _ ) ) (by simp)
end YM.FVA2.O.Read
