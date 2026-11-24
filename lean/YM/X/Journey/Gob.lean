import YM.X.Wrap.Fowl
/-!
# Normalized stamp & periodic covariance interpretation at any center
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Crate.Fund
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics Reed Braid
open Clove Crystal Gravity Shelf Haze Ocean Interval Size Fielding Print PertExtension LatticePT Plate
open LiftMark Tensor Rays Hinge
open Stems hiding X
open scoped Topology ContDiff BigOperators Classical
variable {q:ℕ+}{n:Side}{k:ℕ}{R:ℝ} {I:Type*} {G:Gauge}
section peri
local notation "Q"=> flow G n
local notation "V"=>Curly G
local notation "J"=>poly (Jam n G)
-- Hair copy of Φ origin o. Sale periodic cost
lemma loc (p:Curly G)(o:Site n): shock Q p= shock sale (hairAt o p):= by
    unfold flow; rw [← sale_self o]; exact remaps ..
lemma tilt (z:Cover) : remap (pointB z) Q=Q:= by
    ext1; funext i j; rw [remap_cov,rτ,rτ]; simp [tau,pointB,Braid.cane]
lemma milked (p:Curly G)(z:Cover): milk Q (dress z p)= dress z (milk Q p):= by rw [dress,renative,tilt]
lemma color_fire (p:PlaqAxes): milk Q (vertex p)=vertex p:= freezes Q (fun i j he=>by rw [rτ]; simp [tau,he]) (vertex_triples p)
variable (S:Finset I)(M:I → Curly G) (A:I → Cover)(o:Site n) (x:I→Site n)
abbrev stock (A:I → Cover)(o:Site n)(i:I):= wrap n (A i)+o
def pack (S:Finset I)(w:I→Site n)(M:I → Curly G):= ∏ i∈S, hairAt (w i) (M i)
lemma tint (z:Cover)(u:Curly G): hairAt o (dress z u)=hairAt (wrap n z+o) u:= by unfold hairAt dress; rw [rename_rename,show place o ∘ pointB z= place (wrap n z+o) from ?_]; ext1 t; simp [place,Stems.west,pointB]; abel
lemma packed : pack S (stock A o) M= hairAt o (∏ i∈S,dress (A i) (M i)):= by rw [map_prod];simp only [tint,pack,stock]
def collector (S:Finset I)(x:I→Site n)(M:I → Curly G): J→ₗ[ℂ] ℂ:= shock sale ∘ₗ (LinearMap.mulRight ℂ (pack S x M))
lemma costP (p:poly (Jam n G)): collector S x M p=shock sale (p*pack S x M):=rfl -- .Flip orientation
lemma wrap_in (p:Curly G): collector S (stock A o) M (hairAt o p)= spine Q (fun i=> dress (A i) (milk Q (M i))) S (milk Q p):= by rw [costP,packed,←map_mul,←loc]; unfold Hinge.shock spine spiro; simp only [blend_components,←milked,minus]
lemma hemlock (p:Curly G): collector S (stock A o) M (hairAt o (milk (-Q) p))= spine Q (fun i=>dress (A i) (milk Q (M i))) S p := by rw [wrap_in,miles]
lemma shoots (p:Curly G)(z:Cover): collector S (stock A o) M (hairAt (wrap _ z +o) p)=spine Q (fun i=>dress (A i) (milk Q (M i))) S (dress z (milk Q p)):= by rw [←milked,← tint o,wrap_in]
lemma coin₁ (p:Curly G)(z:Site n)(a:ℝ): collector S (stock A o) M (hairAt (z+o) (a • p))= a • spine Q (fun i=>dress (A i) (milk Q (M i))) S (dress (lift z) (milk Q p)) := by
    simp_rw [RCLike.real_smul_eq_coe_smul (K:=ℂ), map_smul]; exact congr_arg _ (by nth_rw 1 [← wrap_lift z]; exact shoots S M A o p _)
lemma section_time (i:I) : stock (fun j=> A j-A i) (stock A o i)= stock A o:= by funext b; simp [stock,map_sub]; abel
lemma in_stock [DecidableEq I](i:I)(hi:i∈ S)(P:V):pack S x (Function.update M i P)= (hairAt (x i) P)*pack (S.erase i) x M:= by rw [pack,← Finset.mul_prod_erase _ (fun i=> hairAt (x i) _) hi, Function.update_self];congr 1;exact Finset.prod_congr rfl fun j hj=> congr_arg _ (Function.update_of_ne (Finset.ne_of_mem_erase hj) ..)
lemma shares [DecidableEq I](i:I)(hi:i∈ S) (z:J): collector S x M z=collector (S.erase i) x M (z*hairAt (x i) (M i)):= by rw [costP, costP];apply congr_arg (shock sale); rw [mul_assoc]; exact congr_arg _ (by nth_rw 1 [← Function.update_eq_self i M]; exact in_stock S M x i hi _)
end peri
-- spherules budgeting powers epsilon^(-d)
def mint (e:ℝ)(W:Word G)(k:ℕ): Curly G:= e^(-(W.d:ℤ)) • bookMark W k
lemma mint_heat (q:ℕ+)(s:ℕ)(W:Word G): milk (flow G (side q s)) (mint (epsilon q s) W 0)= epsilon q s ^(-(W.d:ℤ)) • load q W s:= map_smul ((milk _).restrictScalars ℝ) ..
lemma mint_urban(w:Fielding.Walk)(W:Word G){T:Type*}(u:T→ℕ)(t:T): urban q u W w t= dress (w (u t)) (milk (flow G (side q (u t))) (mint (epsilon q (u t)) W 0)):= by rw [mint_heat]; exact (map_smul ((dress _).toLinearMap.restrictScalars ℝ) ..).symm
end YM.PositionX.Crate.Fund
