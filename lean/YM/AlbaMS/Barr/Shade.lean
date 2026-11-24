import YM.AlbaMS.Barr.Notes
/-!
# Exact value of FP chart ghost action on tree slice. Use loom maps

On that slice the Faddeev-Popov calculation has no contribution in `stim`,
even before a determinant rule is needed. Loves all root gauges. This uses
actual vertex/array derivatives; not assuming formal gauge equivalence.
Requires simple wave parameters. Compare to general via `baseInd` later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Bric.Coil
open Set Function Filter IsNilpotent
open scoped BigOperators Classical Topology
variable {E B R S:Type*}[CommRing R][CommRing S]{ρ : E→ Bool} {k:E→E→R} {s: Finset E} (Z:E→R)
lemma Hvar (i:E): weft Z (varC R ρ i)= Z i • varC R ρ i:= by ext l; by_cases h:l=[i]<;>simp [wefts,var_read,h]
def SumB : Coil ρ R→ₐ[R] Coil ρ R where
 __:= weft Z
 map_mul' _ _:= weft_mul Z
 map_one':= YM.MSBar.Barr.one_on Z
 map_zero':= (weft Z).map_zero
 commutes' c:= by change weft Z (put ρ c)=put ρ c; ext l; cases l <;> simp [wefts]
lemma SumB_exp [Algebra ℚ R](F:Coil ρ R)(h:IsNilpotent F): weft Z (exp F)=exp (weft Z F):=map_exp h (SumB Z)
lemma dualWeft (U:E→R)(F:Coil ρ R): weft Z (weft U F)=weft U (weft Z F):= by ext l; simp_rw [wefts]; rw [mul_left_comm]
lemma heldrank (n:ℕ)(F:Coil ρ R): weft Z (rankn n F)=rankn n (weft Z F):= by ext l; simp_rw [rankn_read,wefts,rankn_read]; split <;> simp
lemma loomroom (n:ℕ)(z:R)(F:Coil ρ R): weft Z (loom z n F)= loom z n (weft Z F):=by ext l; simp_rw [looms,wefts,looms]; rw [mul_left_comm]
lemma turnroom (H:R→+*S)(F:Coil ρ R): Wind _ H (weft Z F)=weft (fun i=> H (Z i)) (Wind _ H F):=by ext l; rw [wefts]; change H (weft Z F l)=_* H _; rw [wefts, H.map_mul]; congr 1; induction l with|nil=>exact H.map_one|cons x l ih=> simp [ih]
end YM.MSBar.Bric.Coil
namespace YM.MSBar.Barr.Axial
open Set Function Filter IsNilpotent LinearMap
open scoped BigOperators Classical Topology ContDiff
open Bric Coil Inlay Inlay.Net Odom Lattice Nexus Loft Loft.Chart Chart.Grove Cutis Cutis.Winter
variable {E I R:Type*}[DecidableEq E][CommRing R]{G:Gauge}
-- Compressor with boolean `use ghost K c`. False=annul both. restrictions on A same.
def mantel (R:Type*)[CommRing R] (b: Bool)(v:Finset E) : Leaf G E I→ R:=Sum.elim (Sum.elim (fun i=> if i.1∈v then 0 else 1) (fun i=> if i.1∈v ∧ b=true then 1 else 0)) (Sum.elim (fun _=>if b then 1 else 0) (fun _=>0))
variable [Fintype E][Fintype I]
abbrev act (s : Finset E)(b:Bool) (U:Heave G E I R):= weft (mantel R b s) U
variable (s: Finset E) (b:Bool)
-- Merge Grove proofs on shifted direction of A
omit [DecidableEq E][Fintype I] in
private lemma outside (Ω : Net E I)(x:Flit G E)(j:Flit G I)(i:Flit G E)(hi:i.1≠x.1):DA i (Ω.chat j x)=0:= by
  change (pathof G E I).shine (dx (slabQ i) (Ω.spotG j x))=0; apply (pathof G E I).vanish; filter_upwards [Net.tide (G:=G) (V:=E)] with y h
  let X:=stip x; let f:= Ω.fly (slabQ j)
  change fderiv ℝ ((stip x).toContinuousLinearMap ∘ Ω.fly (slabQ j)) y (slabQ i)=0; rw [fderiv_comp _ (stip x).toContinuousLinearMap.differentiableAt ((Ω.wax_rate h _).differentiableAt (by simp)),(stip x).toContinuousLinearMap.fderiv]; change coefQ x.2 (fderiv ℝ (Ω.fly (slabQ j)) y (slabQ i) x.1)=0; rw [Ω.sees h,show slabQ i x.1=0 from (show _=_ from Inlay.slab i.1 i.2 x.1).trans (if_neg (Ne.symm hi)),map_zero,map_zero]
omit [Fintype I] in
lemma zeroc (Ω:Net E I)(x:Flit G E)(he:x.1∈s)(j:Flit G I): act s true (Ω.chat j x)=put ø (Ω.chat j x []):=by
  apply deep; exact weft_nil (F:= _) _; rintro ((i|i)|(i|i))
  · change D _ (weft (mantel _ _ _) _)=D _ _; rw [D_put,weftD]; by_cases hv:i.1=x.1; · rw [show mantel ℝ true s (.inl (.inl i): Leaf G E I)=0 by simp [mantel,hv,he],zero_smul]
    rw [show D (ρ:=ø) _ _=0 from outside Ω x j i hv, map_zero,smul_zero] -- specify binder
  all_goals unfold act; rw [D_put,weftD]; first| simp_rw [(bare_simple (Ω.spotG j x)).1.2, map_zero,smul_zero]| simp_rw [(bare_simple (Ω.spotG j x)).1.1,map_zero,smul_zero]| simp_rw [(bare_simple (Ω.spotG j x)).2,map_zero,smul_zero]
end YM.MSBar.Barr.Axial
