import YM.FVA2.PriceB
/-!
# Literal power series of all tests prior to reset

Also define using `Bill.sheet` notation at any lattice address (common center) No
wrap restrictions, beyond the test support. Those constraints enter limit functions.
Ensures fields refer to exact symbols before normalization.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option quotPrecheck false
namespace YM.FVA2.BoxOffice
open Function Filter Set MeasureTheory
open Pert Pert.Position Maxwell Maxwell.Free PositionX PositionX.Bare.Shop PositionX.Bare.Subcell
open Wilson Lattice Gauge Labels PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested
open PertExtension.LatticePT RG FormalOPE.RG10 FormalOPE.RG10.BlockGauge FormalOPE.RG10.MultiGauge FormalOPE.RG10.InversionTop
open MS MS.Koszul MS.Theater MS.Book MS.Book.Program MS.Book.Convolve
open Clock Score Based PairCoords Modes Paper Trans Attend
open PowerSeries
open scoped Topology Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} (V: Warehouse G) {U J : Type} {n m d:ℕ} {N:Side}
local notation "F"=>V.F
local notation "ψ"=> PairCoords.φ (U:=U) (J:=J)
local notation "Y"=> (V.scene d).basis

section grid
lemma univ_unique {A:Type*}{u v:Fintype A}: @Finset.univ A u=@Finset.univ A v:= congr_arg (@Finset.univ A) (Subsingleton.elim u v)
variable [Fintype U][Fintype J][DecidableEq J]
section generic
variable (he:Even N.val)(b:Module.Basis U ℝ (Wilson.Field G N))(g:Module.Basis J ℝ (Param G N))(e:ℝ) (v:Fin n→ Site N)
local notation "η"=> (Currency b he (J:=J))
local notation "ιψ"=> Boson.sharp (bell (J:=J) b) φ (bell_even b)
local notation "W"=> unmarked b g
local notation "Ξ"=> Attend.guide η W
variable (w:Fin n→ V.Atom d)
local notation "H"=>members V w
lemma point (j:ℕ): ((e^4:ℂ)^n)*coeff j (key V he b g e v d (Y ∘ w)) = ∑ t:Mixed.Task (members V w), ( Orb.diag (Orb.restrictedO (Mixed.product H Finset.univ t v e)) ( Mixed.number H t + j ):ℂ):= by
   change _*coeff j (Ξ (∏ i:Fin n,gate V b (v i) e d (Y (w i))))=_; simp_rw [gate_name]; unfold enter; rw [ Fintype.prod_sum,map_sum,map_sum,Finset.mul_sum ]; refine Finset.sum_congr rfl (fun t _=> ?_); rw [ ← deals V he e v w t j ]; push_cast; rw [ show Ξ (∏ i:Fin n, (↑(billV e ( raw V d (w i) ) (t i)):ℂ) • ιψ (cast (raw V d (w i)) (t i) (v i)))= _ from latticePrice V he b g e v w t, map_smul, into_coeff ]; rw [mul_assoc]; rfl
end generic
variable (v: Test n) -- avoid redundant
section spell
variable (q:ℕ+)(k:ℕ)(b:Module.Basis U ℝ (Wilson.Field G (LatticePT.side q k)))(g:Module.Basis J ℝ (Param G (LatticePT.side q k)))
local notation "N1"=> LatticePT.side q k
local notation "ϵ"=> LatticePT.epsilon q k
local notation "Z"=> LatticePT.Native q k
local notation "I"=> LatticePT.origins q k
-- use swept functions as MS target comparison test at finite lattice. outside support no claims.
def zoneμ (q:ℕ+)(k:ℕ) (x:Fin n→ LatticePT.Native q k) (v: Test n) : ℂ:=
   (Mixed.price q k (( sweep (Complex.re∘v) (LatticePT.epsilon q k) ) ∘ points) x:ℂ) + Complex.I*( Mixed.price q k ((sweep (Complex.im∘v) (LatticePT.epsilon q k) ) ∘ points) x:ℂ)
-- Subcell aliased path issue
def collected (x:Fin n→ Z)(o: Z) : MultilinearMap ℂ (fun _:Fin n=> Label G d) Cn:= key V (side_even q k) b g (epsilon q k) (fun i=> x i + o) d
def shown (d:ℕ) (v:Test n) : MultilinearMap ℂ (fun _:Fin n=> Label G d) Cn := ∑ x:Fin n→ Site N1,∑ o∈I,(zoneμ q k x v * (((ϵ:ℂ)^4)^n)) • collected V q k b g x o
lemma banked (P: Fin n→ Label G d) (j:ℕ): coeff j (shown V q k b g d v P)=(warehouse V).full q k d v j P:= by
   let A: (MultilinearMap ℂ (fun _:Fin n=>Label G d) ℂ):= (coeff j).compMultilinearMap (shown V q k b g d v); let R:= (warehouse V); suffices H:A=R.full q k d v j from (show A P=_ from H ▸ rfl); apply Module.Basis.ext_multilinear (fun _=> Y); intro w
   let f:= members V w; have he: R.full q k d v j (fun i=> Y (w i)) =series f q k v j:= PositionX.Bare.spread_eval ..; rw [he];
   change coeff j (shown V q k b g d v _) = _; -- expand sums
   let Rφ(x:Fin n→ Z)(o:Z):Fin n→ Site N1:= fun i=> x i + o;
   unfold shown series collected zoneμ; simp_rw [ _root_.sum_apply, _root_.smul_apply,map_sum, map_smul, smul_eq_mul, mul_assoc ];
   unfold Mixed.polynomialTop; simp only [ Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum ]; rw [ ← Finset.sum_add_distrib ]; refine Finset.sum_congr (@univ_unique (Fin n → Z) _ _) fun x _=>?_ ; rw [ ← Finset.sum_add_distrib ]; refine Finset.sum_congr rfl fun i _=>?_; rw [ show (↑ϵ ^ 4)^n * coeff j (key V (side_even q k) b g _ (Rφ x i) d fun i=> Y (w i))=_ from point V (side_even q k) b g ϵ (Rφ x i) w j, Finset.mul_sum, ← Finset.sum_add_distrib ]; refine Finset.sum_congr (@univ_unique _ _ _) fun t _=>?_ ; rw [add_mul,mul_assoc]; rfl
-- SEC helper with exact smeared counterpart.Semantic ℂ.PT sparse
open Mixed
def shelter (d:ℕ)(v: Test n): MultilinearMap ℂ (fun _ : Fin n=> E F d) Cn := (shown V q k b g d v).compLinearMap (fun _=> RawLabels.physicalLabel F d)
lemma sheltered (P: Fin n→ E V.F d)(j:ℕ) : (warehouse V).bank q k d j n v P= coeff j (shelter V q k b g d v P):= by apply Eq.symm; exact banked V v q k b g _ _
lemma tends (P: Fin n→ E V.F d): shelter V q k b g d v P= ∑ x:Fin n→Site N1,∑ o ∈ I, (zoneμ q k x v*(((ϵ:ℂ)^4)^n)) • view V ( side_even q k ) b g ϵ (fun i => x i + o) d P := by unfold shelter; rw [MultilinearMap.compLinearMap_apply, shown]; simp_rw [_root_.sum_apply,_root_.smul_apply]; rfl
end spell
end grid
end YM.FVA2.BoxOffice
