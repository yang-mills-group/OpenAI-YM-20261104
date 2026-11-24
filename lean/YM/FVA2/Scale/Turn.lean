import YM.FVA2.Scale.Blocks
/-!
# Equator & diagonal at constant scale and its conjugation on frame Guard.
We need a compatible group of **Near** frames on actual physical sectors only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Scale
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical
open Dframe
variable {G:Gauge}{d j i k n:ℕ}
local notation "L"=> FieldEnd G d
local notation "S"=> Sec G d
local notation "D"=> Level.E d
local notation "r"=> Guard G d
structure Base (F:Guard G d) : Prop where
    lead : PowerSeries.constantCoeff F=1
    high : ∀ i:ℕ,i≠0→ PowerSeries.coeff i F ∈ XSpace.Normalize.Change G d
abbrev Native (F:Guard G d):=∀ i, Level.Graded (PowerSeries.coeff i F)
abbrev diagonal (A:Guard G d): Guard G d:= PowerSeries.mk (fun i=> Level.diag (PowerSeries.coeff i A))
abbrev remainder (A:Guard G d): Prop:= diagonal A=1
-- `Base` here only formal invertible, not IsOpen at nonzero or analytic continuation.
namespace Base
open Level PowerSeries
variable {A B: Guard G d}
lemma equivalence (T:Guard G d): Base T ↔ Formal T ∧ PowerSeries.constantCoeff T=1:= by
    constructor
    · intro h; refine ⟨ ⟨ ?_,(PowerSeries.isUnit_iff_constantCoeff (φ:=T) ).mpr ( h.lead ▸ isUnit_one ) ⟩, h.lead ⟩
      let f: Normalize.Pick G d:= fun i=> if H:i=0 then 0 else ⟨ coeff i T,h.high i H ⟩
      refine ⟨ f, PowerSeries.ext (fun i=>?_ ) ⟩; by_cases hp:i=0
      · subst i; simp only [ coeff_zero_eq_constantCoeff_apply,h.lead,const_deck,show f 0=0 from dif_pos rfl,stand0 ]
      rw [pos_decked _ hp]; unfold f; rw [ dif_neg hp]
    rintro ⟨⟨⟨y,rfl⟩,_⟩,he⟩; exact ⟨he,fun i h'=> ( pos_decked y h' ).symm ▸ ( y i ).property⟩
lemma zero (h:Base A): coeff 0 A=1:= (coeff_zero_eq_constantCoeff_apply _).trans h.lead
lemma lies (h: Base A) : Formal A:=(equivalence A |>.mp h).1
lemma one : Base (1:Guard G d):=(equivalence _).mpr ⟨Formal.one ..,map_one _⟩
lemma mul (h:Base A)(he: Base B): Base (A*B):= (equivalence _).mpr ⟨ Formal.product h.lies he.lies, (by rw [map_mul,h.lead,he.lead,mul_one])⟩
lemma band (h:Base A) (i:ℕ): Band (coeff i A):= by
    by_cases he:i=0; · subst i; rw [h.zero]; exact one_band
    exact ( h.high _ he ).2.1
-- canonical inverse. preserve every cut.
end Base
def mirror (A:Guard G d):= PowerSeries.invOfUnit A 1
namespace Base
variable {A B: Guard G d}
lemma turn (h:Base A): mirror A*A=1:= invOfUnit_mul A 1 h.lead
lemma turn' (h:Base A): A*mirror A=1:= mul_invOfUnit A 1 h.lead
lemma rewind (h:Base A): Base ( mirror A ):= by
    obtain ⟨b,H,hb,hv⟩:= reversal_exists h.lies; obtain hp: mirror A=b:= ( by nth_rw 1 [← mul_one ( mirror A ),← hv, ← mul_assoc,h.turn,one_mul]); refine ( equivalence _ ).mpr ⟨ hp ▸ H,?_⟩; rw [← mul_one (constantCoeff (mirror A)), ← h.lead, ← map_mul,h.turn,map_one,h.lead]
lemma twice (h:Base A): mirror ( mirror A )=A:= by rw [← mul_one (mirror (mirror A)), ← h.turn, ← mul_assoc,h.rewind.turn, one_mul]
lemma alone (h:Base A)(v:A*B=1): mirror A=B:= by rw [ ← mul_one (mirror A), ← v, ← mul_assoc,h.turn,one_mul]
lemma payment (h:Base A): Base (diagonal A):= by
    have he(i:ℕ): coeff i (diagonal A)=Level.diag (coeff i A):=coeff_mk ..
    exact ⟨ (coeff_zero_eq_constantCoeff_apply _).symm.trans ( ( he 0 ).trans (by rw [h.zero,Level.diagonal_one]) ),fun i hv=> (he i).symm ▸ Level.diagonal_change _ ( h.high i hv ) ⟩
lemma guard (h:Base A)(he:Base B) : diagonal (A*B)=diagonal A*diagonal B:= by refine PowerSeries.ext fun i=>?_ ; rw [coeff_mul]; simp only [diagonal, coeff_mk, coeff_mul, map_sum,Level.diagonal_mul _ _ (h.band _) (he.band _)]
lemma native (A:Guard G d): Native (diagonal A):= by intro i; rw [diagonal,coeff_mk]; exact Level.diagonal_react _
lemma house : Native A ↔ diagonal A=A:= ⟨fun h=> PowerSeries.ext fun i=> ( coeff_mk .. ).trans (h i),fun h i=> ( coeff_mk .. ).symm.trans ( congr_arg ( coeff i ) h ) ⟩
lemma house₀ : diagonal (1:Guard G d)=1:= by apply house.mp; intro i; rw [coeff_one]; split_ifs; exact Level.diagonal_one; exact _root_.map_zero ( Level.diag (G:=G) (d:=d) )
lemma diagonal_rev (h: Base A): diagonal (mirror A)=mirror (diagonal A):= Eq.symm (h.payment.alone (by rw [ ← h.guard h.rewind,h.turn',house₀]))
lemma matter (h:Base A)(hu: Native A): Native (mirror A):= house.mpr (by rw [h.diagonal_rev,house.mp hu])
lemma befits (h: Base A)(hu: Native A)(k:Base B)(hv:Native B): Native (A*B):= house.mpr (by rw [h.guard k,house.mp hu,house.mp hv])
lemma switch {t: Cn}(h:Base A)(hp:Reg.Unique.CoreR t): Base (Reg.Point.stepV t A):= by
    obtain ⟨y,he⟩:= h.lies.actions; -- use h.lead
    have ht: constantCoeff (Reg.Point.stepV t A)=1:= by unfold Reg.Point.stepV; rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk,pay0,h.zero]
    refine ( equivalence _ ).mpr ⟨ ⟨ ⟨ Reg.Unique.shift y t,?_⟩, ( PowerSeries.isUnit_iff_constantCoeff (φ:= Reg.Point.stepV t A) ).mpr (ht ▸ isUnit_one)⟩,ht⟩
    rw [he, Reg.Unique.fees hp]
lemma paid_sub (t:Cn)(hu: Native A): Native (Reg.Point.stepV t A):= by intro i; unfold Reg.Point.stepV Level.Graded; rw [coeff_mk,rules]; simp_rw [map_sum, _root_.map_smul, hu ] -- hu abbrev
end Base
namespace Level
variable (p:Sec G d)(t v:ℝ)
def Dial (d:ℕ)(t:ℝ): FieldEnd G d:= ∑ i: E d, Extent.token t i • proj i
lemma taken (i:E d): Dial d t (proj i p)= Extent.token t i • proj i p := by
    unfold Dial; rw [LinearMap.sum_apply]; simp_rw [LinearMap.smul_apply]; rw [Finset.sum_eq_single i]; · rw [again];
    · intro j _ hj; rw [distinct p j i hj, smul_zero]
    simp
lemma exact₀ (a:Toon G d): Dial d t (theory a)=Extent.token t a.size • theory a:= by
    conv_lhs=>arg 2; rw [ ← top a ];
    rw [taken, top]
lemma flat : Dial d 0=(1:L):= by ext1 p; rw [ ← all p,map_sum,map_sum ]; apply Finset.sum_congr rfl; intro i _; rw [taken]; simp [Extent.token]
lemma rise (A:FieldEnd G d)(h:Graded A): Dial d t*A=A*Dial d t:= by
    ext1 p; rw [ ← all p,map_sum,map_sum ]; apply Finset.sum_congr rfl; intro i _; rw [Module.End.mul_apply,Module.End.mul_apply, taken, ← ( graded_test A ).mp h p i,taken,( graded_test A ).mp h p i,_root_.map_smul ]; -- check
lemma group : Dial d t*Dial d v= (Dial d (t+v): L):= by
    ext1 p; rw [ ← all p,map_sum,map_sum ]; apply Finset.sum_congr rfl; intro i _; rw [Module.End.mul_apply,taken,taken, _root_.map_smul,taken, smul_smul ]; unfold Extent.token; rw [neg_add, Real.exp_add, Complex.ofReal_mul,mul_pow,mul_comm ]
lemma spring : Dial d (-t)*Dial d t=(1:L):= by rw [group,neg_add_cancel,flat]
lemma autumn : Dial d t*Dial d (-t)=(1:L):= by rw [group,add_neg_cancel,flat]
-- conjugation later.Progress as planned
end Level
end YM.FVA2.Scale
