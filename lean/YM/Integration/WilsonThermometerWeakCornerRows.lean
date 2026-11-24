import YM.GapsContact.Earn.Pieces
import YM.Integration.WilsonThermometerWeakPublishedWatch

/-! Mixed near derivatives on the original Wilson hierarchy with a stationary
physical exterior. Each derivative pays its physical radius at its own true
near field. The exterior keeps its own reflected size. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakCornerRows
open Function Filter Finset Set MeasureTheory Spec Table Extraction Trace Trace.Pilot
open GapsContact GapsContact.Ascent GapsContact.Seams EveryPhase OPE RG Lattice
open Frontier6 Frontier6.Tale Frontier6.Road PhysicalNext.Repeat.Legato
open scoped Topology Classical BigOperators
universe u
variable {G:Gauge} {R:Run G} {T:Campaign R} {W:Campaign.Pillars R T} {f:Extraction.Order}
    {S:Table R.family.book} (F:Final R.family f S) {I J:Type} [Fintype I] [DecidableEq I] [Fintype J]

theorem original (simple:G.Simple){e:ℝ}
    (funded:WilsonLimitConstruction.FundedOriginalProperties.{u} simple e W)(L:Almanac F)(X:Completed F L):
    Roll.{u} F simple L :=
  Roll.ofFlight F simple (Flight.join X (funded.2.1.trace f S))

def rows : List (I×Axis)→(I→S.Tag)→(I→S.Tag)
  | [],v=>v
  | p::l,v=>route F (rows l v) p 1

def grades : List (I×Axis)→(I→ℕ)→(I→ℕ)
  | [],d=>d
  | p::l,d=>update (grades l d) p.1 (grades l d p.1+1)

private lemma raised (d:I→ℕ)(a:List (I×Axis))(v:I→S.Tag)(degrees:∀i,(v i).1=d i):
    ∀i,(rows F a v i).1=grades a d i:=by
  induction a with
  | nil=>exact degrees
  | cons p a ih=>exact fun i=>route_degree F (rows F a v) (p:=p) (n:=1) (grades a d) ih i

private lemma priced {simple:G.Simple}{L:Almanac F}(H:Roll.{u} F simple L)(d:I→ℕ)(a:List (I×Axis)):
    ∃B:ℝ,1≤B ∧ ∀ρ∈Ioc (0:ℝ) 1,∀v:I→S.Tag,(∀i,(v i).1=d i)→
       ρ^a.length*billSlots F ρ (rows F a v)≤B*billSlots F ρ v:=by
  induction a with
  | nil=>refine ⟨1,le_rfl,?_⟩;intro r _ v _;simp [rows]
  | cons p a ih=>
    obtain ⟨B,Bp,base⟩:=ih
    obtain ⟨C,Cp,step⟩:=route_pay F H (grades a d) p 1
    refine ⟨C*B,one_le_mul_of_one_le_of_one_le Cp Bp,?_⟩
    intro r hr v degrees
    have endFee:=step r hr (rows F a v) (raised F d a v degrees)
    rw [pow_one] at endFee
    change r^(a.length+1)*_≤_
    rw [pow_succ,mul_assoc]
    change _*(r*billSlots F r (route F (rows F a v) p 1))≤_
    calc _≤r^a.length*(C*billSlots F r (rows F a v)):= mul_le_mul_of_nonneg_left endFee (pow_nonneg hr.1.le _)
         _=C*(r^a.length*billSlots F r (rows F a v)):=by ring
         _≤C*(B*billSlots F r v):=mul_le_mul_of_nonneg_left (base r hr v degrees) (zero_le_one.trans Cp)
         _=_:=by ring

/-- All original viewers and the entire measured exterior are present. The
price is uniform in the actual placements, including macroscopically distant
exterior positions, and in the two independently priced position radii. -/
theorem exterior {simple:G.Simple}{L:Almanac F}(H:Roll.{u} F simple L)
    (d:I→ℕ)(e:J→ℕ)(a:List (I×Axis)){s:ℝ}(sp:0<s):
    ∃(B:ℝ)(m:ℕ),1≤B ∧ ∀ρ∈Ioc (0:ℝ) 1,∀b∈Icc ρ 1,
      ∀(x:I→E4)(y:J→E4),
      Pairwise (fun i j=>s*(Sum.elim (fun _:I=>ρ) (fun _:J=>b) i)≤‖Sum.elim x y i-Sum.elim x y j‖)→
      ∀q:StateIndex F,∀(v:I→S.Tag)(w:J→S.Tag),(∀i,(v i).1=d i)→(∀j,(w j).1=e j)→
        ‖ρ^a.length • peal F q (assembly S x (rows F a v)*assembly S y w)‖≤
          B*dock ρ^m*billSlots F ρ v*billSlots F b w:=by
  obtain ⟨C,Cp,inner⟩:=priced F H d a
  obtain ⟨D,m,Dp,outer⟩:=acrossCorners F H (Sum.elim (grades a d) e) sp
  refine ⟨D*C,m,one_le_mul_of_one_le_of_one_le Dp Cp,?_⟩
  intro r hr b hb x y clear q v w vv ww
  let radius:=Sum.elim (fun _:I=>r) (fun _:J=>b)
  have fits(i:I⊕J):radius i∈Icc r 1:=by cases i with
                                         | inl i=>exact ⟨le_rfl,hr.2⟩
                                         | inr j=>exact hb
  have degrees(i:I⊕J):((Sum.elim (rows F a v) w) i).1=Sum.elim (grades a d) e i:=by
    cases i with
    | inl i=>exact raised F d a v vv i
    | inr j=>exact ww j
  have all:=outer r hr radius fits (Sum.elim x y) clear q (Sum.elim (rows F a v) w) degrees
  rw [concatenates] at all
  have split:crestSet F radius (Sum.elim (rows F a v) w)=billSlots F r (rows F a v)*billSlots F b w:=by
    simp only [crestSet,billSlots,Fintype.prod_sum_type,radius,Sum.elim_inl,Sum.elim_inr]
  rw [split] at all
  have nonneg:0≤D*dock r^m:=mul_nonneg (zero_le_one.trans Dp) (pow_nonneg (zero_le_one.trans (dock_valid r hr)) m)
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hr.1.le _)]
  calc _≤r^a.length*(D*dock r^m*(billSlots F r (rows F a v)*billSlots F b w)):=
           mul_le_mul_of_nonneg_left all (pow_nonneg hr.1.le _)
       _=(D*dock r^m)*((r^a.length*billSlots F r (rows F a v))*billSlots F b w):=by ring
       _≤(D*dock r^m)*((C*billSlots F r v)*billSlots F b w):=
           mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (inner r hr v vv) (billSlots_pos ..)) nonneg
       _=_:=by ring

end YM.Integration.WilsonThermometerWeakCornerRows
end
