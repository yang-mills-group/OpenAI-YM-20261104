import YM.Integration.WilsonMatrixOriginalGermForecast
import YM.Integration.WilsonInvariantActionCapturedProfile
import YM.Integration.WilsonForwardMeasurable

/-! The actual signed covariance of the two returned regular fields. Each located operand is
the full priced captured column sum minus exactly its own original forced contribution. -/

noncomputable section
namespace YM.Integration.WilsonMatrixOriginalGermGram
open Filter Function Finset MeasureTheory Lattice Wilson RG Source Labels RG12 RG17 MS.Local.Physical MS.Menus
open Trace.Physical.GermGraph FVA2 PhysicalNext.Repeat.Legato Next.Rank.Price
open WilsonMatrixTicketLanesNativePrices WilsonMatrixOriginalIndependentColumns WilsonMatrixOriginalGermMarket
open WilsonInheritedRegisteredField
open scoped Classical BigOperators

def moment {X:Type*} [MeasurableSpace X] (ν:Measure X) (f g:X→ℂ):ℂ:=
  (∫x,f x*g x ∂ν)-(∫x,f x ∂ν)*(∫x,g x ∂ν)

private theorem average {X I:Type*} [MeasurableSpace X] [Fintype I] (ν:Measure X) [IsFiniteMeasure ν]
    (a:I→ℂ) (f:I→X→ℂ) (hf:∀i,Envelope (f i)):
    (∫x,∑i,a i*f i x ∂ν)=∑i,a i*(∫x,f i x ∂ν):=by
  rw [integral_finsetSum]
  · simp only [integral_const_mul]
  · exact fun i _=>((Envelope.constC (a i)).mulC (hf i)).integrableC ν

private theorem left {X I:Type*} [MeasurableSpace X] [Fintype I] (ν:Measure X) [IsFiniteMeasure ν]
    (a:I→ℂ) (f:I→X→ℂ) (hf:∀i,Envelope (f i)) (g:X→ℂ) (hg:Envelope g):
    moment ν (fun x=>∑i,a i*f i x) g=∑i,a i*moment ν (f i) g:=by
  unfold moment
  have product (x:X):(∑i,a i*f i x)*g x=∑i,a i*(f i x*g x):=by rw [sum_mul];simp only [mul_assoc]
  simp only [product,average ν a f hf,average ν a (fun i x=>f i x*g x) (fun i=>(hf i).mulC hg),
    mul_sub,sum_sub_distrib,sum_mul,mul_assoc]

private theorem swap {X:Type*} [MeasurableSpace X] (ν:Measure X) (f g:X→ℂ):moment ν f g=moment ν g f:=by
  unfold moment;simp only [mul_comm]

theorem matrix {X I J:Type*} [MeasurableSpace X] [Fintype I] [Fintype J] (ν:Measure X) [IsFiniteMeasure ν]
    (a:I→ℂ) (b:J→ℂ) (f:I→X→ℂ) (g:J→X→ℂ) (hf:∀i,Envelope (f i)) (hg:∀j,Envelope (g j)):
    moment ν (fun x=>∑i,a i*f i x) (fun x=>∑j,b j*g j x)=∑i,∑j,a i*b j*moment ν (f i) (g j):=by
  rw [left ν a f hf _ (Envelope.sumC univ _ (fun j _=>(Envelope.constC (b j)).mulC (hg j)))]
  apply sum_congr rfl
  intro i _
  rw [swap,left ν b g hg _ (hf i),mul_sum]
  apply sum_congr rfl
  intro j _
  rw [swap ν (g j) (f i),mul_assoc]

variable {G:Gauge} (R:Run G) (B:Deck G) {m N p:ℕ}

private theorem carried {j:ℕ} (hj:j≤N) {o:Config G (R.family.side j p)→ℂ} (e:Envelope o)
    (live:m≤j):Envelope (actualTransport R.family (N:=N) o live):=by
  induction live using Nat.decreasingInduction with
  | self=>rw [actualTransport_base R.family R.makes hj];exact e
  | of_succ u hu ih=>
    rw [actualTransport_step R.family R.makes hj _ hu]
    exact WilsonForwardMeasurable.average R.makes (hu.trans_le hj) ih

private theorem full (age:R.family.ref 4 ≤ m) (live:m≤N) (w:R.family.label 4) (o:Site (R.family.side m p)):
    Envelope (field R.makes live w o):=by
  rw [←WilsonInheritedRegisteredField.original R.makes live age w o]
  apply carried R (le_refl N)
  apply Envelope.compactC
  exact (((R.family.localSection 4).continuous_places _ _).const_smul _)

private theorem marked (age:R.family.ref 4 ≤ m) (live:m≤N) (w:R.family.label 4) (o:Site (R.family.side m p)):
    Envelope (forced R.makes live w o):=by
  have h:(fun U=>field R.makes live w o U + -regular R.makes live w o U)=forced R.makes live w o:=by
    funext U
    rw [separated R.makes live w o U];ring
  rw [←h]
  exact (full R age live w o).addC (regular_envelope R.makes live age w o).negC

def quote (m N p:ℕ) (w:R.family.label 4):Option (Glyph B 4)→ℂ
  | none=>-1
  | some i=>spectrum R B m N p w i

def arm (opened:Opened R.family 4 m p) (live:m ≤ N) (w:R.family.label 4) (o:Site (R.family.side m p)):
    Option (Glyph B 4) → Config G (R.family.side m p)→ℂ
  | none=>forced R.makes live w o
  | some i=>let fit:=(fitting 4 N p m R.makes opened live).trans (WilsonMatrixOriginalGermAnchor.clocked R m
      (shrink R.family m N p) (shrink_pos R.family R.makes live p).ne')
    field R.makes live (WilsonMatrixOriginalGermAnchor.issued R B (N:=N) (p:=p) fit i) o

private theorem enrolled (simple:G.Simple) (opened:Opened R.family 4 m p) (live:m ≤ N)
    (w:R.family.label 4) (o:Site (R.family.side m p)):
    regular R.makes live w o=fun U=>∑i,quote R B m N p w i*arm R B opened live w o i U:=by
  funext U
  have program:field R.makes live w o U=∑i:Glyph B 4,spectrum R B m N p w i*
      arm R B opened live w o (some i) U:=
    WilsonMatrixOriginalGermMarket.read R B simple m N p opened live w o U
  rw [Fintype.sum_option]
  change _= -1*forced R.makes live w o U + ∑i:Glyph B 4,spectrum R B m N p w i*
    arm R B opened live w o (some i) U
  rw [←program,separated R.makes live w o U];ring

private theorem proper (opened:Opened R.family 4 m p) (live:m ≤ N) (w:R.family.label 4)
    (o:Site (R.family.side m p)) (i:Option (Glyph B 4)):Envelope (arm R B opened live w o i):=by
  cases i with
  | none=>exact marked R opened.post live w o
  | some k=>exact full R opened.post live _ o

/-- Includes the signed original marked cofactor against each full column and the
forced–forced cell, with the two actual subtracted means in every cell. -/
theorem invoiced (simple:G.Simple) (opened:Opened R.family 4 m p) (live:m ≤ N)
    (v:Fin 2→R.family.label 4) (o:Fin 2→Site (R.family.side m p))
    (ν:Measure (Config G (R.family.side m p))) [IsFiniteMeasure ν]:
    moment ν (regular R.makes live (v 0) (o 0)) (regular R.makes live (v 1) (o 1))=
      ∑i,∑j,quote R B m N p (v 0) i*quote R B m N p (v 1) j*
        moment ν (arm R B opened live (v 0) (o 0) i) (arm R B opened live (v 1) (o 1) j):=by
  rw [enrolled R B simple opened live (v 0) (o 0),enrolled R B simple opened live (v 1) (o 1)]
  exact matrix ν _ _ _ _ (proper R B opened live (v 0) (o 0)) (proper R B opened live (v 1) (o 1))

theorem tested (simple:G.Simple) (opened:Opened R.family 4 m p) (live:m ≤ N)
    (v:Fin 2→R.family.label 4) (φ:Test 2):WilsonInvariantActionCapturedProfile.earlier R (per:=p) live v φ=
    ∑x:Fin 2→Site (R.family.side N p),WilsonExternalMeshMass.charge R.family φ x*
      let o:=fun i=>(R.family.S.toDepth live p).parent (x i)
      ∑i,∑j,quote R B m N p (v 0) i*quote R B m N p (v 1) j*
        moment (OPE.Therm.scene R.family.path N p m)
          (arm R B opened live (v 0) (o 0) i) (arm R B opened live (v 1) (o 1) j):=by
  letI:IsProbabilityMeasure (OPE.Therm.scene R.family.path N p m):=OPE.Therm.probability R.makes.wilson live
  apply sum_congr rfl
  intro x _
  exact congrArg (fun a:ℂ=>WilsonExternalMeshMass.charge R.family φ x*a)
    (invoiced R B simple opened live v (fun i=>(R.family.S.toDepth live p).parent (x i)) _)

end YM.Integration.WilsonMatrixOriginalGermGram
