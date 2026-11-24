import YM.Integration.WilsonOlderFreshSoftCoveredRead

/-! At every actual date the arriving thermal scalar consists of the original
deposit and the nonconstant contributions already transferred by that date.
Each deposited contribution subsequently follows the original kinetic clock. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftRoseScalarLedger
open Function Finset Lattice Wilson RG Laurent Bloch Precision PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Mer WilsonCoeffUV.Blue
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Power WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Fountain WilsonCoeffUV.Soil
open WilsonOlderFreshSoftStops (scalarOnly)
open WilsonOlderFreshSoftCoverScalar (clock)
open scoped Classical BigOperators
variable {G:Gauge}

private theorem clock_add (L:Levels G)(O:ChartRatio G)(N c v:ℕ)(vc:v≤c)(X Y:Cost):
    clock L O N c v (X+Y)=clock L O N c v X+clock L O N c v Y:=by
  induction vc using Nat.decreasingInduction with
  | self=>
    have noMove (Z:Cost):clock L O N c c Z=Z:=by rw [clock,dif_neg (lt_irrefl c)]
    rw [noMove,noMove,noMove]
  | of_succ i hi ih=>
    have tick (Z:Cost):clock L O N c i Z=reel (ratioHigh L O N i) (clock L O N c (i+1) Z):=by rw [clock,dif_pos hi]
    rw [tick,tick,tick,ih]
    exact map_add (substAlgHom _) _ _

private theorem clock_append (L:Levels G)(O:ChartRatio G)(N c w v:ℕ)(vw:v≤w)(wc:w≤c)(X:Cost):
    clock L O N c v X=clock L O N w v (clock L O N c w X):=by
  induction vw using Nat.decreasingInduction with
  | self=>conv_rhs=>rw [clock,dif_neg (lt_irrefl w)]
  | of_succ i hi ih=>
    conv_lhs=>rw [clock,dif_pos (hi.trans_le wc),ih]
    conv_rhs=>rw [clock,dif_pos hi]

def front (L:Levels G)(O:ChartRatio G)(N k c i:ℕ)(P:Era G ℝ):Era G ℝ:=
  cruises L O N k c i P

def feed (L:Levels G)(O:ChartRatio G)(N k c i:ℕ)(P:Era G ℝ):Cost:=
  ScalarTrim (verseI L O i N k (axeR (front L O N k c (i+1) P))).2

theorem step (L:Levels G)(O:ChartRatio G)(simple:G.Simple)(localO:LocalRatio O)
    (N k c i:ℕ)(ic:i<c)(cn:c≤N)(P:Era G ℝ)(licensed:Auth k P):
    ScalarTrim (front L O N k c i P).2=
      clock L O N (i+1) i (ScalarTrim (front L O N k c (i+1) P).2)+feed L O N k c i P:=by
  let H:=front L O N k c (i+1) P
  have wh:Auth k H:=cruising L simple localO ic cn licensed
  have keep:Auth k (scalarOnly H):=wh.sub wh.axe
  have signed:H-scalarOnly H=axeR H:=by dsimp [scalarOnly];abel
  have move:=cruisePlus L (Nat.le_succ i) simple localO (ic.trans_le cn) wh keep
  rw [signed] at move
  have restored:=WilsonOlderFreshSoftCoverScalar.received L O simple localO N k (i+1) i
    (ic.trans_le cn) (by omega) H
  have single (Y:Era G ℝ):cruises L O N k (i+1) i Y=verseI L O i N k Y:=by
    rw [cruises_sub _ _ _ _ _ (Nat.lt_succ_self i),cruises_top]
  simp only [single] at move restored
  unfold front
  rw [cruises_sub _ _ _ _ _ ic]
  change ScalarTrim (verseI L O i N k H).2=_
  unfold feed
  change _=_+ScalarTrim (verseI L O i N k (axeR H)).2
  ext e
  have rank:=congrArg (fun X:Era G ℝ=>X.2 e 0 Fin.elim0) move
  change (verseI L O i N k (axeR H)).2 e 0 Fin.elim0=
    (verseI L O i N k H).2 e 0 Fin.elim0-(verseI L O i N k (scalarOnly H)).2 e 0 Fin.elim0 at rank
  rw [restored] at rank
  simp only [uband,shine_lit] at rank
  have zeroRank (Y:Era G ℝ):coeff e (ScalarTrim Y.2)=Y.2 e 0 Fin.elim0:=by
    simp only [ScalarTrim,PowerSeries.coeff_mk]
  rw [map_add,zeroRank,zeroRank]
  exact (sub_eq_iff_eq_add'.mp rank.symm)

private theorem deposits_sum (g:ℕ → Cost)(w c:ℕ)(wc:w≤c):
    g w=g c+∑i∈Ico w c,(g i-g (i+1)):=by
  induction c,wc using Nat.le_induction with
  | base=>simp
  | succ c wc ih=>rw [sum_Ico_succ_top wc,ih];abel

theorem original (L:Levels G)(O:ChartRatio G)(simple:G.Simple)(localO:LocalRatio O)
    (N k c w:ℕ)(wc:w≤c)(cn:c≤N)(P:Era G ℝ)(licensed:Auth k P):
    ScalarTrim (front L O N k c w P).2=clock L O N c w (ScalarTrim P.2)+
      ∑i∈Ico w c,clock L O N i w (feed L O N k c i P):=by
  let g (i:ℕ):Cost:=clock L O N i w (ScalarTrim (front L O N k c i P).2)
  have inward:=deposits_sum g w c wc
  have gain (i:ℕ)(hi:i∈Ico w c):g i-g (i+1)=clock L O N i w (feed L O N k c i P):=by
    obtain ⟨wi,ic⟩:=mem_Ico.mp hi
    dsimp only [g]
    rw [step L O simple localO N k c i ic cn P licensed,clock_add _ _ _ _ _ wi,
      ←clock_append _ _ _ _ _ _ wi (Nat.le_succ i)]
    abel
  rw [sum_congr rfl gain] at inward
  dsimp only [g,front] at inward
  rw [cruises_top] at inward
  nth_rw 1 [clock] at inward
  simpa only [dif_neg (lt_irrefl w),front] using inward
end YM.Integration.WilsonOlderFreshSoftRoseScalarLedger
end
