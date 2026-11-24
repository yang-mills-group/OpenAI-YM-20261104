import YM.SchemeRG11.Plate.Seed
/-! Mark binding at degree zero and one. -/
set_option maxHeartbeats 320000
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Pile
open Lattice Function Filter Haze Pert Bare Labels Bark MvPolynomial Tree Catch Cellular Full Atoll
open MeasureTheory ProbabilityTheory
open scoped Classical ContDiff Topology
variable {G : Gauge} {N : Side}
abbrev vellum(G:Gauge):= Paper (Shaft G) ℝ
abbrev pLabel(G:Gauge):= Paper (Labels.Key G) ℝ
variable (h:ℝ)
def bud(i:Labels.Key G):vellum G:= h^(-(i.1+2:ℤ)) • omegaJ (0:Cover) i.1 ((axes G _).coord i.2)
-- constant and linear part
abbrev stemZero(h:ℝ) := vary (leafProbe (G:=G) h)
def film (i:Labels.Key G):PowerSeries (vellum G):= PowerSeries.C (leaf (leafProbe h i))+PowerSeries.C (bud h i)*PowerSeries.X
def lantern : pLabel G→+* PowerSeries (vellum G):= MvPolynomial.eval₂Hom (PowerSeries.C.comp MvPolynomial.C) (film h)
def expandW (p:pLabel G) := (PowerSeries.coeff 1) (lantern h p)
lemma petal (i: Labels.Key G):PowerSeries.constantCoeff (film h i)=leaf (leafProbe h i)∧PowerSeries.coeff 1 (film h i)=bud h i:=by simp [film,PowerSeries.coeff_C]
lemma lantern_z (p:pLabel G): PowerSeries.constantCoeff (lantern h p)=stemZero (G:=G) h p:=by
 induction p using MvPolynomial.induction_on with
 | C c=> rw [lantern, MvPolynomial.eval₂Hom_C, vary_C, RingHom.comp_apply, PowerSeries.constantCoeff_C]
 | add a b ha hb=> rw [_root_.map_add,map_add,map_add,ha,hb]
 | mul_X a i hq=> rw [_root_.map_mul (lantern h), _root_.map_mul (stemZero h),map_mul,hq,vary_X,lantern,MvPolynomial.eval₂Hom_X', (petal h i).1]
lemma expand_C (v:ℝ): expandW h (C v:pLabel G)=0:=by rw [expandW,lantern,MvPolynomial.eval₂Hom_C,RingHom.comp_apply,PowerSeries.coeff_C];rfl
lemma expand_add(p q:pLabel G):expandW h (p+q)=expandW h p+expandW h q:=by simp [expandW]
lemma expand_mul(p q:pLabel G):expandW h (p*q)=stemZero h p*expandW h q+expandW h p*stemZero h q:=by simp only [expandW,map_mul (lantern h),PowerSeries.coeff_one_mul, ← lantern_z]; ring
lemma expand_x(i: Key G):expandW h (X i)=bud h i:=by rw [expandW,lantern,MvPolynomial.eval₂Hom_X']; exact (petal h i).2

def castFirst(p:pLabel G):= expandW h ((Atoll.unmarked G h).neg.heat p)
def castZero(p:pLabel G):= stemZero h ((Atoll.unmarked G h).neg.heat p)
lemma castFree(p:pLabel G): castZero h p=(land G).neg.heat (stemZero h p):=by unfold castZero; exact Eq.symm (Dose.night ..)

variable (o:Site N)(w:Orb.Coords G N)
def plead(q:vellum G):= (MvPolynomial.aeval (cant (absorb o (Orb.expand G N w).val))) q
lemma canopy(k:Key G):
 PowerSeries.constantCoeff (seriesLex h o w k)=(plead o w (leaf (leafProbe h k)):ℝ)∧PowerSeries.coeff 1 (seriesLex h o w k)=(plead o w (bud h k):ℝ):=by
 let A: trunk G (Per N):= (Orb.expand G N w).val; let B := absorb o A; let S:ℝ:= h^(-(k.1+2:ℤ)); let L: Labels.Taylor G k.1→ₗ[ℝ] ℝ:=(axes G _).coord k.2
 have he (t:Bool): starJet t h o k.1 A A=S • starJet t 1 (0:Cover) k.1 B B:=by rw [coins, tensorAbs]; simp only [map_zero,zero_add,S]
 rw [(issuance ..).1, (issuance ..).2, plead, Haze.realTaste]
 rw [he true, he false]  -- maybe
 constructor
 · unfold leafProbe; rw [map_smul,map_smul, alpha_at]
 unfold plead bud; simp only [map_smul] -- wrong
 rw [omega_at]; simp only [smul_eq_mul]; unfold S; push_cast; ring
lemma rivers (p:pLabel G):
 PowerSeries.constantCoeff (Bare.field h o w (MvPolynomial.map Complex.ofRealHom p)) = Complex.ofReal (plead o w (stemZero h p)) ∧
 PowerSeries.coeff 1 (Bare.field h o w (MvPolynomial.map Complex.ofRealHom p)) = Complex.ofReal (plead o w (expandW h p)):=by
 induction p using MvPolynomial.induction_on with
 | C c=>rw [expand_C,map_C,Bare.field_C,vary_C]; simp [plead]
 | add p q Hp Hq=> rw [expand_add,map_add,map_add (stemZero h),Bare.field_add]; simp only [_root_.map_add, Hp.1,Hp.2,Hq.1,Hq.2,plead,Complex.ofReal_add, and_self]
 | mul_X p i Hp=>
   rw [_root_.map_mul (MvPolynomial.map _),Bare.field_mul,map_mul (stemZero h),vary_X,map_X,Bare.field_X, map_mul (PowerSeries.constantCoeff (R:=ℂ)),PowerSeries.coeff_one_mul]; simp only [Hp.1,Hp.2,(canopy ..).1,(canopy ..).2,expand_mul,expand_x]; unfold plead; simp only [map_mul,map_add,Complex.ofReal_add, Complex.ofReal_mul]; rw [vary_X,true_and];ring
lemma script (d:ℕ)(p:pLabel G)(he: Full.within (MvPolynomial.map Complex.ofRealHom p) d):
 let q:= (Full.column d h o (MvPolynomial.map Complex.ofRealHom p) w)
 PowerSeries.constantCoeff q=Complex.ofReal (plead o w (castZero h p)) ∧ PowerSeries.coeff 1 q=Complex.ofReal (plead o w (castFirst h p)):=by
 dsimp only; rw [inventory _ _ _ _ he w,dream,Dose.mapped_heat]; exact rivers ..
end YM.SchemeRG11.Pile
