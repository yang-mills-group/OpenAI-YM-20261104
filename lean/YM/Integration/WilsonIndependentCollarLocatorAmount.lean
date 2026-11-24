import YM.Integration.WilsonIndependentCollarLocatorRoster
import YM.Integration.WilsonIndependentCollarRoutedBinder

/-! Pay each specified physical binder at its actual length, using the
original once-counted occupied rows over all relative placements. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarLocatorAmount
open Function Finset Lattice Laurent RG Wilson Precision Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Affinity PhysicalNext.Repeat.Legato
open Push Push.AbsoluteSums Push.Local WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue
open WilsonCoeffUV.Embroider WilsonCoeffUV.Winding WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Wheel.Address
open FundedMarkedPathSelection OriginalIssuedMarkedRows WilsonOlderFreshConnectedRobe WilsonOlderFreshConnectedRoll
open WilsonOlderFreshConnectedAppointment WilsonOlderFreshConnectedBirth WilsonOlderFreshGraphSlate
open WilsonRegisteredPairUnaryWallet WilsonOlderFreshGraphArmada
open WilsonOlderFreshGraphPointWallet (point)
open scoped Classical BigOperators
variable {G:Gauge}{n e m N:ℕ}{D k:Fin n→ℕ}{S J:Finset (Fin n)}{A δ σ:ℝ}
  (R:Run G)(V:Realm G (e+1) Credit.leanC)(hm:V.anchor ≤ m)(app:Paid R V hm D k δ σ)
  (c:Fin n)(X:Input V hm S k D A)(included:J⊆S)(live:c∈J)(apos:0≤A)
  (cut:m<N)(deep:0 < mass k J)(hs:0≤σ)(o:Cover)(v:Case D)
local notation "T" u:max => issued R V hm app N c X included live apos cut deep hs o v u
local notation "M" => R.family.path.levels.clock.hatBeta m^δ*A^J.card


private theorem inject {a b:Type}{f:a→b}(h:Injective f)(r:b→Type):
    Injective (fun z:Σ l:a,r (f l)=>Sigma.mk (f z.1) z.2):=by
  rintro ⟨i,s⟩ ⟨j,t⟩ eq
  have same:i=j:=h (congrArg Sigma.fst eq)
  subst j
  have copy:s=t:=eq_of_heq (Sigma.mk.inj eq).2
  subst t
  rfl

theorem original {I:Type}[Fintype I]{n':Side}{P:Passport n' (Fin n)}
    (B:I→Binder P (Stock.census (Fin n)))(u:I→Frill J c)(distinct:Injective u)
    (site:Frill J c→Site n')(placed:∀l,(B l).center=site (u l))(reserve:ℕ)
    (fits:∀l,(B l).length ≤ reserve+32*feeH (toe J c o (u l)) c J):
    ∑l:I,Real.exp (σ*(B l).length)*WilsonIndependentCollarSlateIntensity.amount (T (u l)) (B l).center ≤
      Real.exp (σ*reserve)*∑j:Fin (e+1),cost J (mass k J) j v M:=by
  let Row (l:I):=(T (u l)).Roster
  let h (l:I)(r:Row l):=((T (u l)).rows (point (site (u l))) disk r).height σ
  have nonneg (l:I)(r:Row l):0≤h l r:=(WilsonIndependentCollarSlateIntensity.spent (T (u l)) (site (u l)) hs).1 r
  have all:=WilsonIndependentCollarLocatorRoster.original R V hm app c X included live apos cut deep hs o v site
  let map:(Σ l:I,Row l)→Σ z:Frill J c,(T z).Roster:=fun z=>⟨u z.1,z.2⟩
  have dry:=budget_pull map (inject distinct fun a=>(T a).Roster) all
  have gross:=budget_scale (Real.exp_pos (σ*reserve)).le dry
  have length (l:I):Real.exp (σ*(B l).length) ≤
      Real.exp (σ*reserve)*Real.exp ((32*σ)*feeH (toe J c o (u l)) c J):=by
    rw [←Real.exp_add,Real.exp_le_exp]
    have edge:((B l).length:ℝ)≤(reserve:ℝ)+32*(feeH (toe J c o (u l)) c J:ℝ):=by exact_mod_cast fits l
    calc
      _≤σ*((reserve:ℝ)+32*(feeH (toe J c o (u l)) c J:ℝ)):=mul_le_mul_of_nonneg_left edge hs
      _= _:=by ring
  have mounted:SumBudget (fun z:Σ l:I,Row l=>Real.exp (σ*(B z.1).length)*h z.1 z.2)
      (Real.exp (σ*reserve)*∑j:Fin (e+1),cost J (mass k J) j v M):=by
    refine sumBudget_mono gross (fun z=>mul_nonneg (Real.exp_pos _).le (nonneg z.1 z.2)) ?_ le_rfl
    intro z
    exact (mul_le_mul_of_nonneg_right (length z.1) (nonneg z.1 z.2)).trans_eq (mul_assoc ..)
  calc
    _=∑'z:Σ l:I,Row l,Real.exp (σ*(B z.1).length)*h z.1 z.2:=by
      rw [mounted.2.1.tsum_sigma,tsum_fintype]
      apply sum_congr rfl
      intro l _
      change _=∑'r:Row l,Real.exp (σ*(B l).length)*h l r
      rw [tsum_mul_left,placed l]
      rfl
    _≤_:=mounted.2.2

end YM.Integration.WilsonIndependentCollarLocatorAmount
end
