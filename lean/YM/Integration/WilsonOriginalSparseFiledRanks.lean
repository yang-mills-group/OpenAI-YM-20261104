import YM.Integration.WilsonOriginalSparseAngularFare

/-! The two native funded prints pay the angular tails on their own wallets. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalSparseFiledRanks
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise Stationary
open AllOrder AllOrder.Floe Comparison.RG02 Multi Exterior FVA1Physical FVA1Physical.TwoReset
open Further.PhysicalPeriodLimitF933 Macrame Push.AbsoluteSums Animals
open WilsonOriginalCenteredSeamSalary WilsonCapturedRootedAngularSlots WilsonCapturedClockRankProjection
open WilsonCapturedPrimaryWindingMaterialRead (nativeClock)
open WilsonNeutralTwoPrintPeg (phase allowed)
open WilsonOriginalSparseAngularFare (pegs)
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{V:Type}[DecidableEq V]{C:Census V}
local notation "Slot" => Site n × Loc G 1

def hull (G:Gauge){n:Side}(o:Site n)(m:ℕ):Finset (Site n×Loc G 1):=(neighbors m o) ×ˢ univ

theorem cardinal (o:Site n)(m:ℕ):(hull G o m).card≤ballCost m*Fintype.card (Loc G 1):=by
  simpa [hull] using Nat.mul_le_mul_right (Fintype.card (Loc G 1)) (neighbors_card m o)

theorem distance (o:Site n)(m r:ℕ)(z:Fin r→Slot)(away:z∉pegs (hull G o m) r):
    m≤radius o (sites z):=by
  by_contra! h
  apply away
  apply Fintype.mem_piFinset.mpr
  intro j
  apply mem_product.mpr
  refine ⟨(neighbors_mem ..).mpr ?_,mem_univ _⟩
  have mem:(z j).1∈sites z:=mem_image.mpr ⟨j,mem_univ _,rfl⟩
  have q:=Finset.le_sup (f:=separation o) mem
  change separation o (z j).1≤radius o (sites z) at q
  omega

variable {I X:Bool→Type}{P:Bool→Passport n V}
  (M:(a:Bool)→I a→Row (P a) C G (X a))(x:(a:Bool)→X a)(grades:Bool→V→ℕ)
  (s:Hot C)(v:s.val.val)(layout:Bool→Layout G)(tape:Bool→Finset Age)
  {w:Bool→V→ℝ}{σ cost:Bool→ℝ}{order seats shelf:Bool→ℕ}
  (stock:∀a,Scene.Armada (M a) (w a) (grades a) (σ a) (cost a) (order a) (seats a) (shelf a))
  (positive:∀a,0<σ a)(proper:∀a,Legal (tape a) (layout a))(wallet:∀a i,0<w a i)
local notation "bank" a:max p:max => WilsonNeutralTwoPrintFronts.table (M a) (x a) (grades a) (layout a) (tape a) s (phase p)
local notation "pole" a:max => (Launch.index C (grades a) s.val+1)

def bill (G:Gauge){V:Type}[DecidableEq V]{C:Census V}
    (w:V→ℝ)(s:Hot C)(σ cost:ℝ)(chargeIndex e r:ℕ):ℝ:=
  ((r.factorial:ℝ)⁻¹*charge nativeClock (-(chargeIndex:ℤ)) (chargeIndex+e) r
    (fun j=>WilsonCapturedCoveredSourceWage.fare G j r σ cost))/Poly.toll w s.val

def value (a:Bool)(e r:ℕ)(z:Fin r→Slot):ℂ:=
  (((bank a false) e r z:ℝ):ℂ)+(((bank a true) e r z:ℝ):ℂ)*Complex.I

local notation "tag" a:max => value M x grades s layout tape a
local notation "fee" a:max e:max r:max => bill G (w a) s (σ a) (cost a) (pole a) e r
local notation "entry" => WilsonNeutralTwoPrintAccount.entry M x grades s layout tape

theorem split (e r:ℕ)(z:Fin r→Slot):
    entry e r z=(tag false) e r z-(tag true) e r z:=by
  unfold WilsonNeutralTwoPrintAccount.entry value
  push_cast
  ring

include stock positive proper v wallet in
theorem accounts (a:Bool)(e r:ℕ)(pr:0<r):
    ∑z,Real.exp ((σ a/8)*(radius ((P a).origin v.val) (sites z):ℝ))*‖(tag a) e r z‖ ≤ 2*(fee a e r):=by
  have component (p:Bool):∑z,Real.exp ((σ a/8)*(radius ((P a).origin v.val) (sites z):ℝ))*|(bank a p) e r z|≤fee a e r:=by
    have paid:=(WilsonNeutralTwoPrintFronts.issued (M a) (x a) (grades a) (layout a) (tape a) s (phase p)
      (stock a) (positive a) (proper a) v (allowed p) e e r pr).2.2.1
    have pos:0<Poly.toll (w a) s.val:=Finset.prod_pos fun j _=>wallet a j
    apply (le_div_iff₀ pos).2
    simpa only [mul_comm] using paid
  calc
    _≤∑z,(Real.exp ((σ a/8)*(radius ((P a).origin v.val) (sites z):ℝ))*|(bank a false) e r z|+
          Real.exp ((σ a/8)*(radius ((P a).origin v.val) (sites z):ℝ))*|(bank a true) e r z|):=by
      apply sum_le_sum
      intro z _
      rw [←mul_add]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      exact (norm_add_le _ _).trans_eq (by simp)
    _≤_:=by rw [sum_add_distrib,two_mul];exact add_le_add (component false) (component true)

theorem zero (e:ℕ)(δ:ℝ)(scalar:‖(peek dvd_rfl (M false) (grades false) (layout false) (tape false) (x false) e 0).part s.val-
    (peek dvd_rfl (M true) (grades true) (layout true) (tape true) (x true) e 0).part s.val‖ ≤ δ):
    ∑z:Fin 0→Slot,‖entry e 0 z‖ ≤ δ:=by
  simp only [WilsonNeutralTwoPrintAccount.scalar,Finset.sum_const,Finset.card_univ,Fintype.card_fun,
    Fintype.card_fin,pow_zero,one_nsmul]
  exact scalar

include stock positive proper v wallet in
theorem original (o:Site n)(same:∀a,(P a).origin v.val=o)(m e r:ℕ)(pr:0<r)(δ:ℝ)(dp:0≤δ)
    (localRead:∀z,(∀j,z j∈hull G o m)→‖entry e r z‖≤δ):
    ∑z,‖entry e r z‖≤((ballCost m*Fintype.card (Loc G 1):ℕ):ℝ)^r*δ+
      Real.exp (-((σ false/8)*(m:ℝ)))*(2*(fee false e r))+
      Real.exp (-((σ true/8)*(m:ℝ)))*(2*(fee true e r)):=by
  have both (a:Bool):∑z,Real.exp ((σ a/8)*(radius o (sites z):ℝ))*‖(tag a) e r z‖≤2*(fee a e r):=by
    simpa only [same] using accounts M x grades s v layout tape stock positive proper wallet a e r pr
  simp_rw [split M x grades s layout tape] at localRead ⊢
  apply (WilsonOriginalSparseAngularFare.rank (hull G o m) r ((tag false) e r) ((tag true) e r)
    (fun z=>(radius o (sites z):ℝ)) (m:ℝ) (σ false/8) (σ true/8) δ (2*(fee false e r)) (2*(fee true e r))
    (by have:=positive false;positivity) (by have:=positive true;positivity) localRead
    (fun z hz=>Nat.cast_le.mpr (distance o m r z hz)) (both false) (both true)).trans
  gcongr
  exact_mod_cast cardinal (G:=G) o m

end YM.Integration.WilsonOriginalSparseFiledRanks
end
