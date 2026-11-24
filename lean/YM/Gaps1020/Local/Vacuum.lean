import YM.Gaps1020.Local.Report
import YM.RG01.Kernel.Caliber
import YM.RG12.Joint.MeasureLimit
set_option autoImplicit false
noncomputable section
namespace YM.GapsLocal.Vacuum
open Function Filter Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Control Window Coat Footprint Raw Matter
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Stained Shield
open PhysicalNext PhysicalNext.Repeat Height Greenbelt
open Gas Ursell Trees RG.Supply Org Roost Opera
open Input Testing PriceCompiler
open AnalyticBridge VerifiedReset Collection Extra.Iteration Match Song Refrain Geo Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat.Daisy.Charity.RG12
open YM.RG01.Survive
open YM.ConnectedActivityE6.Blaze.Thermal1020
variable {G:Gauge} {X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Factor A}{L:Side}{m n N K k : ℕ}
variable {u: RG.Rep G (A.B.a.S.side (m+1) n)} (H : Guide A.B R.shape N m n u) (O:Return.Wood A.B m n)

local notation "s0" => A.B.a.clock.hatBeta m
local notation "j₀" => A.B.a.clock.J m
local notation "i₀" => A.B.a.clock.J (m+1)
local notation "σ" => X.p.profile j₀
local notation "Q0" => R.target i₀ j₀
local notation "o0" => R.shape.o i₀ j₀
local notation "Γ" => R.expense i₀ j₀
local notation "χ!" => Chi.canonical

lemma radiusBill (b:ℝ)(hp:0<b)(h:b≤2*A.B.a.clock.hatBeta (m+1))(k:ℕ):
    ((horizonRadius G (D.L (i₀)) s0)^(2*k))⁻¹ ≤ (Real.sqrt 2*nativeG b)^k := by
   let x := betaF G s0 (D.L (i₀))
   have hx: A.B.a.clock.hatBeta (m+1) = x := Push.PriceCompiler.beta_eq A.B.valid m
   have hL:1 < x:= hx ▸ A.B.a.fits.delayed _; have hd:0<x:=zero_lt_one.trans hL
   have hg:Real.sqrt x ≤ (x^Thermal1020.ray:ℝ)^2 := by rw [← Real.rpow_mul_natCast hd.le Thermal1020.ray 2,Real.sqrt_eq_rpow]; apply Real.rpow_le_rpow_of_exponent_le hL.le; norm_num [Thermal1020.ray]
   rw [pow_mul,← inv_pow]; unfold horizonRadius; apply pow_le_pow_left₀ (by change 0≤((x^Thermal1020.ray:ℝ)^2)⁻¹; positivity); apply le_trans (inv_anti₀ (Real.sqrt_pos.mpr hd) hg)
   unfold nativeG; rw [← div_eq_mul_inv,le_div_iff₀ (Real.sqrt_pos.mpr hp),inv_mul_le_iff₀ (Real.sqrt_pos.mpr hd),mul_comm _ (Real.sqrt 2),← Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
   exact Real.sqrt_le_sqrt (hx ▸ h)

include H
lemma promote {C A0:ℝ} (h : Report H O K C)(hb:C≤ (A0:ℝ)) : Report H O K A0:=
    {h with localErr:= liftLocal h.localErr hb le_rfl}

variable (h: Mallow.RG12.Earned (Thermal1020.vacuum G) R.shape A.delay)
variable (hG:G.Simple)
omit H
include R h hG

abbrev targetM (d:ℕ):=2*d+1 -- one full power after requested precision d
local notation "bill[" k "," m "]" => ((horizonRadius G (D.L (A.B.a.clock.J ((m:ℕ)+1))) (A.B.a.clock.hatBeta m))^((k:ℕ)+1))⁻¹
set_option quotPrecheck false
local notation "stage" k => X.p.profile (A.B.a.clock.J k)
-- Uniform in period, β in band and on all background links, actual input
-- Lives (which includes inherited interactions). Review comments in report.
theorem step (k d:ℕ) : ∃ C:ℝ, 0≤ C ∧ ∀ (N m n:ℕ), m<N → targetM d ≤ A.B.a.clock.J (m+1) →
    ∀ (u:RG.Rep G (A.B.a.S.side (m+1) n)) (H:Guide A.B R.shape N m n u), Opera.Price A.B R.shape N m n u H→ RG.Shoot.Lives A.B.bake N (m+1) n u → u.beta∈RG.Shoot.band A.B.a (m+1) →
      let g:= nativeG u.beta
      let t:= C*g^(d+1)
      let w:= A.B.a.clock.forcedAllowance m
      (∀ O:Return.Wood A.B m n, Report H O (targetM d) t) ∧
      0 < w ∧ A.B.a.clock.hatBeta (m+1)^k*(w/Real.sqrt w) ≤ t ∧
      ∃ (C d' v Y a b r B q:ℝ)(j:ℕ)(N':Captain H (stage m).order C d' v Y a b r B q j Chi.canonical), Receipt (R.expense (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (stage m) (targetM d) N':= by
  let M:=targetM d; let Q:ℝ:=Real.sqrt 2
  have hp:1≤ Q:= by unfold Q; exact Real.one_le_sqrt.mpr (by norm_num)
  obtain ⟨b,hb,hD⟩:= RG01.Vacuum.markCurrency R hG (M+1)
  obtain ⟨l,hl,hT⟩:= RG01.Vacuum.Flat.currency A.B.a hG (d+1) k
  let t:=(Q^(M+1)+b)*Q^(d+1)+Q^(d+1)+l
  refine ⟨t,by unfold t; positivity,?_⟩
  intro N m n hm hd u H hf hu hx g t' w
  have hw:0<w:=Real.exp_pos _
  have ha:1<A.B.a.clock.hatBeta (m+1):=A.B.a.fits.delayed _
  have hg:0 < u.beta :=by linarith only [ha,hx.1]
  have hv: 0 < g:= inv_pos.mpr (Real.sqrt_pos.mpr hg)
  have hp:g ≤ Q:=by
    change (Real.sqrt u.beta)⁻¹ ≤ _; rw [inv_le_comm₀ (Real.sqrt_pos.mpr hg) (by unfold Q; positivity)]
    unfold Q; rw [← Real.sqrt_inv]; apply Real.sqrt_le_sqrt; linarith only [hx.1,ha]
  obtain ⟨C',d',v,Y,a,b',r,B,q,k',N',H'⟩:= certified H hm h (targetM d) hd
  refine ⟨fun O=> promote H O (full H O hm H' hu hx hf (hD m N hm u.beta hx)) ?_,hw,?_,C',d',v,Y,a,b',r,B,q,k',N',H'⟩
  · have hS (m:ℕ) : targetM m+1=2*(m+1):= by unfold targetM; omega
    let x : ℝ:= Q^(M+1)+b
    have hL : 0≤ x:=by unfold x; positivity
    have hu: g^(M+1) ≤ Q^(d+1)*g^(d+1):= by nth_rw 1 [hS d,two_mul,pow_add]; gcongr
    have ha': bill[M,m] ≤ Q^(d+1)*g^(d+1):= by rw [hS]; rw [← mul_pow]; apply radiusBill; exact hg; exact hx.2
    change x*g^(M+1)+(bill[M,m]) ≤ _
    unfold t' t; nlinarith only [ha',hu,hL,mul_le_mul_of_nonneg_left hu hL,mul_nonneg hl (pow_nonneg hv.le (d+1))]
  rw [show w/Real.sqrt w=Real.sqrt w from (div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr hw))).mpr (Real.mul_self_sqrt hw.le).symm]
  have ht:l ≤ t:=le_add_of_nonneg_left (by positivity)
  exact (hT m u.beta hg (.inl hx.2)).trans (mul_le_mul_of_nonneg_right ht (pow_nonneg hv.le _))

open UVExtension Spire Orchard Mast Oasis Progress.DirectedRecipe Mallow RG12

variable {hG}(S:Spire.Uses R hG)
    {t : ℕ→ℕ}{a:Bid.Worth}{f:ℕ→ℝ}{Z:Legato.Bandage R f a} (T:Cellar S t Z)
local notation "X0" => Cellar.yard (roseA S) T
local notation "W[" N "," p "," m "]" => ((X0).path.rep N p m)
set_option quotPrecheck false
open RG01.Kernel
open OPE

-- Extends the denotational *actual normalized* local sector expansion:
-- the evaluated identity in the propagated cell catalogue, with denominator
-- kept by the same common level value. Does NOT take a global norm of the
-- numerical ratios. Normalization here is represented (split additive log in
-- the stated pre-reset norm before Exp and put the actual K in denominator).
structure Programme : Prop where
 follows : Mallow.RG12.Earned (Thermal1020.vacuum G) R.shape A.delay
 supplies (k d z:ℕ) : ∃ C:ℝ, 0≤ C ∧
   ∀ᶠ m:ℕ in atTop, z ≤ (A.B.a.budget m).order ∧ z ≤ (A.B.a.budget m).power ∧
   ∀ N n:ℕ, m<N→
     let g:= Pert.Asymptotics.regulatorRun (X0) N n (m+1)
     let e:= C*g^(d+1)
     let V:=W[N,n,m+1]
     let w:= A.B.a.clock.forcedAllowance m
     (Nonempty (Return.Wood A.B m n)∧∃ H:Guide A.B R.shape N m n V,Opera.Price A.B R.shape N m n V H) ∧
       0<w ∧ A.B.a.clock.hatBeta (m+1)^k*(w/Real.sqrt w) ≤ e ∧
       (∀ H:Guide A.B R.shape N m n V,Opera.Price A.B R.shape N m n V H→
         (∃ (C d' v Y a b r B q:ℝ)(l:ℕ)(N':Captain H (stage m).order C d' v Y a b r B q l Chi.canonical), Receipt (R.expense (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (stage m) (targetM d) N') ∧
         ∀ O:Return.Wood A.B m n, Report H O (targetM d) e ∧
           let W:=W[N,n,m]
           W.eval=RG01.Survive.coarse H O (keep H (targetM d))*RG01.Vacuum.exponentialShare (standard H) (A.B.a.budget m) (err H (targetM d)) ∧
           ∀ U:Config G (A.B.a.S.side m n), 0< W.eval U ∧
             (∀ X₁ : ℂ,X₁/(W.eval U:ℂ)= X₁/(RG01.Survive.coarse H O (keep H (targetM d)) U:ℂ)* (Real.exp (((standard H).read (err H (targetM d))).additive (A.B.a.budget m) U):ℂ)) ∧
           RG01.Kernel.Caliber (RG01.Kernel.expense (X0).path N m n U) (Wilson.prior G ((X0).side (m+1) n)))
-- Roof `Programme` forces the family to be a real one with all mask
-- conventions. Physical readout on all backgrounds, not just no-flag.
variable (ht : (Cellar.yard (roseA S) T).Makes)
include h ht
lemma provides : Programme (R:=R) S T := by
  refine ⟨h,?_⟩; intro k d z
  obtain ⟨C,hC,h⟩:= step (R:=R) h (hG) k d
  refine ⟨C,hC,?_⟩
  filter_upwards [A.B.a.fits.deep.eventually_ge_atTop (targetM d), eventually_ge_atTop ((X0).ref z)] with m hx hp
  obtain ⟨ha,hb⟩:= (ht.stages z).2 m hp
  refine ⟨le_trans (Nat.le_succ _) ha,hb,?_⟩
  intro N n hm g e V w
  have hv: RG.Shoot.Lives A.B.bake N (m+1) n V∧ V.beta ∈ RG.Shoot.band A.B.a (m+1) := (S.ticking N n (Uses.centerP _)).prices (m+1) (Nat.zero_le _) hm
  have hk H (he:Opera.Price A.B R.shape N m n V H):= h N m n hm (hx.trans (step_paid A.B.a m).1) V H he hv.1 hv.2
  obtain ⟨H,hH⟩:= RG01.Vacuum.hasGuide S (n:=n) hm
  have he':= hk H hH
  refine ⟨⟨Tree.select (A.B.a.clock.op m n).ratio (A.B.a.clock.op m n).patch.odd_side,⟨H,hH⟩⟩, he'.2.1,he'.2.2.1,?_⟩
  intro H hH; obtain ⟨hl,-,-,hY⟩:= hk H hH
  refine ⟨hY,fun O=>⟨hl O,?_⟩⟩
  intro W
  have hK: W.eval= _:= (ht.wilson.steps N n m hm).1.trans (hl O).evaluated
  refine ⟨hK,?_⟩; intro U
  have hv : 0 < W.eval U := Extra.Histories.Tour.bright (X0).path ht.wilson N n m hm.le U
  refine ⟨hv,fun x=>?_, RG01.Kernel.actual N (X0).path ht.wilson U hm⟩
  rw [hK, Pi.mul_apply,RG01.Vacuum.exponentialShare,Real.exp_neg,Complex.ofReal_mul,Complex.ofReal_inv,div_mul_eq_div_div, div_inv_eq_mul]
end YM.GapsLocal.Vacuum
