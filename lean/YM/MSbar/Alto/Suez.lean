import YM.MSbar.Alto.Halo
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Alto
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure Matrix
open Precision Gauge Midpoint Rolling Tramp Exterior Tree Wilson Laurent Bloch Wave Parma Tin Bronze Asymptotics Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}
open Supply Input
variable {O:ChartRatio G}{K:MapPrices} {B: Sheet G}{D: Rolls B}{Θ:Protection D}{T0:Delays Θ}{W: Bar T0}{I:Wait W}{P:PostCost D}(A:Directed G I O K P)
local notation "λ'"=> A.kin
variable (p:ℕ)
set_option quotPrecheck false
variable (h:G.Simple)(hA : Reports K B O A.a) (hp:Merit A.a A.M)
variable (s:ℕ)(v:G.ColorIndex)(hs:6≤ s)
local notation "σ!" x=>candles A.a x
local notation "μ" x=> hat A.a x
local notation "S!"=> A.a.S
include h
lemma booth : ∀ᶠ N:ℕ in atTop,∀ g:Side, Wedge (opening G g) Dean (μ N) (σ! N) s p:=by
    let X:=range (p+1); choose C hC using fun i:ℕ=> paint_supply G (i+2)
    let D i:=Alto.duty G (C i) 1 s i; have hx' (i:ℕ) : ∀ᶠ x:ℝ in atTop,D i*x^(i+1+1) ≤ x^(Dean i):=by
        have hh:i+1+1<Dean i:=by have h:= Alto.climb i; omega
        filter_upwards [eventually_gt_atTop (0:ℝ), (Tuition.down (Tuition.scaled (D i) (Tuition.front (i+1+1))) hh).eventually (ge_mem_nhds zero_lt_one)] with x hx hp; exact (div_le_one (pow_pos hx _)).mp hp
    have ht:= hats A h; filter_upwards [ht.eventually_ge_atTop 1,ht.eventually (X.eventually_all.mpr (fun i _=>hx' i))] with t h₀ hh G'; constructor; intro i hi; have hw : 0 < hat A.a t:= lt_of_lt_of_le zero_lt_one h₀; let W₁ := μ t; have hp:1 ≤ purse Dean W₁ i:=one_le_pow₀ h₀
    by_cases hr:i=0
    · have hV:PowerSeries.coeff i (opening G G')=MvPolynomial.C 0:= by rw [hr,Rolling.opening,_root_.map_neg,splitK,neg_zero,_root_.map_zero]
      rw [hV]; exact Tin.constant hw 0 (zero_le_one.trans hp)
    have ht:=Alto.pursue (n:=G') i (hC i) zero_le_one (by omega) (hat A.a t) (Dean i) h₀ (hh i (mem_range.mpr (by omega)))
    exact sunrise _ (show (σ! t) ≤ 1 from div_le_one (pow_pos hw _)|>.mpr (one_le_pow₀ h₀)) _ ht
include hs hp hA
lemma skyline : ∀ᶠ m in atTop,∀ (N i:ℕ),∀ T:Scene A.a i p,Realized A.kin N i m p (sun G v) T→ (∀ j,m ≤ j → j ≤ N→ Wedge (T.Poly j) Dean (μ j) (σ! j) s p)∧∀ j:ℕ, m≤ j→j<N→∀ r≤p,|PowerSeries.coeff r (T.action j)| ≤ purse Dean (μ j) r:=by
    obtain ⟨k,hk⟩:= eventually_atTop.mp (booth A p h s); filter_upwards [eventually_ge_atTop k,A.a.fits.deep.eventually_ge_atTop (max p s)] with m hh ht N i T hF
    have hD (j) (he:m ≤ j)(hX:j ≤ N):Wedge (T.Poly j) Dean (μ j) (σ! j) s p:=by
        induction hX using Nat.decreasingInduction with
        | self=> rw [hF.opening]; exact hk _ (by omega) _
        | of_succ j hj ih=> exact (solitaire A p j h hA hp s i N v hs T hF hj he (ht.trans (A.a.fits.mono he)) (ih (by omega))).1
    exact ⟨hD,fun j he hj=> (solitaire A p j h hA hp s i N v hs T hF hj he (ht.trans (A.a.fits.mono he)) (hD _ (by omega) hj)).2⟩
-- rates unbounded beta, support.L.Callback.Q. Existence at all for universal path
lemma prize (N i:ℕ) :∃ T: Scene A.a i p,Realized A.kin N i 0 p (sun G v) T := chosen A h hA hp N v p i (Nat.zero_le N) -- args
end YM.MSbar.Alto
