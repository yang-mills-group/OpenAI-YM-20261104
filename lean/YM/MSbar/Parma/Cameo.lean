import YM.MSbar.Tramp.Orion
import YM.Push.STATIONARY_UNIFORM.ScoreBounds
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Parma
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure
open Precision Gauge Midpoint Rolling Tramp Exterior Tree Wilson Laurent Bloch
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge} {c n:Side}{S:StepData c n}(F: Forest S.ratio)
local notation "X"=>Primary n G
local notation "Y"=>Primary c G
local notation "𝙆"=>Joint F G
local notation "Ʌ"=>Positions (Joint F G)
local notation "T"=> S.ratio
local notation "Ψ"=>address F G
local notation "O"=> Tramp.path S.ratio G
local notation "φ"=>Key F G
noncomputable def cup (F: Forest S.ratio) (G:Gauge): Positions (Joint F G)→L[ℝ]Positions (Joint F G) := (lowerCol (ι:=Primary c G)).comp (pushG F)
lemma silver (x:Positions (Joint F G)) : ‖cup F G x‖ ≤‖x‖:=by
   refine pi_norm_le_iff_of_nonneg (norm_nonneg _)|>.mpr fun i=>?_ ; cases i
   · change ‖(0:ℝ)‖ ≤ _; simp
   next i=> exact norm_le_pi_norm x (Sum.inr i)
noncomputable def mer (F:Forest S.ratio)(G:Gauge)(x:Positions (Joint F G)):= fine G F (cup F G x)
lemma dresses (x:Positions (Joint F G)) : represent (relayB F G x).2= mer F G x:=by
    change represent (tint G _ (stamp _ _ _))= _; rw [tango]; unfold mer fine; change _=lifting _ (represent 0) ((tint G _) _); rw [link_one]; unfold lifting; rw [replica_one]; congr 1; ext i; simp; rfl
lemma blazer (x:Ʌ): represent (relayB F G x).1= outer G F x:=rfl
variable (t:S.Choices)(i:Bond c)(x: Site c)(y:Positions (Joint F G))
noncomputable def arch (p:S.Choices)(i:Bond c)(x:Positions (Joint F G)) :ℝ := (S.kernel.penalty:ℝ) * G.price (outer G F x i*(S.prediction (mer F G x) p i)⁻¹)
lemma robe (x:Ʌ): pushChart F G t x = ∑ i:Bond c, arch F t i x:=by
    unfold pushChart Costree; change noiseTaylor S (outer _ _ _) (represent (relayB F G x).2) t=_; rw [dresses]; unfold arch; rw [← Finset.mul_sum]; rfl
noncomputable def routeN (g:Ratio c n)(i:Edge (Site c)):=g.embed i.1
variable (h:S.patch.Branches S.kernel G)
local notation "cτ"=> noiseCost S.patch
include h
lemma behove : arch F t i (haul _ (curbL Ψ (S.ratio.embed i.1) cτ) y)= arch F t i y:=by
   let V:= haul _ (curbL Ψ (S.ratio.embed i.1) cτ) y; let W : Site n:= S.ratio.embed i.1
   have ht:together Ψ W cτ V y:=by
       intro i hi; refine if_pos (Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩); rwa [separation_comm]
   have hh:together Ψ W cτ (cup F G V) (cup F G y):=by intro i he; cases i with | inl=>rfl|inr i=> exact ht _ he
   change arch _ _ _ V= _; unfold arch; rw [co_read F ht i (show separation _ _ ≤ _ from ?_),show S.prediction (mer F G V) t i=S.prediction (mer F G y) t i from noise_read F h t i hh]; unfold W; rw [separation_self]; omega
omit h
variable {m:ℕ}{x:Positions (Joint F G)}{C Z B D ρ:ℝ}
noncomputable def portio (G:Gauge)(n:ℕ)(Z:ℝ) := composeCost n (fineCost G n Z) 1
lemma vino (hp: PaintSupply G m Z) : Uniform.Inputs (mer F G) m (portio G m Z):=by
   obtain ⟨hx,h,hh⟩:=fine_supply F hp; let T':=cup F G; refine ⟨by change fine _ _ _=_; rw [map_zero,hx],by unfold portio composeCost; positivity,fun k y hy=>?_⟩
   exact (hh k (T' y) ((silver F y).trans hy)).comp (f:=T') (allows_linear (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x=> (silver F x).trans_eq (one_mul _).symm) ((silver F y).trans hy))
local notation "𝔏"=>S.patch
variable {W:ℝ}
local notation "J"=>S.kernel
noncomputable def priceArc (P:Patch)(G:Gauge)(U:KernelChoices)(m:ℕ)(Z K W:ℝ):= |U.penalty| * priceCost G (2^m * outerCost G (m+1) Z * composeCost m W (connectorCost P G m K (portio G (m+1) Z)))
variable {V J₀ r:ℝ}
lemma august (hn:2 ≤ m)(hp:PaintSupply G (m+1) Z)(hF:FocusReceipt G m W r)(hK:ExpReceipt G (m+1) B)(hL:LogReceipt G D ρ): Allows m (arch (G:=G) F t i) 0 (priceArc S.patch G S.kernel m Z B W):=by
    have he:= vino F hp; have hh:=outer_supply F hp; let z:= portio G (m+1) Z
    have h0:=prediction_radius_pos S he hn hK hL hF
    have hx':=prediction_pay S he hn hK hL hF 0 (Metric.mem_ball_self h0) t i
    refine Allows.smul ?_ _; refine Allows.price ?_; exact (((hh.2.2 i 0 (by simp)).order (Nat.le_succ m)).times (hx'.inverse (f:=fun z=>_))) -- inspect
end YM.MSbar.Parma
