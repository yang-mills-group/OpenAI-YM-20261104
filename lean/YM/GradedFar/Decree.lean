import YM.GradedFar.Zoning
/-!
# Continuum estimate from grid value and the compact stage hypotheses

Exercise in original farm precisely (p, A, calendar ...); never charge different fields or a
Far layout with larger circumference. State even the geometry called at the C-grid (sufficient to
exercise at enlarged compacts as in the argument).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Tariff.Crosser
open Function Filter Set PowerSeries
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits
open FVA2 XSpace XSpace.Normalize FVA2.Scale FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Fleet Neighbor
open Fork (Sold Safe)
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)(J:ℝ→tower S)
   (R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
   (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (ν:ℝ)
variable {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true)

variable {n m h:ℕ} {U B:ℝ}
local notation "Pt" => Points (n+m)
local notation "P∥" => moving G U B
local notation "g" => strength G
abbrev Access (K:Set (Points n))(N:Set (Points m)) (p:Calendar):= Fits K N p.2
-- prior statement required on f-grid v=none. One k. can use w/e etc as v' t if more general heterogeneous.
-- This is NOT RoundPoint statement. hypotheses used to get here given separately below elsewhere.
def Coded (K:Set (Points n))(N:Set (Points m))(t:ℝ→ℝ)(U B:ℝ)(X:Arenas G)(h k:ℕ)
    (W:Calendar→ Set (Points (n+m))) : Prop := ∀ u:ListInput G (n+m) h, Sold (moving G U B)
      (fun p z=> z∈ W p ∧ Access K N p z) (fun p _=> Δlog p) (fun p _=> g p.1^(k+1))
      (fun p z=> frank F J none h p.1 z u-appointedH140Crop k (t p.1) (sent X h z u))
-- enough: on extended compacts only

def GridPower (K:Set (Points n))(N:Set (Points m))(t:ℝ→ℝ)(U B:ℝ)(X:Arenas G)(h k:ℕ) := ∀ K' N',
    IsCompact K'→K' ⊆ conf n→ IsCompact N'→N' ⊆ Outside m→ K ⊆ interior K'→N ⊆ interior N'→
    ∀ j:ℕ, 1≤j→ ∃ W,Coverage G U B K N W j ∧ Coded F J K' N' t U B X h k W

variable {K:Set (Points n)}{N:Set (Points m)}(hK:IsCompact K)(hx:K ⊆ conf n)(hN:IsCompact N)(hz:N ⊆ Outside m)
variable {t:ℝ→ℝ}{α:Future G h}(ht:Coupling G t)(hμ: Included F J h (h+1) (Nat.le_succ h))(hP:PaidFuture F J α t)
    (hX:ClassExpansion F J (Scale.Measure.outlook Z.scheme Z.criterion) t (n+m) h)
    (hY:ClassExpansion F J (Scale.Measure.outlook Z.scheme Z.criterion) t (n+m) (h+1))
-- Entrants. Acquire physical P/G... at the indicated compacts; comes from separate Fork estimates
-- (requiring Coat).
variable (hU:0<U)(hB:0<B)
abbrev HorizonPaid (n m h:ℕ)(U B:ℝ): Prop:= ∀ (K:Set (Points n))(N:Set (Points m)),
    IsCompact K → K ⊆ conf n → IsCompact N→N ⊆ Outside m → ∃ D:ℝ,G6 F R J (Ceiling n h) (Ceiling m h) h U B D K N

local notation "X" => Scale.Measure.outlook (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
include hU hB hK hx hN hz H ht hμ hP hX hY
lemma campus (u:ListInput G (n+m) h)(k:ℕ) (hp:G1Wide J Z M ν (h+1) t U B)(he:HorizonPaid F J R n m (h+1) U B)
    (hat:GridPower F J K N t U B X h k): Sold P∥ (Access K N) (fun p _=> Δlog p) (fun p _=> (g p.1)^(k+1))
      (fun p z=> frank F J none h p.1 z u-appointedH140Crop k (t p.1) (sent X h z u)):=by
 -- grade prices decisive, then choose the grid exponent
 obtain ⟨K',N',hK',hN',h₀,h₁,hx',hz'⟩:=larger hK hN hx hz
 obtain h₂:= he K' N' hK' hx' hN' hz'
 obtain hR:= refee (hG:=hG) hU hB (W:= fun p (q:Pt × Pt)=> ‖q.2-q.1‖) (Eventually.of_forall fun _ _ _=> norm_nonneg _)
     (calculated F J Z M H hK' hx' hN' hz' ht hμ hP hX hY u k (U:=U) (B:=B))
 obtain hL:= earned F J R Z M ν hK' hx' hN' hz' ht hμ hP u (fun _ _=>none) hp h₂ (hG:=hG)
 let hh:= Road.phys_safety (U:=U) (B:=B) (hG:=hG) (W:=Crosser.segment K' N') (f:=fun p q=>‖q.2-q.1‖) (Eventually.of_forall fun _ _ _=>norm_nonneg _)
 obtain ⟨i,a,ha,ihe⟩:=Fork.Sold.sub hh hL hR
 obtain ⟨W,hH,hq⟩:= hat K' N' hK' hx' hN' hz' h₀ h₁ (k+1+i) (by omega)
 obtain ⟨C,hC,H0⟩:= Coverage.data hK hN hH h₀ h₁ (by omega) (hG:=hG); obtain ⟨j,b,hb,coded⟩:=hq u
 refine ⟨j,b+a*C,by positivity,?_⟩; filter_upwards [strength_positive hG |> poses, H0,coded,ihe,moneySafe] with p hg H hc hv hb' z hz
 obtain ⟨w,hw,xw,yw,Aw⟩:= H z hz; specialize hc w ⟨hw,xw⟩; specialize hv (z,w) yw
 let y (v:Pt):= frank F J none h p.1 v u - appointedH140Crop k (t p.1) (sent X h v u)
 have hz'': ‖y z - y w‖ ≤ a*C*(g p.1)^(k+1):=by
   rw [norm_sub_rev]; dsimp only at hv; change ‖frank F J none h p.1 w u - _ - (frank F J none h p.1 z u -_)‖ ≤ _
   rw [sub_sub_sub_comm];
   refine hv.trans ((mul_le_mul_of_nonneg_left Aw (mul_nonneg ha (by unfold wallet; positivity))).trans_eq ?_)
   rw [wallet,inv_pow,pow_add (strength _ _) (k+1)]; field_simp
 have he : ‖y z‖ ≤ b*Δlog p^j*g p.1^(k+1)+a*C*g p.1^(k+1):= by
   rw [add_comm]; exact le_trans (show _ ≤ ‖y z-y w‖ + ‖y w‖ from by simpa only [sub_add_cancel] using norm_add_le (y z - y w) (y w)) (add_le_add hz'' hc)
 refine he.trans ?_; rw [add_mul,add_mul]; exact add_le_add_right
   (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (mul_nonneg ha hC.le) (one_le_pow₀ hb')) (by positivity : 0 ≤ g p.1^(k+1))) _
end YM.Integration.GradedFar.Tariff.Crosser
