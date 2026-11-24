import YM.GradedFar.Room
/-!
# Costs along any admissible moving forms of the combined shapes

Here operator costs on the r-all-fields experiment, and true formal powers on the *same*
layouts. include along all admissible segments.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Tariff
open Function Filter Set PowerSeries
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits
open FVA2 XSpace XSpace.Normalize FVA2.Scale FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Fleet Neighbor
open Fork (Sold Safe)
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)(J:ℝ→tower S)
   (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
   {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true)
local notation "X" => Scale.Measure.outlook (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
variable {n m h:ℕ}{U B:ℝ}
local notation "P∥" => moving G U B
variable {K:Set (Points n)} {N:Set (Points m)} (hK:IsCompact K)(hx:K ⊆ conf n)(hN:IsCompact N)(hz:N ⊆ Outside m)

def Fits (K:Set (Points n))(N:Set (Points m))(T:ℝ)(z:Points (n+m)):= ∃ x∈K,∃ y∈N, z=forest x (T•y)
variable {I : Type*}{W : Calendar→I→Prop}{z: Calendar→I→Points (n+m)}(hf:∀ p i, W p i → Fits K N p.2 (z p i))
namespace Road
lemma log_safety {f:Calendar→I→ℝ}(hv:∀ᶠ p in P∥,∀ i,W p i→0≤f p i): Safe P∥ W (fun i _=>Δlog i) f:=
    (moneySafe.and hv).mono fun _ h i hi=>⟨h.1,h.2 i hi⟩
include hG in
lemma phys_safety {f:Calendar→I→ℝ}(hv:∀ᶠ p in P∥,∀ i,W p i→0≤f p i): Safe P∥ W (fun i _=>wallet G i) f:=
    ((bring (hG:=hG)).and hv).mono fun _ h i hi=>⟨h.1,h.2 i hi⟩
lemma safety : Safe P∥ W (fun i _=>Δlog i) (fun _ _=>1):= log_safety (Eventually.of_forall fun _ _ _=> zero_le_one)
include hK hN hx hz hf
lemma funded_forms : ∀ᶠ p in P∥,∀ i,W p i → z p i ∈ conf _:=by
 filter_upwards [Dirty.upper hK hx hN hz] with p H i he; obtain ⟨x,h,y,h',A⟩:=hf p i he; rw [A]; exact H _ h _ h'
include H
lemma formal_bill (q:ℕ) (u:ListInput G (n+m) h): Sold P∥ W (fun i _=>Δlog i) (fun _ _=>1)
    (fun p i=> coeff q (sent X h (z p i) u)):=by
 -- any fixed frame-label tuple
 simp_rw [sent,coeff_mk,basis_sum (declared X h _ q) u]; refine Fork.Sold.sum (safety) (fun b _=>?_)
 let P:= indexScan b
 let σ:=fun i:Fin n=> P (Fin.castAdd m i); let ξ:=fun j:Fin m=>P (Fin.natAdd n j)
 have hw: P = Fin.append σ ξ:= (show P=_ from funext fun i=> Fin.addCases (fun j=>(Fin.append_left σ ξ j).symm)
    (fun j=> (Fin.append_right σ ξ j).symm) i)
 have HA:= (H.separatedOPE 0).wilson; have hd:= demand_full HA hK hx hN hz σ ξ q 0
 obtain ⟨C,hC,k,H'⟩:= ((hd _ (Nat.lt_succ_self q)).size (show (0:ℝ)≤(totalG ξ:ℝ) from Nat.cast_nonneg _))
 refine ⟨k,‖multipliers u b‖*C, by positivity,?_⟩; filter_upwards [funded_forms hK hx hN hz hf, horizonUp
    (Real.tendsto_log_atTop.eventually H'), ifWide] with p hp Hv hx i hi
 specialize hp i hi; obtain ⟨x,h,y,hY,hz⟩:=hf p i hi; specialize Hv (⟨⟨x,h⟩,⟨y,hY⟩⟩: ↥K × ↥N)
 have hv: squeeze (-Real.log p.2) y=p.2 • y:=by rw [squeeze,neg_neg,Real.exp_log (zero_lt_one.trans_le hx.1)]
 unfold party at Hv; simp only [hv, ← hw,post,neg_zero,zero_mul,Real.exp_zero,mul_one] at Hv
 rw [declared,dif_pos hp]; rw [← hz] at Hv
 rw [caring P (boundedByCaps b) HA.dimensions hp, test,Reg.Point.story,coeff_mk] at Hv
 rw [norm_smul,mul_one, mul_assoc]; exact mul_le_mul_of_nonneg_left Hv (norm_nonneg _)

lemma predicts (α:Future G h)(u:ListInput G (n+m) h)(k:ℕ)(v: Calendar→I→Points (n+m)): Sold P∥ W
    (fun i _=> Δlog i) (fun i j=> ‖v i j‖) (fun i j=> coeff k (SpecCost α X (v i j) (z i j) u)):=by
 have hh: Safe P∥ W (fun i _=>Δlog i) (fun i j=> ‖v i j‖):= log_safety (Eventually.of_forall fun _ _ _=>norm_nonneg _)
 simp_rw [SpecCost,map_sum,coeff_C_mul,map_sum,coeff_mul]; refine Fork.Sold.sum hh (fun a _=> ?_)
 have hm: Sold P∥ W (fun i _=>Δlog i) (fun i j=> ‖v i j‖) (fun i j=> parallel a (v i j)) := Fork.Sold.bounded (c:=1) zero_le_one
    (Eventually.of_forall fun i j _=>by rw [one_mul]; exact shift_cost ..)
 have ha: Sold P∥ W (fun i _=>Δlog i) (fun _ _=>1) (fun p i=> ∑ j: Toon G (h+1),∑ s ∈ Finset.HasAntidiagonal.antidiagonal k,
    coeff s.1 (α a.2 (u a.1) j)*coeff s.2 (sent X (h+1) (z p i) (update (climbing u) a.1 (theory j)))):=by
   refine Fork.Sold.sum safety (fun j _=> Fork.Sold.sum safety (fun m _=> ?_))
   have hv:= (formal_bill Z M H hK hx hN hz hf (G:=G) m.2 (update (climbing u) a.1 (theory j)) (U:=U) (B:=B))
   simpa only [mul_one] using Fork.Sold.mul safety hv (Fork.Sold.closed (coeff m.1 (α a.2 (u a.1) j)))
 simpa only [mul_one] using Fork.Sold.mul safety ha hm
end Road
end YM.Integration.GradedFar.Tariff
