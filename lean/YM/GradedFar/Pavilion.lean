import YM.GradedFar.Bundled
/-!
# Use Authentic cutoffs of `m_N`, including the Far-normalized estimator

This proves Room/Pose implications from the *paired tails* & `FullSales`. Any grid of
that distance in R units can be used. All masked arms, mixed horizons, profile powers.
Do not silently change any offsets of Far. (Not a histogram estimator implementation.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Auth
open Function Filter Set PowerSeries Metric
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits Lattice FullVolume
open XSpace XSpace.Normalize XSpace.Structure1 FVA2 FVA2.Scale FVA2.Scale.Facets FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Fleet Neighbor Tariff Tariff.Playbill Tariff.Crosser Tariff.Billboard Tariff.Sunshine Batch
open Fork (Sold Safe)
open scoped Topology BigOperators Classical ContDiff
local instance {n:ℕ} : ContinuousSMul ℝ (Points n):= IsBoundedSMul.continuousSMul
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
   (R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (J P:ℝ→tower S) (Z:WilsonPrescription G) (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
   {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true) (ν:ℝ)
    {t:ℝ→ℝ}(Ht:Pose F J Z t)(hF:Prepared F J P Z t)(Hq:LogTrace F R.port)
variable {n m k h :ℕ}{K:Set (Points n)}{N:Set (Points m)} {U B:ℝ}
local notation "g∴"=> strength G
local notation "X"=> Scale.Measure.outlook Z.scheme Z.criterion
local notation "S•"=> moving G U B
variable (hU:0<U)(hB:0<B)(hK:IsCompact K)(hx:K⊆conf n)(hN:IsCompact N)(hz:N ⊆ Outside m)
    (hQ:FullVolume.FixedBounds C)(hp:ClusterFrames C)(hC:C.Makes)

-- cost in BOTH products of basis fields, quantity in r' units never rescaled implicitly.
variable {d:Fin n→ℕ}{e:Fin m→ℕ}(hd:AppointedH140Through h d)(he:AppointedH140Through h e)
include H Ht hF hU hB ν
local notation "E*"=> FVA2.GradedFar.power e
lemma shift_cost : ∀ᶠ p in S•, ∀ (u:AppointedH140Inputs G d)(v:AppointedH140Inputs G e), Box u 1→ Box v 1 →
    (∏ i,width (shiftFar P p.1 (p.1*p.2) u v i)) ≤ 2^m * p.2^(FVA2.GradedFar.power e):= by
 let g(h:ℕ):= G1 F J P Z M H ν Ht hF (h:=h) hU hB; filter_upwards [poses (eventually_all.mpr
    (fun i:Fin m=> (g (e i)).1)),ifWide] with p hp ht u v hu hv
 let s:=p.1*p.2; let D(i):= Fin.append d e i; let T:= shiftFar P p.1 s u v; let f(i:Fin m):= 2*p.2^(e i); have he:0 ≤ p.2:= zero_le_one.trans ht.1
 let A(i:Sticker G)(s:ℝ):= width (relative P p.1 s i.1 i.snd); let w: ℝ→ℝ:= id -- discard
 refine le_trans (b:=∏ i : Fin (n+m), Fin.append (fun _:Fin n=> (1:ℝ)) f i) (Finset.prod_le_prod (fun _ _=> width_nn _) (fun i _=> ?_)) (le_of_eq ?_)
 · change A (stickers (tape u v) i) (Fin.append (fun _: Fin n=> p.1) (fun _: Fin m=>s) i) ≤ _; rw [tape_bill]; refine Fin.addCases (fun i=>?_) (fun i=>?_) i <;> simp only [Fin.append_left, Fin.append_right]
   · change width (relative P p.1 p.1 (d i) (u i))≤_; rw [(show relative P p.1 p.1 (d i) (u i)= u i from (assign P p.1 (d i)).symm_apply_apply (u i))]; exact (boxes zero_le_one).1 hu i
   change width (relative P p.1 _ (e i) (v i)) ≤ _; exact (op_use ((relative P p.1 s (e i)).toLinearMap) (v i)).trans ((mul_le_mul (hp i p.2 ht|>.1) ((boxes zero_le_one).1 hv i) (width_nn _) (by positivity)).trans_eq (mul_one _))
 rw [Fin.prod_univ_add]; simp only [Fin.append_left,Fin.append_right, Finset.prod_const_one,one_mul]; exact pow_all ..
include hK hx hN hz hQ hp hC Hq hd he
-- on theses exercises any desired g^q before T^E multiplying. estimator rounding uses one more power g (can take higher). simultaneous all offsets and test values.
theorem front_sales (q:ℕ)(S':ℝ)(hv:0≤S'): ∃ b:ℝ,0≤b ∧ ∀ᶠ p in S•, ∀ᶠ i : ℕ×ℕ in (again f).fuse,
    Awarded (C:=C) (Fin.append d e) i.1 i.2 ∧ ∀ s:Lattice.Site (C.side i.1 i.2),∀ o x y, x∈K → y∈N → ∀ z z', ‖rounded C p.1 i.1 (Fin.append z z')-forest x (p.2•y)‖≤ S'*g∴ p.1^(q+1)→
     ∀ (u:AppointedH140Inputs G d)(v:AppointedH140Inputs G e), Box u 1→ Box v 1→
        ‖recite F P p.1 p.1 z z' s u v - today F P none o p.1 (p.1*p.2) p.1 x y u v‖ ≤ b*g∴ p.1^q ∧
        ‖recite F P p.1 (p.1*p.2) z z' s u v - atLength F P none o p.1 p.2 x y u v‖ ≤ b*g∴ p.1^q*p.2^E* := by
 obtain ⟨b,hb,H'⟩:= within_sales F R J P Z M H ν Ht hF Hq (tape_horizon hd he) hU hB hK hx hN hz hQ hp hC q S' hv
 refine ⟨ b*2^m,by positivity,?_⟩
 filter_upwards [ H',Dirty.upper hK hx hN hz,poses (show ∀ᶠ r in trail,0<r from self_mem_nhdsWithin),
    poses (strength_positive hG), ifWide, (shift_cost F J P Z M H ν Ht hF hU hB (d:=d) (e:=e))] with
    p hp hD hr h hT hV
 filter_upwards [hp] with i hu
 refine ⟨hu.1, fun s o x y hx hy z z' hz u v he h'=>?_⟩; let t:= forest x (p.2 • y); let d':=Fin.append d e; let Z:=Fin.append z z'; let uL:=tape u v; let L:= fun _:Fin (n+m)=> p.1; let Y:=fun (v:AppointedH140Inputs G d')=> nl P d' L (p.1 • t) v
 let A:= assemble F P L d' i.1 i.2 s Z; have hQ (v:AppointedH140Inputs G d') (he:Box v 1): ‖A v - Y v‖≤ b*g∴ p.1^q:= hu.2 s t ⟨_,hx,_,hy,rfl⟩ _ hz v he
 have ha:= hD x hx y hy; constructor
 · let k:=Fin.append (fun _:Fin n=>p.1) (fun _:Fin m=>p.1); rw [← combo_today F P u v hr ha o]; change ‖assemble F P k d' i.1 i.2 s Z uL-nl P d' k (p.1•t) uL‖≤_
   rw [show k=L from funext fun i=> Fin.addCases (fun i=> Fin.append_left ..) (fun j=> Fin.append_right ..) i]; exact
    (hQ _ (tape_box zero_le_one u v he h')).trans (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hb (one_le_pow₀ one_le_two)) (by positivity))
 let w:=shiftFar P p.1 (p.1*p.2) u v; unfold recite atLength; rw [← combo_today F P u v hr ha o, ← assemble_shift, ← nl_shift]; change ‖A w-Y w‖ ≤ _
 exact (box_apply (G:=G) (d:=Fin.append d e) (A-nl P d' L (p.1•t)) (C:=b*g∴ p.1^q) (by positivity) hQ w).trans
    ((mul_le_mul_of_nonneg_left (hV u v he h') (by positivity)).trans_eq (by ring))
-- G.9 point with authentic Estimator, before any recrop in A. any horizon after.
theorem purchase_value (q:ℕ)(S':ℝ)(hv:0≤S'): ∃ b:ℝ,0≤b ∧ ∃ k:ℕ,∀ᶠ p in S•, ∀ᶠ i:ℕ×ℕ in (again f).fuse,
    Awarded (C:=C) (Fin.append d e) i.1 i.2 ∧ ∀ s:Lattice.Site (C.side i.1 i.2),∀ x y, x∈K → y∈N → ∀ z z', ‖rounded C p.1 i.1 (Fin.append z z')-forest x (p.2•y)‖≤ S'*g∴ p.1^(q+2)→
    ∀ (u:AppointedH140Inputs G d)(v:AppointedH140Inputs G e), Box u 1→ Box v 1→
        ‖recite F P p.1 p.1 z z' s u v - constantCrop X (-Real.log p.2) hd he x y q (t p.1) u v‖ ≤ b*g∴ p.1^(q+1)*(1+Real.log p.2)^k := by
 obtain ⟨b,hb,H'⟩:= front_sales F R J P Z M H ν Ht hF Hq hU hB hK hx hN hz hQ hp hC hd he (q+1) S' hv
 obtain ⟨c,hc,k,T,hT,Hᵣ⟩:= G9 F R J P Z M H ν Ht hF Hq hK hx hN hz hU hB (p:=q) hd he
 refine ⟨b+c,add_nonneg hb hc,k,?_⟩; filter_upwards [H',horizonUp (eventually_ge_atTop T),poses Hᵣ,ifWide, poses (strength_positive hG)] with i hi hv h he' hG
 filter_upwards [hi] with j hx
 refine ⟨ hx.1,fun s x y h₀ h₁ z z' h₂ u v h₃ h₄=>?_⟩
 have hP:= (hx.2 s 0 x y h₀ h₁ z z' h₂ u v h₃ h₄).1
 apply (opt _ _ (today F P none 0 i.1 (i.1*i.2) i.1 x y u v)).trans ((add_le_add hP (h i.2 hv he'.2 x h₀ y h₁ 0 none u v h₃ h₄)).trans ?_)
 have h:= Real.log_nonneg he'.1; exact (add_le_add_left (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (le_add_of_nonneg_right h))) _ |>.trans_eq (show b*g∴ i.1^(q+1)*(1+Real.log i.2)^k+c*_*_=_ from by ring))
end YM.Integration.GradedFar.Auth
