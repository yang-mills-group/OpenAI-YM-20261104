import YM.GradedFar.Earth
/-!
# Pay also the estimate for derivatives in (M.4): coordinate presentation

compare to crop of true booked c. Also present as derivative of comparison-Ms predicted position
kernel. All x in Near compact around chosen o, even o uniform.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Batch
open Function Filter Set MeasureTheory Metric PowerSeries
open Extraction Table Spec OPE OPE.Orbits PhysMS Trace.Pilot
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 FVA2.Scale FVA2.Scale.Facets FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh MS MS.Native MS.Land MS.Fleet
open Tariff Tariff.Sunshine FVA2.GradedFar.Cart
open Window
open scoped Topology BigOperators ContDiff Classical
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book} (F : Final C f S) (J P: ℝ→tower S) (R: Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
variable (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true)(ν:ℝ)
local notation "V"=> Scale.Measure.outlook (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
variable {t:ℝ→ℝ} (Ht:Pose F J Z t)(Hp:Prepared F J P Z t)(HL:LogTrace F R.port)
variable {n h d:ℕ} (l:Toon G d)
local notation "X" => Points n
variable {e:Fin n→ℕ}(he:AppointedH140Through h e)
include H ν Ht Hp HL he
omit ν HL he in
private lemma avenir : ∃ α:∀ h, Future G h,∀ h,PaidFuture F P (α h) t := by
 choose α hα using (fun h=> futureWins F P Z M H Ht.running (Hp.connects (h+1) h (Nat.le_succ _)) (YPose F J P Z M H Ht Hp)); exact ⟨α,hα⟩
lemma lit (u:AppointedH140Inputs G e)(k:ℕ): ContDiffOn ℝ ∞ (fun x=> coeff k (Cargo V x u l)) (conf n):=by
 obtain ⟨α,hα⟩:=avenir F J P Z M H Ht Hp; exact mixedS F P R Z M H l Ht.running (fun _=>regain F J P R Z M H ν Ht Hp HL) Hp.connects α hα he u k
lemma creed (u:AppointedH140Inputs G e)(L:TraceOrder n)(p:ℕ)(z:ℝ){x:X}(hx:x∈ conf n):
    δ L (fun x=> coord l (msVector Z M ν u x p d z)) x= appointedH140Crop p z (liability Z l u x L):=by
 simp_rw [bookVector Z M H ν,cargo_crop,crop_eq, liability, coeff_mk]
 rw [δ_sum (conf_open _) _ _ (fun i _=>contDiffOn_const.mul (lit F J P R Z M H ν Ht Hp HL l he u i)) L hx]; exact Finset.sum_congr rfl fun j _=> δ_const_mul (conf_open _) (lit F J P R Z M H ν Ht Hp HL l he u j) _ L hx
variable {K:Set (Points n)}(hK:IsCompact K)(hx:K⊆conf n) (L:TraceOrder n)
lemma levy (u:AppointedH140Inputs G e) {x:X}(hx:x∈conf n): liability Z l u x L=∑ a:Picks G e, PowerSeries.C (multipliers u a) * liability Z l (basisWord a) x L := by
 ext1 k; simp_rw [map_sum (coeff k),coeff_C_mul,liability,coeff_mk]; simp_rw [cargo_basis (A:=V) l _ u,map_sum (coeff k), coeff_C_mul]; rw [δ_sum (conf_open _) _ _
   (fun i _=> contDiffOn_const.mul (lit F J P R Z M H ν Ht Hp HL l he _ k)) L hx]; exact Finset.sum_congr rfl fun _ _=> δ_const_mul (conf_open _) (lit F J P R Z M H ν Ht Hp HL l he _ _) _ L hx
omit H ν Ht Hp HL he in
lemma messenger_levy (u:AppointedH140Inputs G e){x:X}(o:E4)(r:ℝ)(H:arena F R d o r x):
    δ L (fun x=> messenger F P R o r l x u) x=∑ a:Picks G e, multipliers u a * δ L (fun x=> messenger F P R o r l x (basisWord a)) x:=by
 have hi (a:Picks G e): ContDiffOn ℝ ∞ (fun x=> messenger F P R o r l x (basisWord a)) {x:X|arena F R d o r x}:= fun x hx=> (breeze F P R o r l x hx _).contDiffWithinAt
 simp_rw [basis_sum (messenger F P R o r l _) u,smul_eq_mul]; rw [δ_sum (season_open F R d o r n) _ _ (fun a _=> contDiffOn_const.mul (hi a)) L H]; exact Finset.sum_congr rfl fun i _=> δ_const_mul (season_open F R d o r n) (hi i) _ L H
local notation "Q∴" => {u:AppointedH140Inputs G e//Box u 1}
include hK hx
theorem tributeOPE : Receives t trail (fun r (i: Q∴ × E4 × ↥K)=> δ L (fun x=> messenger F P R i.2.1 r l x i.1.val) i.2.2.val) (fun i=>liability Z l i.1.val i.2.2.val L) := by
 obtain ⟨α,hα⟩:=avenir F J P Z M H Ht Hp
 let f(i:Picks G e)(r:ℝ)(j: Q∴ × E4 × ↥K):= multipliers j.1.val i * δ L (fun x=> messenger F P R j.2.1 r l x (basisWord i)) j.2.2.val; let Q(i:Picks G e)(j:Q∴ × E4 × ↥K):=PowerSeries.C (multipliers j.1.val i) * liability Z l (basisWord i) j.2.2.val L
 have he (i): Receives t trail (f i) (Q i):= Receives.mul (Receives.const (Charge.cap ⟨1^n, fun j=> multipliers_le zero_le_one _ i j.1.property⟩))
    (Receives.along (mixedCosts F P R Z M H l Ht.running (fun _=>regain F J P R Z M H ν Ht Hp HL) Hp.connects α hα hK hx he _ L) Prod.snd) (Coupling.conforms hG Ht.running)
 exact Receives.congr (Receives.sum Finset.univ fun i _=>he i) ((near_collar F R n d hK hx).mono fun r hr=> funext fun j=> (messenger_levy F P R l L _ _ _ (hr _ j.2.2.property _)).symm)
    (fun i=>(levy F J P R Z M H ν Ht Hp HL l ‹AppointedH140Through h e› L _ (hx i.2.2.property)).symm)
theorem derivativesOPE_coord (p:ℕ) : ∃ D:ℝ,0≤ D ∧ ∀ᶠ r in trail, ∀ o x,x∈ K → ∀ u:AppointedH140Inputs G e, Box u 1→ ‖δ L (fun x=> coord l (packet F P R d o r x u)) x- δ L (fun x=> coord l (msVector Z M ν u x p d (t r))) x‖ ≤ D*(t r)^(p+1):= by
 obtain ⟨D,hD,H'⟩:=((tributeOPE F J P R Z M H ν Ht Hp HL l he hK hx L).good p).cost
 refine ⟨D,hD,?_⟩; filter_upwards [H',Ht.running.positive] with r hr hp o x hw u hu
 specialize hr ((⟨u,hu⟩,o,⟨x,hw⟩): Q∴ × E4 × ↥K); simp_rw [alarm, abs_of_pos hp] at hr; rw [creed F J P R Z M H ν Ht Hp HL l he u L p (t r) (hx hw)]; exact hr
end YM.Integration.GradedFar.Batch
