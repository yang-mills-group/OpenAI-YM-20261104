import YM.GradedFar.Kiosk
/-!
# post-inverse compare: iterate derivatives BEFORE pricing through requested horizon

physical first-push (and center margin receipts) in Reels and formal shape derivatives from FTC.
Also resolves inclusion of formal c without requiring comparing price for a different formal matching:
uses uniqueness after both comparisons on the one setup.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Window
open Function Filter Set MeasureTheory Metric PowerSeries
open Extraction Table Spec OPE OPE.Orbits OPE.Nesting PhysMS Trace.Pilot
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 FVA2.Scale FVA2.Scale.Facets FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh MS MS.Native MS.Land MS.Fleet
open Tariff Tariff.Sunshine FVA2.GradedFar.Cart
open scoped Topology BigOperators ContDiff Classical
local instance {n:ℕ} : ContinuousSMul ℝ (Points n):= IsBoundedSMul.continuousSMul
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book} (F : Final C f S) (P: ℝ→tower S) (R: Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
variable (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true)
local notation "V"=> Scale.Measure.outlook (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
variable {n h d:ℕ} (l:Toon G d)
local notation "X" => Points n
local notation "ι" => Fin n × Axis
local notation "Y" => Toon G (h+1)
variable {t:ℝ→ℝ} (ht:Coupling G t) (Hn: ∀ h, Regained F P R (Scale.Measure.outlook (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)) t n h d)
    (Hs: ∀ h, ∀ j, ∀ (hj:j ≤ h), Neighbor.Included F P j h hj)(α: ∀ h, Future G h)(hα: ∀ h,PaidFuture F P (α h) t)

variable (u:ListInput G n h)
include Hn Hs H ht hα
lemma disp (p:ℕ)(i:ℕ) : ContDiffOn ℝ p (fun x=> coeff i (Cargo V x u l)) (conf n):=by
 induction p generalizing h i with
 | zero=> rw [Nat.cast_zero, contDiffOn_zero]; exact cargo_cont Z M H l u i
 | succ p ih=>
    let f:= launch Z l (α h) u i; have he (x:X) (hx:x∈conf n) : HasFDerivAt (fun x=> coeff i (Cargo V x u l)) (f x) x:= trueC F P R Z M H l ht Hn (Hs (h+1) h (Nat.le_succ h)) (α h) (hα h) u i hx
    have hg:ContDiffOn ℝ p f (conf n):= by
       unfold f launch; refine ContDiffOn.sum (fun j (_:j∈ Finset.univ)=> ?_)
       have hf:ContDiffOn ℝ p (fun x=> coeff i (projectionOne Z l (α h) u j x)) (conf n):=by
          simp_rw [projectionOne,map_sum, coeff_mul]; refine ContDiffOn.sum (fun t (_:t ∈ Finset.univ)=> ?_); exact ContDiffOn.sum (fun a _=> contDiffOn_const.mul (ih _ a.2))
       exact hf.smul contDiffOn_const
    rw [Nat.cast_add_one]; exact (contDiffOn_succ_iff_fderiv_of_isOpen (conf_open _)).2 ⟨fun x hx=> (he x hx).differentiableAt.differentiableWithinAt,(by simp),hg.congr (fun x hx=> (he _ hx).fderiv)⟩
lemma disp_all (k:ℕ):ContDiffOn ℝ ∞ (fun x=> coeff k (Cargo V x u l)) (conf n):=contDiffOn_infty.mpr fun p=> disp F P R Z M H l ht Hn Hs α hα u p k
def liability {e:Fin n→ℕ} (v:AppointedH140Inputs G e)(x:X)(L:TraceOrder n): PowerSeries ℂ:= PowerSeries.mk
 (fun k=> δ L (fun x=> coeff k (Cargo V x v l)) x)
lemma liability_cons (i:ι)(L:TraceOrder n) {x:X}(hx:x∈conf n) : liability Z l u x (i::L)= ∑ j: Toon G (h+1),α h i.2 (u i.1) j * liability Z l
    (update (climbing u) i.1 (theory j): ListInput G n (h+1)) x L := by
 ext1 k; let t₂ (j: Toon G (h+1)):ListInput G n (h+1):=update (climbing u) i.1 (theory j); let f(j: Toon G (h+1))(x:X):=Cargo V x (t₂ j) l; let c:=α h i.2 (u i.1)
 have he : EqOn (Points.gradient i.1 i.2 (fun x=> coeff k (Cargo V x u l))) (fun x=> coeff k (∑ j,c j * f j x)) (conf n):= fun x hx=>
    ((DFunLike.congr_fun (trueC F P R Z M H l ht Hn (Hs (h+1) h (Nat.le_succ h)) (α h) (hα h) u k hx|>.fderiv) (Points.direction i.1 i.2)).trans (launchSlot ..))
 simp_rw [liability,map_sum,coeff_mul,coeff_mk]; rw [δ,δ_congr (conf_open _) he L hx]; simp_rw [map_sum (coeff k),coeff_mul]; let p:=Finset.HasAntidiagonal.antidiagonal k
 have ho(t: Toon G (h+1))(s:ℕ×ℕ): ContDiffOn ℝ ∞ (fun x=> coeff s.1 (c t) * coeff s.2 (f t x)) (conf n):= contDiffOn_const.mul (disp_all F P R Z M H l ht Hn Hs α hα (t₂ t) s.2)
 rw [δ_sum (conf_open _) _ _ (fun t _=>ContDiffOn.sum (fun s _=> ho t s)) L hx]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [δ_sum (conf_open _) p _ (fun t _=> ho j t) L hx]; exact Finset.sum_congr rfl fun s _=> δ_const_mul (conf_open _) (disp_all F P R Z M H l ht Hn Hs α hα (t₂ j) _) _ L hx
omit ht Hn Hs hα H in
lemma messenger_cons (i:ι)(L:TraceOrder n)(o:E4){r:ℝ}(Hu: Going F P h r){x:X}(hx: arena F R d o r x) :
    δ (i::L) (fun x=> messenger F P R o r l x u) x=∑ j: Toon G (h+1), coord j (push F P h i.2 r (u i.1))*δ L (fun x=> messenger F P R o r l x (update (climbing u) i.1 (theory j): ListInput G n (h+1))) x:=by
 let U(j: Toon G (h+1)):ListInput G n (h+1):=update (climbing u) i.1 (theory j); let f(j: Toon G (h+1))(x:X):=messenger F P R o r l x (U j); let Z₀:={x:X|arena F R d o r x}; have hi(j: Toon G (h+1)): ContDiffOn ℝ ∞ (f j) Z₀:= fun x hx=> (breeze F P R o r l x hx _).contDiffWithinAt; have ht:=season_open F R d o r n
 let g(j: Toon G (h+1))(x:X):=coord j (push F P h i.2 r (u i.1))* f j x; have he: EqOn (Points.gradient i.1 i.2 (fun x=>messenger F P R o r l x u)) (fun x=> ∑ j,g j x) Z₀:=fun x hx=> (mete F P R o r l Hu u x i hx).trans (changing ..)
 rw [δ,δ_congr ht he L hx,δ_sum ht _ _ (fun j _=> contDiffOn_const.mul (hi j)) L hx]; exact Finset.sum_congr rfl fun j _=> δ_const_mul ht (hi j) _ L hx
variable {K:Set (Points n)} (hK:IsCompact K)(hx:K⊆ conf n)

include hK hx
lemma derivativeCosts (L:TraceOrder n): Receives t trail (fun r (i:E4 × ↥K)=> δ L (fun x=> messenger F P R i.1 r l x u) i.2.val) (fun i=> liability Z l u i.2.val L) := by
 induction L generalizing h with
 | nil=> exact Receives.congr (Hn h (fun _=>le_rfl) K hK hx l u) (Eventually.of_forall (fun _=>rfl)) (fun _=> (by ext1 k; rw [liability,coeff_mk]; rfl))
 | cons i L ih=>
    let f(j: Toon G (h+1))(r:ℝ)(p:E4 × ↥K):= coord j (push F P h i.2 r (u i.1)) * δ L (fun x=> messenger F P R p.1 r l x (update (climbing u) i.1 (theory j):ListInput G n (h+1))) p.2.val; let t₂ (j: Toon G (h+1))(p:E4 × ↥K):= α h i.2 (u i.1) j * liability Z l (update (climbing u) i.1 (theory j) : ListInput G n (h+1)) p.2.val L
    have he(j: Toon G (h+1)):Receives t trail (f j) (t₂ j):= Receives.mul (Receives.along (hα h _ _ _) (fun _=>())) (ih _) (Coupling.conforms hG ht)
    apply Receives.congr (Receives.sum Finset.univ fun i _=> he i); · exact ((near_collar F R n d hK hx).and (Hs (h+1) h (Nat.le_succ h))).mono fun r hr=> funext (fun p=> (messenger_cons F P R l u i L p.1 hr.2 (hr.1 _ p.2.property p.1)).symm)
    exact fun p => (liability_cons F P R Z M H l ht Hn Hs α hα u i L (hx p.2.property)).symm
variable {e:Fin n→ℕ}(he:AppointedH140Through h e)
include he
lemma mixedCosts (v:AppointedH140Inputs G e)(L:TraceOrder n) : Receives t trail (fun r (i:E4 × ↥K)=> δ L (fun x=> messenger F P R i.1 r l x v) i.2.val) (fun i=> liability Z l v i.2.val L) := by
 apply Receives.congr (derivativeCosts F P R Z M H l ht Hn Hs α hα (GradedFar.raised he v) hK hx L); · exact (eventually_all.mpr (fun i=> Hs _ _ (he i))).mono (fun r hr=> funext (fun i=> by simp_rw [resurface F P R _ r l he hr _ v])) -- simplify lambdas
 intro i; ext1 k; simp_rw [liability,coeff_mk]; exact δ_congr (conf_open n) (fun y hy=> congrArg (coeff k) (cargo_inclusions F P R l ht Hs (Hn h) hy he v (hG:=hG))) L (hx i.2.property)
omit hK hx in
lemma mixedS (v:AppointedH140Inputs G e)(k:ℕ) : ContDiffOn ℝ ∞ (fun x=> coeff k (Cargo V x v l)) (conf n):=(disp_all F P R Z M H l ht Hn Hs α hα (GradedFar.raised he v) k).congr (fun _ hx=> congrArg (coeff k) (cargo_inclusions F P R l ht Hs (Hn h) hx he v (hG:=hG)).symm)
end YM.Integration.GradedFar.Window
