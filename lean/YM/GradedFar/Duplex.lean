import YM.GradedFar.Navigating
/-!
# Bootstrapping compact orientation from the actual mixed-experiment PoseFit input

`MultiPose` is small subset of C5 & earlier purchases required. Does NOT assume the
frame closeness itself. This and the indicated Leading, axes conditions (plus budgets) suffice at compact
ratio and extended ratio. Uses only quadratic slots at the same wall as in our final inverse (at its
own aperture here). cf bbcb 1468.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Tariff.Billboard
open Function Filter Set PowerSeries
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 FVA2.Scale FVA2.Scale.Facets FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Fleet
open YM.Integration.GradedFar.Neighbor YM.Integration.GradedFar.Tariff.Playbill
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)(J P:ℝ→tower S)
   (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
   {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true)
local notation "Post" => Scale.Measure.outlook (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
local notation "Before"=> Scale.Measure.start (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
local notation "Σ0"=> outgoing RootG
private abbrev panel: Stage 2:= ⟨Σ0,ok_wall⟩
variable (h:ℕ)
local notation "V"=>Sec G h
local notation "mark"=> Neighbor.stamp G h
local notation "Ops"=> Operation G h
local notation "g∴" => strength G

/-- The unselected mixed home assertion. Poses in these r units (using same wall).
W is J when using (C5); if using these as previous hypotheses see also Era.
-/
def shared (h:ℕ)(p:Route)(v w:Sec G h):ℂ:=
    S.classMoment (spectator F none) (Ceiling 2 h) (p.1 • Σ0)
        ![assign J (next p) h (Level.Dial h (Real.log (stretch p)) v), assign J p.1 h w]
lemma shares (i:Route)(v w:V): shared F J h i v w = frank F J none h i.1 Σ0 (carpet h (adapted J h i v) w):=by
 unfold shared; apply congrArg (S.classMoment (spectator F none) (Ceiling _ h) (i.1 • Σ0)); funext j; fin_cases j
 exacts [(atHome J ..).symm, rfl]

def Mixed (h:ℕ):Prop:= ∀ v w : Sec G h, Tendsto (fun i=>shared F J h i v w) upGauge (𝓝 (iris panel (carpet h v w)))

structure MultiPose (h:ℕ) (q:ℕ) (τ:Route→ℝ)(α β:Route→ Sec G h→ₗ[ℂ] Sec G h):Prop where
 left : Tendsto τ upGauge (𝓝 0)
 today : Tendsto (fun i=>Neighbor.stamp G h (α i)) upGauge (𝓝 1) -- lim of Cash(vec at s), not of frame
 cost : Tendsto (fun i=>Neighbor.stamp G h (β i)) upGauge (𝓝 1)
 time (v w: Sec G h) : ∃ c:ℝ,0≤c ∧ ∀ᶠ i in upGauge,
    ‖shared F J h i v w - appointedH140Crop q (τ i) (sent Before h Σ0 (carpet h (α i v) (β i w)))‖ ≤ c*g∴ i.1
-- name `earlierUpC5` used in final. even ∃ψ per window allowed but data simultaneous on cost clocks.
def JointTicket (h:ℕ): Prop:=∃ q τ α β, MultiPose F J Z h q τ α β
include H
lemma crop_lead (q:ℕ)(p:V)(w:V): appointedH140Crop q 0 (sent Before h Σ0 (carpet h p w))=iris panel (carpet h p w):= by
 have hx: Σ0∈conf 2:=ok_wall; rw [crop_eq,Finset.sum_eq_single 0,pow_zero,one_mul,cashed Before _ hx,before0 Z M H]
 exacts [fun x _ hx=>by rw [Complex.ofReal_zero, zero_pow hx,zero_mul],by simp]
private lemma costPoll {q τ} {α β} (H': MultiPose F J Z h q τ α β) (v w:V) : Tendsto (fun i=> appointedH140Crop q (τ i)
    (sent Before h Σ0 (carpet h (α i v) (β i w)))) upGauge (𝓝 (iris panel (carpet h v w))):=by
 have hm(A:Route→V→ₗ[ℂ] V)(p)(he:Tendsto (fun i=> Neighbor.stamp G h (A i)) upGauge (𝓝 1)): Tendsto
    (fun i=> columns G h (A i p)) upGauge (𝓝 (columns G h p)):= by
    simp_rw [← stamped]; exact ((ContinuousLinearMap.apply ℂ (Sheet G h) (columns G h p)).continuous.tendsto (1:Operation G h)).comp he
 have hx(j:Fin 2):Tendsto (fun i=> columns G h (carpet h (α i v) (β i w) j)) upGauge (𝓝 (columns G h (carpet h v w j))):=by
    fin_cases j; exact hm α v H'.today; exact hm β w H'.cost
 rw [← crop_lead Z M H h q]; simp_rw [crop_as_is (carpet h _ _)]; refine tendsto_finsetSum Finset.univ fun i _=> ?_
 have hn (A:PowerSeries ℂ): Continuous (fun t:ℝ=> appointedH140Crop q t A):= by simp_rw [crop_eq]; exact continuous_finsetSum _ (fun j _=> (Complex.continuous_ofReal.pow _).mul continuous_const)
 exact (tendsto_finsetProd Finset.univ (fun l _=> tendsto_pi_nhds.mp (hx l) (i l))).mul (((hn (sent Before h Σ0 (basisWord i))).continuousAt.tendsto).comp H'.left)

lemma makes (hv:JointTicket F J Z h): Mixed F J h:=by
 obtain ⟨q,τ,α,β,hx⟩:= hv; intro v w; obtain hp:= costPoll F J Z M H h hx v w; let X(i:Route):=appointedH140Crop q (τ i) (sent Before h Σ0 (carpet h (α i v) (β i w)))
 have ht : Tendsto (fun i=> shared F J h i v w-X i) upGauge (𝓝 0):=by
    obtain ⟨C,hC,H⟩:= hx.time v w; exact squeeze_zero_norm' H (by simpa only [mul_zero,Function.comp_apply] using (((Coupling.conforms hG (strength_coupling hG)).comp
       (running.mono_left (show upGauge≤clock from inf_le_left))).const_mul C))
 exact Tendsto.congr' (Eventually.of_forall (fun i=> sub_add_cancel ..)) (by simpa only [zero_add] using ht.add hp)

omit H in
private lemma at_score (u w:V)(H:Mixed F J h): Tendsto (fun i:Route=> frank F J none h i.1 Σ0 (carpet h u w)) clock (𝓝 (iris panel (carpet h u w))):=by
 let j:Joggle:=⟨1,by constructor <;> norm_num⟩
 let v (i:Route):Route:= (i.1,j)
 have hv:Tendsto v clock upGauge:=tendsto_inf.mpr
    ⟨tendsto_prod_iff'.mpr (And.intro (show Tendsto (fun i:Route=>(v i).1) clock trail from running) tendsto_top),
     tendsto_principal.mpr (Eventually.of_forall (fun i:Route=> (show (1:ℝ) ≤ stretch (v i) from le_rfl)))⟩
 refine ((H u w).comp hv).congr (fun i=>?_); dsimp only [Function.comp_apply]; rw [shares,adapted];
 have ht: stretch (v i)=1:= rfl; rw [ht,Real.log_one,Level.flat,mul_one]; unfold asset next; rw [ht,mul_one]; apply congrArg; apply congr_arg₂ (carpet h) _ rfl
 exact (assign J _ h).symm_apply_apply _

private def wall (i:Toon G h)(F:MultilinearMap ℂ (fun _:Fin 2=>Sec G h) ℂ): V→ₗ[ℂ] ℂ:= F.toLinearMap (carpet h 0 (Bank.detector i)) 0
private def retina (i:Toon G h)(F:MultilinearMap ℂ (fun _:Fin 2=>Sec G h) ℂ) : Sheet G h→L[ℝ]ℂ:=
    ((wall h i F).comp (columns G h).symm.toLinearMap).toContinuousLinearMap.restrictScalars ℝ
omit H in
lemma retina_value (i:Toon G h)(F: MultilinearMap ℂ (fun _:Fin 2=>Sec G h) ℂ)(v:V): retina h i F (columns G h v)= F (carpet h v (Bank.detector i)):= by
 change F (update _ _ ((columns G h).symm _)) = _; rw [LinearEquiv.symm_apply_apply, ← carpet_update h v (Bank.detector i)]

lemma Mixed.bootstrap (H0: Mixed F J h): SteadyUp J h:= by
 let L(i:Toon G h):= retina h i (iris panel); let t(p:Route)(i:Toon G h):= retina h i (frank F J none h p.1 Σ0); let B:= Bank.place h (Bank.initial Post h)
 have hr: Ground Post:= (H.separatedOPE 0).wilson.wardRank
 have he(v:Sheet G h)(a:∀ i,L i v=0): v=0:= by
    obtain ⟨v,rfl⟩:=(columns G h).surjective v; have hc:(B v) =0:=by
       funext i; unfold B; rw [Bank.placed]; let k:= carpet h v (Bank.detector i); have hf : Σ0 ∈ conf 2:= ok_wall
       change Bank.initial Post h _ (fun _=>Bank.detector i)=0; rw [towall h Post v (Bank.detector i) 0, crop_eq]; simp only [FormalCompact,coeff_mk,Nat.zero_add, Finset.sum_range_one,pow_zero,one_mul,lead0 Z M H (h:=h)]
       specialize a i; unfold L at a; rw [retina_value] at a; exact a
    rw [((injective_iff_map_eq_zero B).1 (Bank.detected hr) v hc),map_zero]
 have hj(i : Toon G h)(v : V): Tendsto (fun p=> t p i (columns G h v)) clock (𝓝 (L i (columns G h v))):=by simp_rw [t,L,retina_value]; exact at_score F J h v _ H0
 have hh(i: Toon G h)(v: Sheet G h): Tendsto (fun p=>t p i v) clock (𝓝 (L i v)):= by obtain ⟨v,rfl⟩:= (columns G h).surjective v; exact hj ..
 obtain ⟨s,C,hC,H⟩:= issued L he (fun i v=> hh i v |>.mono_left (show upGauge≤clock from inf_le_left)); unfold SteadyUp; refine plan_cpx (fun i=>?_); obtain ⟨v,rfl⟩:= (columns G h).surjective i
 have hv(i: Toon G h): Tendsto (fun p=> t p i (columns G h (adapted J h p v)-columns G h v)) upGauge (𝓝 0):=by
    have he:= H0 v (Bank.detector i); have hp:= hj i v; unfold t L at hp; unfold t -- too much
    simp_rw [map_sub,retina_value]; simp_rw [shares] at he; simp_rw [retina_value] at hp
    simpa only [sub_self] using he.sub (hp.mono_left (show upGauge≤clock from inf_le_left))
 simp_rw [stamped]; apply tendsto_iff_norm_sub_tendsto_zero.mpr; refine squeeze_zero' (Eventually.of_forall fun _=> norm_nonneg _) (H.mono fun p hhh=> hhh (columns G h (adapted J h p v)-columns G h v)) ?_
 have hp : Tendsto (fun i:Route=> (fun j:↥s=> t i (j.val) (columns G h (adapted J h i v)-columns G h v))) upGauge (𝓝 0):= tendsto_pi_nhds.mpr fun i=> hv i.val
 simpa only [norm_zero,mul_zero] using hp.norm.const_mul C
end YM.Integration.GradedFar.Tariff.Billboard
