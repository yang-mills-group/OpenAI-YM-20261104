import YM.GradedFar.Logged.Stroke
/-!
# Estimate on the fixed Reader by averaging the new log receipts

Maintaining orientations & linears. Certified Spin, Bookshelf. Compare at the **same**
P.port and frame (unselected vs Reader averaging), as in Orbits/Receipts & Fee.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Logged.Pages
open Finset Filter Function Set Spec Table Extraction OPE.Log Asymptotics Orbits MeasureTheory
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius ContDiff
open Economy (Paint)
attribute [local instance] measO borelO YM.Work.A15.compact_ortho
attribute [local instance] hμ
open private cell_margin int_live from YM.OPE.Orbits.Fee
variable {G:Gauge}{C:Family G}{f:Order}{S:Table C.book}
    (F:Final C f S)(R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    {I L:Type} [Fintype I] (K:Economy.Small L) {M δ:ℝ}(hm:0≤M)(hd:0<δ)
    (x:L→I→E4)(z:L→E4) (hx:∀ᶠ i in K.p,WithinRoom (K.r i) M δ (x i) (z i))
    {d:I→ℕ}
    (bank : LogTrace F R.port) (v: Labels S d)
    (m n:ℕ)
local notation "Q"=>F.sector.derivatives
local notation "X"=>F.sector.turns
local notation "P"=>R.port
local notation "r"=>K.r
local notation "ρ"=>F.room.kernel.spin
open Stroke (lifetime)
local notation "ζ"=>fun l:L=>shadowOld R.port m (x l) (z l) v

section
variable (k:L→Ortho)
local notation "x₀"=>fun i l=>spinning P X n (x l) (z l) i
local notation "ω"=>fun l=>(sole (z l))
include hm hd hx bank
lemma fit_old : Paint K (lifetime d m ∘ K.r) (fun i=>spinning P X n (x i) (z i) (k i) v -spinning P X n (ω i) (z i) (k i) (d:=fun _:Unit=>m) (sole (ζ i))) := by
    let f (i:Mode Q)(l:L) : S.Field n :=∑ y∈(R.port.sheet i).support, ((R.port.sheet i) y * singleError F R m x z v l y (k l)) • F.sector.turns.act n (k l) (R.port.loaded i n)
    refine Paint.assists (f:=fun l=> ∑ i∈bands Q n,f i l) (Paint.sum _ (fun i hi=>Paint.sum _ fun j _=>?_)) ?_
    · have e:= (Stroke.conforms F R K k i n).scales ((Paint.const ((R.port.sheet i) j)).times (Stroke.spun F R K hm hd x z hx bank v k m j)); simpa only [one_mul,mul_one,Function.comp_def] using e
    filter_upwards [Dock.margined F R hm hd x z hx n] with i hi; rw [discrepancy_spin P R.law R.continuum F.phase.transport.motion _ _ hi]; apply Finset.sum_congr rfl; intro j _; exact Finset.sum_smul.symm
lemma fit_colored : Paint K (lifetime d m ∘ K.r)
    (fun i=>spinning P X n (x i) (z i) (k i) (bar ρ v) - spinning P X n (ω i) (z i) (k i) (d:=fun _:Unit=>m) (sole (S.conj ρ m (ζ i)))) := by
    let f (i:Mode Q)(l:L) : S.Field n :=∑ y∈(R.port.sheet i).support, ((R.port.sheet i) y * errorColor F R m x z v l y (k l)) • F.sector.turns.act n (k l) (R.port.loaded i n)
    refine Paint.assists (f:=fun l=> ∑ i∈bands Q n,f i l) (Paint.sum _ (fun i hi=>Paint.sum _ fun j _=>?_)) ?_
    · have e:= (Stroke.conforms F R K k i n).scales ((Paint.const ((R.port.sheet i) j)).times (Stroke.tint F R K hm hd x z hx bank v k m j)); simpa only [one_mul,mul_one,Function.comp_def] using e
    filter_upwards [Dock.margined F R hm hd x z hx n] with i hi; rw [discrepancy_spin P R.law R.continuum F.phase.transport.motion _ _ hi]; apply Finset.sum_congr rfl; intro j _; exact Finset.sum_smul.symm
end

section Average
include hm hd hx
abbrev apart (K:Economy.Small L):Economy.Small (L × Ortho) := ⟨comap Prod.fst K.p,K.r ∘ Prod.fst,K.leaps.comp tendsto_comap⟩
omit bank in
private lemma fare (v:Labels S d) (w:L→ S.Field m)
    (h:Paint (apart K) (lifetime d m ∘ (apart K).r) (fun i=> spinning P X n (x i.1) (z i.1) i.2 v -spinning P X n (sole (z i.1)) (z i.1) i.2 (d:=fun _:Unit=>m) (sole (w i.1)))) :
    Paint K (lifetime d m ∘ K.r) (fun i=>averageV P X n (x i) (z i) v -averageV P X n (sole (z i)) (z i) (d:=fun _:Unit=>m) (sole (w i))) := by
    obtain ⟨C,hC,q,hp⟩:= h; refine ⟨C,hC,q,?_⟩
    filter_upwards [eventually_comap.mp hp,Dock.margined F R hm hd x z hx n] with i hi h
    rw [averageV,averageV,if_pos h, if_pos (cell_margin F R (z i) n),← integral_sub (int_live F R v h) (int_live F R (d:=fun _:Unit=>m) _ (cell_margin F R _ _))]
    let c:= C* badge (K.r i)^q* |lifetime d m (K.r i)|
    exact (norm_integral_le_of_norm_le_const (C:=c) (Eventually.of_forall fun u=> hi (i,u) rfl)).trans_eq (by simp; rfl)
include bank
lemma average_benefit : Paint K (lifetime d m ∘ K.r) (fun i=> checkReal P R.law R.continuum n (x i) (z i) v -
    checkReal P R.law R.continuum n (sole (z i)) (z i) (d:=fun _:Unit=>m) (sole (ζ i))) := by
    let Z i:=shadowOld R.port m (x i) (z i) v
    have ht:= fit_old F R (apart K) hm hd (x ∘ Prod.fst) (z ∘ Prod.fst) (Filter.Tendsto.eventually tendsto_comap hx) bank v m n Prod.snd
    have hu:= fit_colored F R (apart K) hm hd (x ∘ Prod.fst) (z ∘ Prod.fst) (Filter.Tendsto.eventually tendsto_comap hx) bank v m n Prod.snd
    have he:= fare F R K hm hd x z hx m n v Z ht
    have hv:= fare F R K hm hd x z hx m n (bar ρ v) (fun i=>S.conj ρ m (Z i)) hu
    have hs:=(he.plus (Paint.linear_r (conjugateR ρ n) hv)).scales_r (Paint.const (2⁻¹:ℝ)); simp_rw [one_mul] at hs
    apply hs.assists; filter_upwards with i; simp_rw [checkValue];
    dsimp only [Function.comp_apply] -- unfold bar pivot
    rw [show bar ρ (d:=fun _:Unit=>m) (sole (ζ i))=sole (S.conj ρ m (ζ i)) from rfl, _root_.map_sub, ← smul_sub];
    unfold Z; congr 1; abel

lemma fresh_log : Paint K (lifetime d m ∘ K.r)
  (fun i=> R.fresh n (x i) (z i) v -R.cutTest n m (ζ i)) := by
    apply (Paint.linear_c (R.knife n) (average_benefit F R K hm hd x z hx bank v m n)).assists
    filter_upwards with i
    let g:Labels S (fun _:Unit=>m):= sole (ζ i); let c:=z i
    have hh: checkReal P R.law R.continuum n (sole c) c g=checkReal P R.law R.continuum n (sole 0) 0 g:=by
      apply Eq.trans ?_ (checkReal_transfer n R.law R.continuum _ _ _ c); rw [zero_add,(show (fun i:Unit=>sole (0:E4) i+c)=sole c from funext (fun _=>zero_add _))]
    simp only [Function.comp_apply,map_sub]; change _ - R.knife n (checkReal P R.law R.continuum n (sole c) c g)= _; rw [hh]; rfl
end Average
end YM.OPE.Logged.Pages
