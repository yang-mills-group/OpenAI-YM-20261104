import YM.QuadraticLocal.Poetry.Vendor
import YM.QuadraticLocal.Poetry.Glass
/-!
# Upper-fold lantern receipts once registered.
Heat payload at κ.A. common trajectory horizon.Spec.C. Might be used in anisotropic widths post transfer.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Poetry.Roll
open Function Filter Lattice Laurent Wilson RG Gauge Precision Tree Exterior
open Matrix Finset Push Uniform
open AbsoluteSums AllOrder AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Fire PertExtension.Series Radial
open AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Field AllOrder.Ink.Money
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open Sunrise Sunrise.Focus Stationary
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {V G0:Type} {ι α M: Type}[Fintype M][Fintype α][DecidableEq M] {G:Gauge} (H:Finset M)(q:M) {a C D b K:ℝ} {n m:Side}{k d N l:ℕ}
local notation "Ω" => (Coarse G ⊕ M)
local notation "Z"=> Point M
local notation "E"=> Point (Coarse G⊕M)
variable (T:Roll G M)(e:ℕ)
def folded (d:ℕ):Ink.Field (Coarse G⊕ M):= Field.sum fun i=> (T.leg i).charter e d
local notation "Λ₀" d:max=> folded T e d
local notation "K'" i:max d:max=> Lantern.charter (T.leg i) e d
local notation "J"=> Link G n
local notation "G'"=> T.leg
open Picket PositionX.Jet
-- cost published uniformly.Level a from previous first-level occupancy.
structure Posture (M:Type)[DecidableEq M][Fintype M] (G:Gauge)(H:Finset M)(q:M)(C a b:ℝ)(k e d:ℕ) : Prop where
   sunny:0<b
   allot:0≤C
   reality : ∀ T: Lantern G M,T.Bears H q k→ (T.charter e d).Good b (C*T.money a) (k+(d-e))
variable (P:Posture M G H q K a b k e d)(h:T.Faith H q k a C) (ht:T.honest)
variable (A: Stationary.Link G n)(x:Site n)(v:rule M n)
local notation "σ₀" x:max=> ((q)) -- not used
local notation "e₀"=> k+(d-e)
local notation "Y₁" i=> K*T.price a i
include h P
lemma lot (i:T.Ty): (K' i d).Good b (K*T.price a i) (k+(d-e)):=P.reality (T.leg i) (h.pinned i)
lemma interest : SumBudget (fun i=>K*T.price a i) (K*C):= budget_scale P.allot h.price
lemma warmth : (Λ₀ d).Good b (K*C) (k+(d-e)):= Field.keep (fun i=> (T.leg i).charter e d) (fun i=> lot H q T e P h i) (Roll.interest H q T e P h)
lemma stays : Fixed H q (folded T e d):= ⟨fun i=> ((T.leg i.1).elected H q (h.pinned _) e d).tracked i.2, fun i=> ((T.leg i.1).elected H q (h.pinned _) e d).root i.2⟩
-- Vital terms at site test
lemma grip (χ : (rule (Coarse G⊕M) n→ℝ)→ℝ) (hL:LinTest _ (k+(d-e)) χ): HasSum (fun i:T.Ty=> χ ((K' i d).site n x)) (χ ((Λ₀ d).site n x)) := (((Roll.warmth H q T e P h).tests P.sunny.le (z:=x) hL).sigma (fun i=> (lot H q T e P h i|>.tests P.sunny.le (z:=x) hL))) -- sigma defeq
lemma renew : (Λ₀ d).site n x (mingle A v)=∑' i, Lantern.gleam (T.leg i) x v e d A:= by
 rw [← (show HasSum _ ((Λ₀ d).site n x (mingle A v)) from grip H q T e P h x _ (LinTest.eval _ (mingle A v))).tsum_eq]; exact tsum_congr fun i=>Lantern.read ..
-- leading.Memory.Step. completion sign true port H.Ed stand.
lemma summit (he:d=e) : (Λ₀ d).table n (mingle A v)= Roll.total T n A v := by rw [Field.table_apply]; refine Finset.sum_congr rfl (fun i _=>?_); rw [renew H q T e P h]; exact tsum_congr fun i => by unfold Roll.dusk; subst d; exact (Lantern.height ..).symm
lemma nil_before (he:d<e) : (Λ₀ d).table n (mingle A v)=0:=by rw [Field.table_apply]; simp_rw [renew H q T e P h, Lantern.pre _ _ _ _ he,Pi.zero_apply,tsum_zero,Finset.sum_const_zero] -- syntax pre
lemma weighed (f:ℝ→Link G n)(hv:ContDiffAt ℝ ω f 0)(j:ℕ) :
   HasSum (fun i:T.Ty=>someJ (Lantern.gleam (T.leg i) x v e d ∘ f) j) (someJ ((Λ₀ d).site n x ∘ fun r:ℝ=> mingle (f r) v) j):= by
 let hχ:= AllOrder.Ink.Pointwise.familiar j (fun r=> mingle (f r) v) (Glass.tacit n _ _ hv) (k+(d-e)); refine (grip H q T e P h x _ hχ).congr_fun (fun i=>?_)
 simp_rw [Function.comp_def,Lantern.read]
omit P
-- across ALL j in aperture.Singular.
variable {B:ℕ→ℝ}(hP:∀ j≤ N, Posture M G H q (B j) a b k e j)
local notation "v₀" j:max=> T.folded e j
include hP ht
lemma embossed (x:Site n)(hx:d≤N) : Vernal G n (fun j z=> (T.folded e j).site n x (mingle z v)) d:= by
 refine ⟨fun a b s g hv hh hG hm=>?_⟩; have h(y:ℝ→Link G n)(he:ContDiffAt ℝ ω y 0): HasSum (fun i:T.Ty=> weigh y (Lantern.gleam (T.leg i) x v e) d) (weigh y (fun j z=>(v₀ j).site n x (mingle z v)) d) := hasSum_sum (s:=Finset.range (d+1)) (fun i hi=> weighed H q T e (hP i (le_trans (Nat.le_of_lt_succ (mem_range.mp hi)) hx)) h x v y he (d-i)) -- parameter F argument likely missing x.Shadow
 rw [←(h a hv).tsum_eq, ← (h b hh).tsum_eq]; apply tsum_congr; intro i; exact ((T.leg i).ever x v e (ht i) d).leaf a b s g hv hh hG hm -- syntax
-- Mark entire stationary print, common publication `Phase.State.Exposure`. Never across Γ slots
lemma spirit (hx:d≤N) : Vernal G n (fun j z=> (T.folded e j).table n (mingle z v)) d := by
 have hp(y:ℝ→ Link G n)(hz:ContDiffAt ℝ ω y 0) : weigh y (fun j z=> (T.folded e j).table n (mingle z v)) d= ∑ x:Site n, weigh y (fun j z=> (T.folded e j).site n x (mingle z v)) d:= by
    unfold weigh; rw [Finset.sum_comm (s:=Finset.univ)]; -- RHS sum_comm s name
    apply Finset.sum_congr rfl; intro i hi; have he:= warmth H q T e (hP i (le_trans (Nat.le_of_lt_succ (mem_range.mp hi)) hx)) h; exact (AllOrder.Ink.Pointwise.familiar (d-i) (fun r=> mingle (y r) v) (Glass.tacit n y v hz) _).finiteTest _ (fun x=> (T.folded e i).site n x) (fun x _=> (he.site (hP i (by have := mem_range.mp hi; omega)).sunny.le x).2.1)
 refine ⟨fun u w s hw ha hb H0 hx' =>?_⟩; rw [hp _ ha,hp _ hb]; apply Finset.sum_congr rfl; intro x hx''; apply (embossed H q T e ‹_› ht v hP x hx).leaf u w s hw ha hb H0 hx'
end YM.QuadraticLocal.Poetry.Roll
