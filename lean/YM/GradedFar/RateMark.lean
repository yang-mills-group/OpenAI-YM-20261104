import YM.GradedFar.Riddle
import YM.XSpace.Panorama
/-! # Actual measurement Jacobian entries with polynomial partners

Use divided differences (hence exact variation across this single path); leading is the actual
finite rank map. These aren't power-series assertions, actually control the price in changing
both fields and clock inside the normalized K-weight measurement at H.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Tariff.Billboard
open Function Filter Set PowerSeries MeasureTheory
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 FVA2.Scale FVA2.Scale.Facets FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Book MS.Book.Program MS.Book.Convolve MS.Fleet MS.Menus
open YM.Integration.GradedFar.Neighbor YM.Integration.GradedFar.Tariff.Playbill FVA2.GradedFar.Cart
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)(J:ℝ→tower S)
    (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (ν:ℝ){hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true)
local notation "Post" => Scale.Measure.outlook (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
local notation "Φ" => bFare Z M ν
local notation "PΦ" => φPred Z M ν
local notation "AΦ" => stripe J
variable (p:ℕ) (t:ℝ→ℝ){n h:ℕ} (x:Stage n) (u:ListInput G n h)
local notation "Ω"=> MoveSpace G h
local notation "Ω'" => Normalize.Change G h -- coe
local notation "V" => Sec G h
local notation "W" => FieldEnd G h

def release (G:Gauge)(h:ℕ): MoveSpace G h →ₗ[ℝ] FieldEnd G h :=
    (Normalize.Change G h).subtype ∘ₗ (guide G h).symm.toLinearMap
def see (v:V): MoveSpace G h →ₗ[ℝ] Sec G h := ((LinearMap.applyₗ (R:=ℂ) v).restrictScalars ℝ) ∘ₗ release G h

noncomputable def spliced (i:Route)(a:Fin n) : ListInput G n h:=
    splice (fun j=> stripe J h i (u j)) (fun j=> Φ h t p i (u j)) a.val
noncomputable def branch (i:Route): MoveSpace G h →ₗ[ℝ] ℂ := ∑ j:Fin n, (((bearing F J i h x).toLinearMap
    (spliced J Z M ν p t u i j) j).restrictScalars ℝ).comp (see (u j))
noncomputable def baseline : MoveSpace G h→ₗ[ℝ] ℂ:= ((Manifest.response x u).restrictScalars ℝ).comp (release G h)
def TickSpace (G:Gauge)(h:ℕ):Type:= ℝ× MoveSpace G h -- abbrev below instead
local notation "g"=> strength G
abbrev Tick (G:Gauge)(h:ℕ):= ℝ × MoveSpace G h

def entry : Tick G h →ₗ[ℝ] ℂ := (baseline x u).comp (LinearMap.snd ℝ _ _) - (LinearMap.fst ℝ _ _).smulRight (Post h n x 1 u)
lemma entry_eval (d:Tick G h): entry Z x u d= Manifest.response x u (release G h d.2)-(d.1:ℂ)*Post h n x 1 u:=rfl

def debit (i:Route): Tick G h →ₗ[ℝ] ℂ:= (branch F J Z M ν p t x u i).comp (LinearMap.snd ℝ _ _)-
    (LinearMap.fst ℝ _ _).smulRight (traverse p (sent Post h x.val u) (t (next i)) (PΦ p t i))
def slide (i:Route):= t (next i)-PΦ p t i
def billΔ (i:Route)(h:ℕ): MoveSpace G h:= if hx:switchValue J Z M ν i h p t∈Normalize.Change G h then guide G h ⟨_,hx⟩ else 0
local notation "β" => billΔ J Z M ν p t
local notation "Δt" => slide Z M ν p t

variable (ht:Coupling G t)(hh:Held J h)(Hκ:ClassExpansion F J (Scale.Measure.outlook Z.scheme Z.criterion) t n h)
include hh H
lemma billing : ∀ᶠ i in clock, release G h (β i h)= switchValue J Z M ν i h p t:=by
 filter_upwards [stays J Z M ν H t p hh] with i hi; rw [release,billΔ,dif_pos hi, LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]; rfl
lemma exact_measure : ∀ᶠ i in clock, debit F J Z M ν p t x u i (Δt i, β i h)=
    bearing F J i h x (fun j=> AΦ h i (u j))-bearing F J i h x (fun j=> Φ h t p i (u j)) -
      (appointedH140Crop p (t (next i)) (sent Post h x.val u) - appointedH140Crop p (PΦ p t i) (sent Post h x.val u)):=by
 filter_upwards [billing J Z M ν H p t hh] with i hi
 change branch F J Z M ν p t x u i (β i h) - (↑(Δt i):ℂ)*traverse _ _ _ _= _; rw [slide,walking,sub_left_inj]
 rw [splice_row (bearing F J i h x) (u:=fun j=> AΦ h i (u j)), branch,LinearMap.sum_apply]; exact Finset.sum_congr rfl fun j _=> by
   change bearing F J i h x (update (spliced J Z M ν p t u i j) j (release G h (β i h) (u j)))= _; rw [hi]; rfl
include ht Hκ
omit Hκ in
lemma splicing (a j:Fin n): Tendsto (fun i=> columns G h (spliced J Z M ν p t u i a j)) clock (𝓝 (columns G h (u j))):= by
 unfold spliced splice; split_ifs with h; · exact hold J _ hh _
 exact lighten Z M ν H ht _ p
attribute [local irreducible] traverse
lemma leading_debit (hp:1≤p)(y:Tick G h): Tendsto (fun i=> debit F J Z M ν p t x u i y) clock (𝓝 (entry Z x u y)):=by
 have hx: Tendsto (t ∘ next) clock (𝓝 0):= (Coupling.conforms hG ht).comp nextPath
 have hv:Tendsto (fun i=> branch F J Z M ν p t x u i y.2) clock (𝓝 (baseline x u y.2)):= by
   simp_rw [branch,LinearMap.sum_apply]; refine tendsto_finsetSum Finset.univ ?_; intro i _
   refine bearing_tends F J Z M ν H ht Hκ x (u:=fun q=> update (spliced J Z M ν p t u q i) i
       (release G h y.2 (u i))) (v:=update u i (release G h y.2 (u i))) ?_; intro j; by_cases h:j=i; · subst j; simp_rw [update_self]; exact tendsto_const_nhds
   simp_rw [update_of_ne h]; exact splicing J Z M ν H p t u ht hh i j
 have hZ:= traverse_limit hp hx (φZero Z M ν H ht p) (sent Post h x.val u); rw [cashed Post _ x.property] at hZ
 exact hv.sub (hZ.const_mul (y.1:ℂ))
lemma individual : ∃ b:ℝ,0≤b ∧ ∀ᶠ i in clock, ‖debit F J Z M ν p t x u i (Δt i,β i h)‖≤ b*(g i.1)^(p+1):= by
 obtain ⟨C,hC,Ha⟩:=boarded F J Z ht Hκ x u p (hG:=hG); obtain ⟨D,hD,Hu⟩:= board_expands F J Z M ν H ht Hκ x u p; refine
   ⟨C+D, by positivity,?_⟩; filter_upwards [Ha,Hu,exact_measure F J Z M ν H p t x u hh] with i h₁ h₂ E
 rw [E,sub_sub_sub_comm]; exact (norm_sub_le ..).trans ((add_le_add h₁ h₂).trans_eq (add_mul ..).symm)
end YM.Integration.GradedFar.Tariff.Billboard
