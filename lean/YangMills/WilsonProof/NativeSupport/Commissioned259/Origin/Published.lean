import YangMills.WilsonProof.NativeSupport.Commissioned259.Origin.Panel
/-! # Compute the pass to original perturbative OPE in the genuine theory.

Point detectors, same x and exactly the Y and D tested at the actual RootG exterior
with all rows and replacements -- not upgraded exponents for a neighbouring call.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Original
open Function Filter Set MeasureTheory Asymptotics Lattice Wilson RG Source Extraction Table Spec
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Climb Maxwell XSpace XSpace.Normalize XSpace.Structure1 OPE OPE.Orbits PhysMS
open FVA2.Scale Comparing O.Score O.Enh Dframe ScaleCost Matrix Flash259HorizonFork
open scoped Topology BigOperators Classical Matrix
local notation "late" => 𝓝[>] (0:ℝ)
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Z : ℝ→PhysMS.tower S) (Q:Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    {N : WilsonPrescription G} {ν : ℝ}
    {O : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {sim : G.Simple}
    {σ : MS.Land.Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N sim O σ dial)
    {t : ℝ→ℝ} (hZ : Leading F Z) (hq : ∀ d, FieldQuote G (GroupS.gaugeN N.scheme N.criterion O ν) t (via Z) d 1)
    (hQ:LogTrace F Q.port)

open FVA2.O.Read
variable {n d h z:ℕ}
    (θ : Calibrated G t) (S0: StepCost G (GroupS.ψ N.criterion O ν) (GroupS.gaugeN N.scheme N.criterion O ν) t (via Z))
    {D:Fin n→ℕ} {a b c M δ W L:ℝ} {K:Set (Points n)}
    (hd:∀ i,D i≤ z)(hh:h≤z)
    (hW:1≤W)(hK:IsCompact K)(hc':K⊆conf n)
local notation "Vx" => Scale.Measure.outlook N.scheme N.criterion
local notation "Bx" => GroupS.gaugeN N.scheme N.criterion O ν
local notation "e" => fun (_:Fin 1) =>h
local notation "g" => g0 G

-- Need that the `L` purchase for M3 on RootG includes *every* one of our reflection probes.
-- Enlarge L (before b,p); always accepted.
def collects (G:Gauge)(L:ℝ)(h:ℕ) : Prop := ∀ b:Toon G h, console 1 b ∈ Balls L G (fun (_:Fin 1)=>h)
lemma sufficiently : ∀ᶠ L:ℝ in atTop,collects G L h := (eventually_all.mpr (fun i=>eventually_all.mpr fun j=>eventually_all.mpr fun k=> eventually_ge_atTop (‖coord k (console 1 i j)‖)))

variable {I:Type}{l:Filter I}{r T:I→ℝ}(hr:Tendsto r l late)
    (hT:∀ᶠ i in l,W ≤ T i ∧ c*(g0 G (r i))^(-b) ≤ T i ∧ T i ≤ a*(g0 G (r i))^(-b))
    (hb:0<b) (hL:0≤L) (ht:collects G L h)
local notation "Here" => Set.singleton RootG
local notation "Ent" => measures F Z e e
local notation "D₀" p:max o:max r:max T:max i:max => instrument F Z h p o r T i
local notation "Y" p:max r:max T:max x:max u:max i:max => total F Z D e p r T x RootG u (console 1 i)
local notation "Yp" q:max i:max r:max T:max x:max u:max => crop q (t r) (measurement Vx Bx hd (fun _=>hh) x (T • RootG) (-Real.log T) u (console 1 i))
local notation "Dq" q:max i:max r:max T:max => predicted Vx Bx (fun _=>hh) hh (T • RootG) (-Real.log T) (console 1 i) q (t r)
local notation "cX" q:max r:max x:max u:max => purchased Vx u x h q (t r)
local notation "cW" o:max r:max x:max u:max => coefficients F Z Q D h o r x u
variable (o:I→Owner F) (x:I→Points n)(hx:∀ᶠ i in l,x i∈K) (u:I→Slots G D)(hu:∀ᶠ i in l,u i∈Balls L G D)
    (P q p:ℕ) (hp:q≤p)(hz:q+1 ≤ P)
    (η:ℝ)(he':0<η)
include H hQ S0 θ hZ
-- M.3 purchase on query; buys `Afford` across all b when using Marker.
include hp hz he' hd hh hW hK hc' hu hx hr hT hb hL ht

lemma stageBudget (
    X : ∃ B:ℝ,0<B ∧ ∀ᶠ r in late,∀ T ≥ W,c*g r^(-b) ≤ T → T ≤ a*g r^(-b) → ∀ x∈K, ∀ y∈({RootG}:Set (Points 1)), ∀ o:Owner F, ∀ u∈Balls L G D, ∀ v∈Balls L G e,
      checkPrice (total F Z D e o r T x y u v)
            (crop p (t r) (measurement Vx Bx hd (fun _=>hh) x (T • y) (-Real.log T) u v))
            (centerD F Z h e o r T y v) (predicted Vx Bx (fun _=>hh) hh (T • y) (-Real.log T) v p (t r))
            (coefficients F Z Q D h o r x u) (purchased Vx u x h p (t r)) ≤ B*T ^(-((h:ℝ)+η))*(g0 G r)^P) :
    let M := fun i:I => Comparing.panel (instrument F Z h (o i).1 (o i).2 (r i) (T i));
    (∀ᶠ i in l, IsUnit (M i)) ∧
      (fun i => stiffness (M i)⁻¹)=O[l] (fun i=>T i^h) ∧
      (fun i=> tallyZ (numbers ((cW (o i) (r i) (x i) (u i))-(cX p (r i) (x i) (u i)))))=O[l] (fun i=>T i ^ (-η)*(g (r i))^P) ∧
      (fun i=> tallyZ (numbers ((cW (o i) (r i) (x i) (u i))-(cX q (r i) (x i) (u i)))))=O[l] fun i=>g (r i)^(q+1) := by
  let D0 i:= instrument F Z h (o i).1 (o i).2 (r i) (T i)
  let y0 i:=cW (o i) (r i) (x i) (u i); let y1 p i:= cX p (r i) (x i) (u i)
  have hc₁: ∀ᶠ i in l,1≤ T i:= hT.mono fun i h=> hW.trans h.1
  obtain ⟨k,K'⟩:= Original.rank F Z Q H hZ hQ (fun i:I=> (o i).2) (fun i=>(o i).1) hr θ S0 (hc₁.and (hT.mono fun i h=>h.2.2)) hb h
  intro M; refine ⟨k,K',?_⟩
  let u0 i j:= Y (o i) (r i) (T i) (x i) (u i) j; let v i j:= Yp p j (r i) (T i) (x i) (u i)
  have hgt := (pace sim).comp hr; have mp := now hgt; have hv: ∀ᶠ i in l,0<T i:= hc₁.mono fun i h=> zero_lt_one.trans_le h
  have raw (j): (fun i=> checkPrice (u0 i j) (v i j) (D0 i j) (Dq p j (r i) (T i)) (y0 i) (y1 p i)) =O[l] Comparing.margin P h η ((g0 G) ∘ r) T := by
    obtain ⟨B,hB,X⟩:= X; refine IsBigO.of_bound B ?_; filter_upwards [hr.eventually X,hT,hx,hu,hv,mp] with i X Y0 xh uh h0 p0
    rw [Real.norm_of_nonneg (checkPos ..), Real.norm_of_nonneg]
    · exact (X _ Y0.1 Y0.2.1 Y0.2.2 _ xh _ (mem_singleton _) (o i) _ uh _ (ht j)).trans_eq (mul_assoc ..)
    unfold Comparing.margin; positivity
  have H' := linked D0 k (matrixPay.mp K') u0 v (fun i j=> Dq p j (r i) (T i)) y0 (y1 p) P η raw hv
  have hv b:= finish (H.separatedOPE ν).wilson hK hc' hL hx hu b p q P hp hz (a:=η) he' ((g0_zero sim).comp hr) ((transition sim θ).comp_tendsto hr) hc₁ (H' b)
  exact ⟨ IsBigO.sum (s:=Finset.univ) (fun i (_:i∈(Finset.univ:Finset (Toon G h)))=>isBigO_norm_left.mpr (H' i)), IsBigO.sum (s:= Finset.univ) (fun i _=>isBigO_norm_left.mpr (hv i))⟩
end YM.FVA2.GradedFar259.Original
