import YM.RG01Estimate.Iris
/-!
 # Mask attachment with exact gas at the compensated scalar.

   On main torus. Preserves candidate label supports exactly (doesn't yet
   claim that branch/readjustment after this operation can be ignored).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Abacus
open Function Filter Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Window Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Shoot Precision SectorMeasure Oriented Reserves
open PhysicalNext PhysicalNext.Repeat Height Beam Brim Match Song
open Next.Scheduling AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Meadow Marlin Trio Slide
open Geo Footprint Animals Progress.DirectedRecipe Payments Ovens Ovens.Pipes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge}{c:Side}{A:Listing G c}{w r:ℕ} (B:BudgetPoint)
    (F : Collection.Source G c) {P U V: ℕ→ Config G c→ℝ} (p:Rack A r U)
    {Y : Stars→ Side} (a : ∀ i:Stars,Trio.Offer G (Y i)) (Q:∀ i:Stars,(Y i).val=2*(w+i.val))
    (k z:ℕ) (x:Site c) (W:Config G c)

local notation "g₀" => p.gap B a Q z
local notation "g" => (Trio.ornament Q a)
local notation "T" => (revise F (P+V))
variable (hM: Trio.Mirrors p.polygon) (hX : Trio.CompatibleP B r p.polygon a)
    {sf q v t m τ α β η:ℝ}
      (hF: F.logRead=P+V+U) (hp: Meadow.Budget B A.reg P q) (hv: Meadow.Budget B A.reg V v)
      (hU: Meadow.Budget B A.reg U sf) (he: ∀ i j,B.Regular univ (a i j)) (hr : 0<r)
      (hw: 2*r≤w)(hz:w+4≤z)(hk:2*z≤k)(hc:4*r+16≤c.val)
      (hm : (A.read (revise F (P+V))).ForcedFamily B) (hΩ : ∀ s b,Nonempty ((A.read (revise F (P+V))).Moves s b))
      (hδ : ∀ i : Site c, (coverNumber B.B (neighbors k i) : ℝ) ≤ η)
      {f : Stars → ℝ} (hΨ : ∀ i (W:Config G (Y i)),flags B.threshold W=∅ → ∀ j, ‖a i j W‖ ≤ f i)
      {d κ Z : ℝ} {q' : ℕ→ℝ}
      (hC : Payments.Rates B.B Z d t κ)(hL: ∀ i,0≤ q' i ∧ ∀ W, ‖F.hardRead i W‖≤ q' i)
      (hK : Ac.Hit (fun i=> (A.hard i).support) B.B q' (B.supportExponent+1+1) d)
      (hV : Marlin.tithe k (Rack.beans (c:=Y) r sf f) B η ≤ t)
local notation "A₀" => (Marlin.lodge A z k)
local notation "B₀" => (Marlin.bison (T) g g₀)
include hX he hr hw hz hk hc hm hΩ hΨ hδ hC hL hK hV hU
lemma claims : Ingredients (A₀) (Marlin.dummy B₀) (raiser B) 0 Z :=
     Marlin.stakes B A z k (T) _ _ hm hΩ hC hL hK (fun i=> p.gap_tidy B a Q k z i hU hk hz he (by omega))
       (fun i w h=> p.gap_fails B a Q k z i w hk hz hr hw hc hX h) (fun i W=> p.priced_all B a Q z i W hU hz hΨ) hδ hV

local notation "D" => (poursP B A₀ B₀)
local notation "N" => (pluck B A₀)

-- rebase P, V and G onto post packs. P, V entries need not be disjoint
-- (ρ projection), but raw budgets paid on V AND P (not just on differences).
variable (P V) in
def tariff (u:ℕ) (i:ℕ→ Config G c→ℝ) (g':Trio.Offer G c): Config G c→ℝ:= Sum.elim i (choir g') (Marlin.leanU c u)
-- 
local notation "u" => p -- notation
local notation "Ip" => (fun i:ℕ => tariff i P 0)
local notation "J" => (fun i:ℕ => tariff i V g)

include hF hM hp hv
lemma bars {C: PathData G}{c' : Clip} (hZ : ∀ s b, Nonempty ((A.read F).Moves s b))
    (hP : ∀ s b, Nonempty ((A.read (revise F P)).Moves s b))(h₁ : ∀ s b, Nonempty ((A.read (revise F V)).Moves s b))
    (hΛ : Meadow.Budget B (leap z) (g: Trio.Offer G c) m) :
        (∀ W:Config G c, earlyValue A C c' B F β τ α W=earlyValue (N) C c' B (D) β
           (τ-p.polygon 0 1) α W) ∧
        (D).logRead= Ip+J ∧
        Collection.Local (N) B (revise (D) Ip) q Z ∧
        Collection.Local (N) B (revise (D) J) (v+turnFee B*m) Z ∧
        Collection.Local (N) B (D) (q+(v+turnFee B*m)) Z := by
   have hx := claims (P:=P) (V:=V) B F p a Q k z hX hU he hr hw hz hk hc hm hΩ hδ hΨ hC hL hK hV -- order
   have hp' := pay_bundle B hp hv
   refine ⟨fun W=> Marlin.carries B A z k T _ _ W F (R:=A) (fun _=>⟨rfl,rfl⟩) C c' β τ α _ hx hp' (fun i=> p.toll B F a Q z i hF hU hp hv hM) hZ hΩ, ?_, ?_, ?_,?_⟩
   · funext i Y'
     change Sum.elim (P+V) (Song.choir g) (Marlin.leanU c i) Y'= Sum.elim P (Song.choir (0:Trio.Offer G c)) (Marlin.leanU c i) Y'+ Sum.elim V (Song.choir g) (Marlin.leanU c i) Y'; rcases Marlin.leanU c i with i|i; rfl
     simp [Song.choir]
   · let K:= bison (revise F P) (0:Trio.Offer G c) g₀
     have he:= Marlin.sous (d:=K) hx (Marlin.reg_bison A z k (revise F P) _ _ hp (pay_zero (G:=G) B _))
           (fun s b=> Marlin.reeds A z k (revise F P) _ g₀ s b (hP s b|>.some))
     rw [mul_zero,add_zero] at he; exact he
   · let K:= bison (revise F V) g g₀
     exact Marlin.sous (d:=K) hx (Marlin.reg_bison A z k (revise F V) _ _ hv hΛ)
           (fun s b=> Marlin.reeds A z k (revise F V) _ g₀ s b (h₁ s b|>.some))
   let K:= B₀; have he:=Marlin.sous (d:=K) hx (Marlin.reg_bison A z k T _ _ hp' hΛ)
           (fun s b=> Marlin.reeds A z k T _ g₀ s b (hΩ s b|>.some))
   rwa [add_assoc] at he

end YM.RG01Estimate.Abacus
