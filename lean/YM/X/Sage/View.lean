import YM.X.Sage.Ferry
/-!
# Combine proficiency at probe.Body.Meta. Stances identities unrotated.Nonterminal data cancelled against D.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Sage
open Lattice Wilson Next.Rank Normal LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Filter Function Reed Ocean Hinge Haze Fielding Print Tri Plate Gravity Chir Fund Imprint
open Stems hiding X
open MvPolynomial Set
open scoped Topology BigOperators Classical
variable {G:Gauge} {d k:ℕ}{V I:Type*} {q:ℕ+}{r R:ℝ}
local notation "Φ"=>Foam G
local notation "K"=> fades ℂ
local notation "τ"=> (atTop:Filter ℕ)
variable (A A' B B' C C' D E:Foam G)
variable (Z X Y:Fielding.Walk)(χ:Floor R)(h:Geom q r Z X Y)(hr:R<r)(hq:1<q.val)
local notation "Ξ"=> Tot.gather q Z X Y
local notation "Θ"=> Reed.Horizontal G
include h hr χ hq
lemma drop_frame (hx:Apt q r A)(hy:B'∈Ready q Θ)(hh:C∈Ready q Θ)(ht:C'∈Ready q Θ)(hB:B-B'∈Ash q Θ)(hC:C-C'∈Ash q Θ)
    (hp:A-A'= D+E)(he:D ∈ Ash q (⊤:Submodule ℝ (Fan G)))(hf:Ξ E B' C'∈K):
    CostF (Ξ A B C) (Ξ A' B' C') := by
       refine (replace_fields q Z X Y h (χ.positive.trans hr) hq hx hB hC hy hh).trans ?_; rw [CostF,← gather_sub,hp,gather_add]; exact Submodule.add_mem _ (get_ash q Z X Y D B' C' h (χ.positive.trans hr) hq he hy ht) hf
variable {B:Labels.Frames G}(S:Bare.Shop B) -- local B shadow
-- rational label thru horizon d
abbrev BW (G:Gauge)(h:6≤d): Labels.Label G d:= crease h (standing (G:=G)) wc
abbrev UW (G:Gauge)(h:4≤d): Labels.Label G d:= crease h (standing₀ (G:=G)) vc
local notation "Rℓ"=> Ready q Θ
variable (H:6≤d)
omit h hr χ
lemma feelB : stance S q d (BW G H)-βDeck q G∈ Ash q Θ:= earn₀ S hq H wc standing (by norm_num)
lemma feelU (hu:4≤d): stance S q d (UW G hu)-μDeck q G∈ Ash q Θ:= earn₀ S hq hu vc standing₀ (by norm_num)
include χ
lemma rootU (hu:4≤d): liftCut 3 (highs q χ S d (UW G hu))-μLift q G∈Ash q (⊤:Submodule ℝ (Fan G)):= earn₁ S χ hq hu vc standing₀ (by norm_num)
lemma rootB : liftCut 4 (highs q χ S d (BW G H))-βLift q G∈Ash q (⊤:Submodule ℝ (Fan G)):= earn₁ S χ hq H wc standing (by norm_num)
-- residue.Health
include h hr
set_option quotPrecheck false
local notation "ι"=> ((by omega:4≤6) |>.trans H)
local notation "T"=> stance S q d
local notation "P"=> μDeck q G
local notation "M"=> βDeck q G
local notation "Vθ"=> highs q χ S d
lemma ward_cut : CostF (Ξ (Vθ (BW G H)) (T (UW G ι)) (T (UW G ι))) (Ξ (βLift q G) P P):= by
      let B:=Vθ (BW G H); let C:= liftCut 4 B; have hb := high_apt S χ (BW G H) hr hq; have he:=rootB χ hq S H; let B':=βLift q G; let u:=feelU (q:=q) hq S ι; have hx: R<r:= hr;
      refine drop_frame (q:=q) _ _ _ _ _ _ (C-B') (B-C) Z X Y χ h hr hq hb (single_ready degreeU) (stan_h S hq _) (single_ready degreeU) u u (by change B-B'= _; ring) he ?_; apply arrest Z X Y χ h hr hq (?_) (upperCost (d:=3) (fun i=> stiff S χ _ (creased H standing wc) i) );
      refine apt_sub hb (ill_top q ?_ hq (χ.positive.trans hr)); change C∈_; refine (sub_add_cancel C B') ▸ Submodule.add_mem _ (ash_ready hq he) (single_ready b_stride) -- check params
lemma unit_cut : CostF (Ξ (Vθ (UW G ι)) (T (BW G H)) (T (UW G ι))) (Ξ (μLift q G) M P):= by
      let B:=Vθ (UW G ι); let C:= liftCut 3 B; have hb:= high_apt S χ (UW G ι) hr hq; have he:=rootU χ hq S ι; let B':=μLift q G;
      refine drop_frame _ _ _ _ _ _ (C-B') (B-C) Z X Y χ h hr hq hb (single_ready degreeB) (stan_h S hq _) (single_ready degreeU) (feelB hq _ _) (feelU hq _ _) (by change B-B'= _; ring) he ?_;
      rw [gather_s, bedrock X Z Y ?_]; exact Submodule.zero_mem _; exact upperCost (d:=2) (fun i=> stiff S χ _ (creased ι standing₀ vc) i)
lemma expense : CostF (priceF q χ Z X Y (T (BW G H)) (T (UW G ι)) (T (UW G ι)) (EngineP q G)) (levy q Z X Y M P P (tollV₁ q G)):= CostF.trans (replace_bill q χ Z X Y h hq hr (feelU hq _ _) (feelU hq _ _) (feelB hq _ _) (stan_h S hq _) (stan_h S hq _) (single_ready degreeB) (single_ready degreeU)) (levy_n Z X Y χ h hr hq)
end YM.PositionX.Sage
