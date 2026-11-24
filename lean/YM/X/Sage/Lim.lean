import YM.X.Sage.View
/-! # combine.D Θ through horizon. point Observer output through ownership at every n (≥6). -/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Sage
open Lattice Wilson Next.Rank Normal LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Filter Function Reed Ocean Hinge Haze Fielding Print Tri Plate Gravity Chir Fund Imprint
open Stems hiding X
open MvPolynomial Set Labels Pert.Position Pert.RawLabels
open scoped Topology BigOperators Classical
variable {G:Gauge} {d k:ℕ} {V I:Type*} {q:ℕ+} {r R:ℝ}
local notation "Φ"=>Foam G
local notation "K"=> fades ℂ
local notation "τ"=> (atTop:Filter ℕ)
variable (Z X Y:Fielding.Walk)(χ:Floor R)(h:Geom q r Z X Y)(hr:R<r)(hq:1<q.val)
variable {B:Labels.Frames G}(S:Bare.Shop B) (H:6≤d)
set_option quotPrecheck false
local notation "ι"=> ((by decide:4≤6) |>.trans H)
abbrev deity (B:Frames G)(hk:6≤d):= enroll B d (BW G hk)
abbrev dean (B:Frames G)(hk:4≤d):= enroll B d (UW G hk)
abbrev talent (B:Frames G)(H:6≤d):Fin 3→Pert.Position.E B d:= ![deity B H,dean B ((by decide:4≤6).trans H),dean B ((by decide:4≤6).trans H)]
def tollT (G:Gauge)(q:ℕ+)(Z X Y: Fielding.Walk)(k:ℕ):ℂ:= ↑(4*Sage.count G * trion (epsilon q k) (transit q X k) (transit q Y k) (transit q Z k))
local notation "Ξx"=> Tot.gather q X Y Z
local notation "Ξz"=> Tot.gather q Z X Y
local notation "Ξy"=> Tot.gather q Y Z X
local notation "ξ"=> talent B H
local notation "Xν"=>Geom.head Z X Y -- Σ notation token
local notation "Vθ"=>BMark q G
local notation "U"=>Umark q G
local notation "b"=>βDeck q G
local notation "u"=> μDeck q G
include h hr hq χ
lemma gridY_b : CostF (Ξz (βLift q G) u u + Ξx (μLift q G) u b + Ξy (μLift q G) b u - levy q Z X Y b u u (tollV₁ q G)) (tollT G q Z X Y):= by
   rw [show levy q Z X Y b u u (tollV₁ q G)=Settlement Z X Y Vθ U U + Settlement X Y Z U U Vθ + Settlement Y Z X U Vθ U from inlet Vθ U U Z X Y];
   let L:=Settlement Z X Y Vθ U U; let S':=ripple Z X Y u u Vθ; let T:=Settlement X Y Z U U Vθ; let T':=Settlement Y Z X U Vθ U;
   have hv: CostF (Ξx (μLift q G) u b) T:= by
       have hY:= matched U Vθ X Y Z χ (h.circles q ..) hr hq U; refine CostF.trans ?_ (CostF.sym hY); change CostF _ (ripple X Y Z u b U); rw [ripple_swap,gather_swap]; exact μ_exit X Z Y ((h.circles q ..).swap q ..) (χ.positive.trans hr) hq -- order μ_exit
   have hy: CostF (Ξy (μLift q G) b u) T':= by
       have he: Geom q r Y Z X:= (h.circles q ..).circles q ..; exact (μ_exit Y Z X he (χ.positive.trans hr) hq).trans (CostF.sym (matched Vθ U Y Z X χ he hr hq U))
   rw [β_exit]; rw [show tollT G q Z X Y = S'+T+T'-(L+T+T') from ?_]; exact (CostF.sub (CostF.add (CostF.add CostF.reflexive hv) hy) CostF.reflexive);
   ext1 i; change _=S' i+T i+T' i -(L i+T i+T' i); rw [show tollT G q Z X Y i=_ from (assay (q:=q) (k:=i) Z X Y).symm]; unfold S' L; abel
omit h hr hq χ in
lemma deity_c (B:Frames G)(h:6 ≤ d): physicalLabel B d (deity B h)=BW G h:= keeper_dial h standing wc B -- errone include
omit h hr hq χ in
lemma dean_c (B:Frames G)(h:4 ≤ d): physicalLabel B d (dean B h)=UW G h:= keeper_dial h standing₀ vc B
local notation "M₀"=> pV S q d ξ
local notation "M₁"=> pV₁ S q χ d ξ
set_option maxHeartbeats 330000 in
lemma rectified : CostF (displayY q χ Xν M₀ M₁ (EngineP q G)) (tollT G q Z X Y):= by
    unfold displayY;
    have h₀ := deity_c B H; have h₁:=dean_c B ι; simp only [Tot.Φ,Geom.head,pV,pV₁,handV,talent,Function.comp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,h₀,h₁]; refine (CostF.trans (CostF.sub (CostF.add (CostF.add ?w ?j) ?f) ?l) (gridY_b Z X Y χ h hr hq));
    case w=> exact ward_cut Z X Y χ h hr hq S H
    case j=> rw [gather_swap q X Y Z,gather_swap q X Y Z]; exact unit_cut X Z Y χ ((h.circles q ..).swap q ..) hr hq S H
    case f=> exact unit_cut Y Z X χ ((h.circles q ..).circles q ..) hr hq S H
    case l=> exact expense Z X Y χ h hr hq S H
-- probe observation. postage
lemma current (a:Size.Beam q): CostF (fun i=> probeX q S (Pulse.away (k:=i) (q:=q) S χ d) i (postal Xν (a i) i) ξ) (tollT G q Z X Y):= by
     apply CostF.trans ?_ (rectified Z X Y χ h hr hq S H); apply (show ∀ {f:ℕ→ℂ}, Tendsto f τ (𝓝 0) → f∈ fades ℂ from fun h=>h); refine (show Tendsto (fun i:ℕ=> (0:ℂ)) τ (𝓝 0) from tendsto_const_nhds).congr' ((mask_global q χ hq).mono (fun i hi=>?_)); exact (sub_eq_zero.mpr (shows S q χ Xν (a i) ξ hi)).symm
end YM.PositionX.Sage
