import YM.X.Gravity.Oak
/-!
# Aperture contour equation. Local FO ribbon harvest and CT purchase absorb. Does *not* give regulator matching yet. ∗No assumptions on ker beyond actual repaint∗. Correction bill budget at weight.; obtains ∗convergence under all released exterior directions, before coupling∗.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Gravity
open Lattice Wilson Next.Rank Normal Interval PertExtension LatticePT Filter Set Function Metric MeasureTheory Asymptotics Reed Size Braid
open MvPolynomial Hinge Clove Haze Grow Shelf Ocean Fielding Crystal Perch LiftMark Bare
open Stems hiding X
open Pert.RawLabels
open scoped Topology ContDiff BigOperators Classical
variable {q: ℕ+}(hq:1<q.val){V:Type*}{k m n d l:ℕ}{G:Gauge}{R r:ℝ}
local notation "L"=>(atTop:Filter ℕ)
local notation "Ψ"=> Book G
local notation "e"=>epsilon q
variable {F:Labels.Frames G}(s:Shop F)(P:Word G)(φ:Floor R)
local notation "D"=>P.d
local notation "E"=> Pert.Position.E F
variable {A:ℕ→Brush G}
variable {B:Rich G}
local notation "Y"=>billet (q:=q) s P φ
local notation "f"=>warp q P φ
local notation "C'"=> emerge q B
include hq
lemma tangent (hr:R<r)(ha:Tide q r A)(hp:Grasp B)(ht:Fill (gate q r) (fun i=>e i^(P.d+1)) P.d 0 A (emerge q B)):
    Tendsto (fun i=> e i ^ (-(D:ℤ)) • (snap (A i) (matchP s q i D (Y i))-shineP (C' i) D (matchSelf s D (Y i)))) L (𝓝 0):= by
   let b:=(-((D+1:ℕ):ℤ)); let H(i:ℕ):= (((snap (A i)).toLinearMap.comp (matchP s q i D))-(shineP (C' i) D).comp (matchSelf s D)); let G'(i:ℕ):= e i ^ b • H i; have hh(i:ℕ)(x: Pert.Position.E F D) : G' i x=e i^b • (snap (A i) (matchP s q i D x)-shineP (C' i) D (matchSelf s D x)):= rfl
   have he:= kills (tend_billet hq s P φ) G' (fun y=>by simp_rw [hh]; apply hush hq s φ.positive.le hr ha hp ht y); refine he.congr (fun i=> ?_); change G' i _=_; rw [map_smul, hh, RCLike.real_smul_eq_coe_smul (K:=ℂ), smul_smul]; -- orientation
   rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]; congr 1; push_cast; change (e i:ℂ) * (e i:ℂ)^b = (e i:ℂ)^(-(P.d:ℤ)); nth_rw 1 [← zpow_one (e i:ℂ)]; rw [← zpow_add₀ (by exact_mod_cast (epsilon_pos q i).ne'), show 1+b= -(P.d:ℤ) by omega]
omit hq in
def mature (q:ℕ+)(S:Shop F)(P:Word G)(φ: Floor R)(i:ℕ): Curly G := (epsilon q i)^(-(P.d:ℤ)) • (warp q P φ i-matchP S q i P.d (billet (q:=q) S P φ i)) -- Deck-scalar
lemma ripe (hr:R<r)(ha:Tide q r A): Released (fun i=> snap (A i) (mature q s P φ i)):= by
   obtain ⟨B,hp,h⟩:= Grasp_cover (d:=P.d) hq (φ.positive.trans hr) ha; let x:= (emerge q B); let V(i):=probeL (x i); let W(i):=e i ^ (-(P.d:ℤ));
   have hh := test_early hq P φ hp; have ht:= tangent hq s P φ hr ha hp h; refine Eq.mp (congr_arg Released ?_) (((shadow_drift (q:=q) hq φ P hr ha hp h).add hh).sub ⟨0,ht⟩)
   funext i; simp only [Pi.add_apply,Pi.sub_apply]; change W i • (snap _ (f i) - V i (bloom D _))+ W i • V i (exposed q P φ i-watch G D _) - W i • (snap _ _- V i (bloom D _))= _; rw [matchS,sold,map_sub,mature,show snap (A i) (e i^(-(D:ℤ)) • _) = e i^(-(D:ℤ)) • snap (A i) (warp q P φ i-matchP s q i D (billet (q:=q) s P φ i)) from map_smul ((snap (A i)).toLinearMap.restrictScalars ℝ) ..,map_sub, smul_sub, smul_sub, smul_sub, smul_sub]; unfold W exposed; abel
end YM.PositionX.Gravity
