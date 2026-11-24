import YM.RGComparison01.AuxPackage
/-!
# Rank-aware probe supply for plaquette insertions

 Uses actual `draw` and Fine coordinates; unlike vacuum, no pre-decided
 committed books cover this automatically. Stage constant required after
 commissioning Before; express dependence on horizon & combined disk. Counts
 dimensions only on projected Aux.Z. -/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Sensor
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open PhysicalNext.Repeat Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open Push.AbsoluteSums Fare Sienna AuxDesk Token AuxFabric AuxConstant AuxMiles AuxWeigh AuxPackage
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MatrixOrder
variable {G : Gauge}
section pair
variable {E X Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {k : ℕ} {u v : ℝ} {f:E→X}{g:E→Y}{x:E}
lemma bride (h : Brush k u v f x) (hh:Brush k u v g x) : Brush k u v (fun y=> (f y,g y)) x:= by
   refine ⟨h.smooth.prodMk hh.smooth,h.pos,fun i hi=> ?_⟩
   unfold normJ; rw [iteratedFDeriv_prodMk h.smooth hh.smooth (by exact_mod_cast hi),ContinuousMultilinearMap.opNorm_prod]; exact max_le (h.order i hi) (hh.order i hi)
-- avoid constant times k.Reflection
-- allows different Z domain
lemma chairs2 {R:ℝ} {x:ℝ×E} {z:X}(h:‖x‖ ≤ 1)(he:‖z‖ ≤ R) : Brush k R 1 (fun y:ℝ×E => y.1 • z) x := by
   let L := (ContinuousLinearMap.fst ℝ ℝ E).smulRight z; have hL : ‖L‖ ≤ R:= ContinuousLinearMap.opNorm_le_bound _ ((norm_nonneg _).trans he) fun q=> by
      change ‖q.1 • z‖ ≤ _; rw [norm_smul, mul_comm R]; exact mul_le_mul (norm_fst_le q) he (norm_nonneg _) (norm_nonneg _)
   refine Brush.linearB L ((L.le_opNorm _).trans ?_) (by rwa [mul_one]) zero_le_one
   exact (mul_le_of_le_one_right (norm_nonneg _) h).trans hL
end pair

section pack
variable {c f:Side} {S:StepData c f} {D W r H β σ C Λ:ℝ} {k j:ℕ} (T : Tube G S) (F:Forest S.ratio) (ρ:Bid.Dir G c→AxisChart G F)
    (X:Before G σ C S.patch.J S.kernel (k+3))
local notation "P" => Positions (Uniform.Primary c G)
local notation "Y" => Poll.Body (Precision.Key F G)
local notation "Ps" => (X.tables T.high S.patch)
variable (hE : X.Service F T.high T.up ρ)

abbrev fusion (z:Y) (x:ℝ×P):= (x.2,Lapis.orbit F ρ x.2 + x.1 • z)
abbrev testF (a:Cell f) (z:Y) (x:ℝ×P):ℝ := G.price (faceValue (F.drape (Fare.draw F (represent (Uniform.tint G _ x.2)) (fusion F ρ z x).2)) a)
lemma native (a:Cell f) (z:Y)(x:ℝ×P): testF F ρ a z x = G.price (faceValue (Uniform.fine G F (combineH («G»:=G) F (fusion F ρ z x))) a):=by rfl
lemma ready (a:Cell f)(x:ℝ×P): Measurable fun z:Y=> testF F ρ a z x:=by
   suffices H:Continuous fun z:Y=> testF F ρ a z x from H.measurable
   unfold testF fusion; dsimp only; refine G.continuous_price.comp (?_) -- inner elaboration?
   exact (show Continuous (fun V:Config G f=>faceValue V a) from continuous_travel ..).comp (F.continuous_drape.comp ((Fare.draw_cont ..).comp (continuous_const.add (show Continuous (fun z:Y=> x.1 • z) from (by fun_prop)))))
variable (hq:Larger (G:=G) S) (hv:T.up.Bounds T.high σ C Λ)
-- orbit budget.K
variable (hb : (Fintype.card (Joint F G):ℝ)≤D) (hD : 1 ≤ D)
local notation "sT" => Before.Service.trailCost Ps (k+3)
include hE hq hv T X
lemma height (x:ℝ×P)(z:Y)(hx:‖x‖ < r) (hr : r ≤ (X.tables T.high S.patch).horizon) (ht:r≤1) (hh : ‖z‖≤ W)
    (he : Before.Service.trailCost Ps (k+3)*r+r*W ≤ 1) : ‖combineH («G»:=G) F (fusion F ρ z x)‖ ≤ 1:= by
   let w:= weld (Precision.Key F G); have hV := (norm_snd_le x).trans_lt hx; have hR:= hV.trans_le hr
   have hu := (hE.trail_lipschitz hv hq rfl rfl).1
   rw [show ‖combineH («G»:=G) F (fusion F ρ z x)‖=max ‖x.2‖ ‖w (fusion F ρ z x).2‖ from norm_meet x.2 (w (fusion F ρ z x).2),max_le_iff]; refine ⟨(hV.trans_le ht).le,?_⟩; unfold fusion; dsimp only; rw [map_add,map_smul]; refine le_trans ((norm_add_le ..).trans (add_le_add (show ‖w (Lapis.orbit F ρ x.2)‖ ≤ _ from ?_) ?_)) he
   · have hp:= Lapis.evacuated F T.up (Classical.arbitrary _) ρ X hq hv hE _ hR; exact hp.trans (mul_le_mul_of_nonneg_left hV.le hu.le)
   rw [norm_smul]; refine mul_le_mul ((norm_fst_le x).trans hx.le) ((w.toContinuousLinearMap.le_opNorm z).trans ?_) (norm_nonneg _) ((norm_nonneg _).trans hx.le)
   exact (mul_le_of_le_one_left (norm_nonneg _) (Lapis.climb _)).trans hh

abbrev glare (V:ChartPrices)(D:ℝ)(k:ℕ)(W:ℝ):= D * Lapis.lensT k V D+W+1
abbrev sight (G : Gauge)(k : ℕ)(Z:ℝ):= |Uniform.priceCost G (Uniform.travelCost G (k+4) 4 (Uniform.fineCost G (k+4) Z))|
-- see paint supply order k+4
abbrev tally (T₀:ChartPrices)(D W Z : ℝ) (k:ℕ)(G:Gauge):= (k.factorial:ℝ)*sight G k Z*(1+(1+ |glare T₀ D k W|)*1)^k
local notation "Ψ" => sight G k X.Z
local notation "τ" => fun w:ℝ=> tally Ps D w X.Z k G

include hb hD
lemma charm (x:ℝ×P) (a:Cell f)(z:Y)(hh:‖combineH («G»:=G) F (fusion F ρ z x)‖ ≤ 1)(hr : ‖x‖≤1) (hx:‖x.2‖ < (X.tables T.high S.patch).horizon) (he: ‖z‖≤ W) : Brush k (τ W) 1 (testF F ρ a z) x:= by
   let L':= combineH («G»:=G) F; let u(y:Positions (Joint F G)):= G.price (faceValue (Uniform.fine G F y) a)
   have hu := Uniform.Allows.price («f»:=fun y=> faceValue (Uniform.fine G F y) a) (travel_jets (U:=fun y : Positions _=> Uniform.fine G F y) (fun i=> (fine_supply F X.labels).2.2 i _ hh) (w:=square _ _) a.1 (a:=4) (by simp [Lattice.square]))
   have hp : Brush k Ψ 1 (u ∘ L') (fusion F ρ z x):=by
      have hx:Brush (k+4) (Uniform.priceCost G _) 1 u (L' _):= Brush.offer.2 ⟨hu.analytic.of_le le_top, hu.norm_le⟩
      have ht:= Brush.reading L'.toContinuousLinearMap (hx.smaller (Nat.le_add_right k 4)) (Lapis.feesComb ..)
      rw [one_mul] at ht
      exact ht.climb (le_abs_self _) le_rfl
   have hP:= Lapis.luminous F (Classical.arbitrary _) T.up T.high ρ σ C Λ X hq hv hE D hD hb x.2 (mem_ball_zero_iff.mpr hx)
   have hT : Brush k _ _ (Lapis.orbit F ρ ∘ (Prod.snd:ℝ×P→P)) x:= Brush.reading (ContinuousLinearMap.snd ℝ ℝ P) (hP.smaller (Nat.le_add_right ..)) (ContinuousLinearMap.norm_snd_le ..); rw [one_mul] at hT
   have hH:= hT.gathering (chairs2 («R»:=W) hr he)
   have he:Brush k 1 1 (Prod.snd:ℝ×P→P) x:= Brush.linearB (ContinuousLinearMap.snd ℝ ℝ P) ((norm_snd_le x).trans hr) (by rw [one_mul]; exact ContinuousLinearMap.norm_snd_le ..) zero_le_one
   have hb:= hH.nonneg
   have hv : Brush k |glare Ps D k W| 1 (fusion F ρ z) x:= bride (he.climb ((le_add_of_nonneg_left hb).trans (le_abs_self _)) le_rfl) (hH.climb ((le_add_of_nonneg_right zero_le_one).trans (le_abs_self _)) le_rfl)
   exact ((hv.pine hp).trim).shimmy (Eventually.of_forall (fun y=> native F ρ a z y))
end pack
end YM.RGComparison01.Sensor
