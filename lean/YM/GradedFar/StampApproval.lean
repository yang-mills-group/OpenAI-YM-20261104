import YM.GradedFar.Ports
import YM.GradedFar.Journal
/-!
# Preinverse measurements of RoundMeter authenticated budgets

R budget and genuine M.3 first THEN prices at meshes
for that Λ criterion. Receding geometry, M.3 authenticated pulse for `m_N`
constant-reference version of actual (uncropped) cutoff moment. Can compare at unrounded points to both S-none and predictions. Packet
cost uses (already shown) continuum comparison, no estimation of m_N derivatives. This
budget is a consequence of earlier results, not requisite for inverse.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Auth
open Function Filter Set PowerSeries Metric
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits Lattice FullVolume
open XSpace XSpace.Normalize XSpace.Structure1 FVA2 FVA2.Scale FVA2.Scale.Facets FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Fleet Neighbor Tariff Tariff.Playbill Tariff.Crosser Tariff.Billboard Tariff.Sunshine Batch
open Fork (Sold Safe)
open scoped Topology BigOperators Classical ContDiff
local instance {n:ℕ} : ContinuousSMul ℝ (Points n):= IsBoundedSMul.continuousSMul
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
   (R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (J P:ℝ→tower S) (Z:WilsonPrescription G) (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
   {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true) (ν:ℝ)
    {t:ℝ→ℝ}(Ht:Pose F J Z t)(hF:Prepared F J P Z t)(Hq:LogTrace F R.port)
variable {n m h l p k :ℕ}{K:Set (Points n)}{N:Set (Points m)} {U B a η:ℝ}
local notation "g∴"=> strength G
local notation "Γx"=> Scale.Measure.outlook Z.scheme Z.criterion
local notation "X♯"=> GroupS.gaugeN Z.scheme Z.criterion M ν
local notation "S•"=> moving G U B
local notation "Y₁"=> atLength F P
local notation "D₁"=> atCenter F P h
variable (hU:0<U)(hB:0<B)(hK:IsCompact K)(hx:K⊆conf n)(hN:IsCompact N)(hz:N ⊆ Outside m)
    (hQ:FullVolume.FixedBounds C)(hp:ClusterFrames C)(hC:C.Makes)
variable {d:Fin n→ℕ}{e:Fin m→ℕ}(hd:AppointedH140Through l d)(he:AppointedH140Through l e)(hh:h≤l)
private lemma row_dist (a b c: Sec G h→ₗ[ℂ]ℂ) : rowPrice (a-c)≤ rowPrice (a-b)+rowPrice (b-c):= by
 have ht(u v : Sec G h →ₗ[ℂ]ℂ) : rowPrice (u+v)≤rowPrice u+rowPrice v:= by
    unfold rowPrice; rw [show row (u+v)=row u+row v from (by ext1 x; rfl)]; exact norm_add_le ..
 exact le_trans (le_of_eq (congrArg rowPrice (sub_add_sub_cancel a b c).symm)) (ht _ _)
private def panelCost (Y X:ℂ)(v w:Sec G h →ₗ[ℂ]ℂ) (c d:Sec G h) : ℝ:=
    ‖Y-X‖+rowPrice (v-w)+‖Y-X-(v-w) d‖+‖Y-v c‖+‖Y-v d‖
private lemma freesia {b d:ℝ} {c' d':Sec G h}{Xf Z X:ℂ} {A Y B:Sec G h →ₗ[ℂ] ℂ} (hq:width d'≤ b)(hd:width c' ≤ b)
    (he:‖X-Xf‖ ≤ d) (hv:rowPrice (A-Y) ≤ d): panelCost X Z A B c' d' ≤ panelCost Xf Z Y B c' d'+(5+3*b)*d:=by
    have hD(p:Sec G h)(hp:width p≤ b):‖A p-Y p‖ ≤ d*b:= (row_le (A-Y) p).trans (mul_le_mul hv hp (width_nn _) ((norm_nonneg (row (A-Y))).trans hv))
    have hx(t u:ℂ) (η:ℝ)(hh:‖t-u‖≤η): ‖X-t‖≤ ‖Xf-u‖+d+η:= by
       obtain ha:= norm_add_le (Xf-u) (X-Xf); obtain hb:=norm_add_le (Xf-u+(X-Xf)) (u-t)
       rw [norm_sub_rev u t,show Xf-u+(X-Xf)+(u-t)=X-t from by ring] at hb; linarith only [ha,hb,he,hh]
    have hA : ‖X-Z-(A-B) d'‖ ≤ ‖Xf-Z-(Y-B) d'‖+d+d*b:=by
       rw [sub_sub, sub_sub]; apply hx; rw [add_sub_add_left_eq_sub,← LinearMap.sub_apply, show (A-B)-(Y-B)=A-Y from by abel]; exact hD d' hq
    unfold panelCost; obtain Hb:= (row_dist A Y B).trans (add_le_add_left hv _); obtain H':= opt X Z Xf
    linarith only [H', Hb,hA,he,hx _ _ _ (hD c' hd), hx _ _ _ (hD d' hq)]

include H Ht hF hK hx Hq hd hh ν
private lemma bounds : ∃ b:ℝ,0≤b ∧ ∀ᶠ r in trail, ∀ o x, x∈ K→∀ u:AppointedH140Inputs G d, Box u 1→
    width (packet F P R h o r x u)≤ b ∧ width (croppedVector Γx h k u x (t r)) ≤ b:= by
 obtain ⟨c,hc,Hq⟩:= Batch.comparisonOPE F R J P Z M H ν Ht hF Hq hd hh hK hx k; obtain ⟨b,hb,Hf⟩:= vector_cap (d:=d) (H.separatedOPE ν).wilson hK hx h k 1 zero_le_one
 have ht:= Ht.running; refine ⟨c+b,add_nonneg hc hb,?_⟩; filter_upwards [Hq,ht.positive,clock_budget hG ht] with r hr ht hv o x hx u hu
 specialize Hf x hx u hu _ hv.2.1; specialize hr o x hx u hu; rw [bookVector Z M H] at hr
 refine ⟨(width_sub ..).trans (add_le_add (hr.trans ?_) Hf), Hf.trans (le_add_of_nonneg_left hc)⟩
 exact mul_le_of_le_one_right hc (pow_le_one₀ ht.le ((le_abs_self _).trans hv.2.1))

open Budget
-- authenticated statement.
def Before_cut (t:ℝ→ℝ) (K:Set (Points n))(N:Set (Points m))(a U η B : ℝ)(hP p q : ℕ)(δ:ℝ): Prop:= ∃ b:ℝ,0≤b ∧
    ∀ᶠ r in trail,∀ T:ℝ,receding (g∴ r) B a U T → ∀ᶠ i in (again f).fuse,
    Awarded (C:=C) (Fin.append d e) i.1 i.2 ∧ Awarded (C:=C) (Fin.append (Output h) e) i.1 i.2 ∧
    ∀ s:Site (C.side i.1 i.2),∀ o x y z z', x∈K→ y∈N→ RoundedWell C i.1 x y r T z z' (δ*g∴ r^(q+1))→
        forest x (T•y)∈ conf (n+m) ∧ outgoing (T•y)∈conf (1+m) ∧ ∀ (u: AppointedH140Inputs G d)(v:AppointedH140Inputs G e), Box u 1→ Box v 1→
        let c:= croppedVector Γx h p u x (t r)
        let Zc:= packet F P R h o r x u
        let Y:= recite F P r (r*T) z z' s u v
        let D:= pulseRow F P h r (r*T) s z' v
        let dY:= Y-appointedH140Crop p (t r) (fullSeries Γx X♯ (-Real.log T) hd he x y u v)
        let dM:= D - croppedResponse Γx X♯ (-Real.log T) hh he y v p (t r)
        ‖dY‖+rowPrice dM+‖dY-dM c‖+‖Y-D Zc‖+‖Y-D c‖ ≤ b*g∴ r^hP*T^(-(h:ℝ)-η)
include he hU hQ hp hB hN hz hC
local notation "v'"=> BeforeInverse F P R Z M ν
local notation "Kx"=> Before_cut F R P Z M ν
variable (ha:0<a)
include ha
theorem at_cut (δ:ℝ)(hv:0≤δ)(H₀: v' t hd he hh K N a U η B k p): ∀ᶠ q in atTop,
    Kx hd he hh t K N a U η B k p q δ:= by
 obtain ⟨C',hc,H₀⟩:=H₀; obtain ⟨b,hb,Hf⟩:= bounds F R J P Z M H ν Ht hF Hq hK hx hd hh (k:=p)
 filter_upwards [ mN_price F R J P Z M H ν Ht hF Hq hU hB hK hx hN hz hQ hp hC hd he hh ha k δ hv (η:=η)] with q h
 refine ⟨C'+(5+3*b),by positivity,?_⟩; filter_upwards [H₀,h,Hf] with r hr hv h T he'
 filter_upwards [hv T he'] with i hp; refine ⟨hp.1,hp.2.1,fun s o x y z z' hx hy hP=> ?_⟩; obtain ⟨h₀,h₁,H⟩:= hr T he' x hx y hy
 refine ⟨h₀,h₁, fun u v hu hv=>?_⟩; obtain ⟨A,B'⟩:= hp.2.2 s o x y z z' hx hy hP u v hu hv; obtain ⟨D,K⟩:=h o x hx u hu
 specialize H o none u v hu hv; dsimp only; obtain he := freesia K D A B' (Z:=appointedH140Crop p (t r) (fullSeries Γx X♯ (-Real.log T) hd he x y u v)) (B:=croppedResponse Γx X♯ (-Real.log T) hh he y v p (t r))
 exact he.trans ((add_le_add_left H _).trans_eq (by ring)) -- may need unfold panel
omit hB
variable (hη:η<1)
include hη
theorem cutoff_M3 (δ:ℝ)(hv:0≤δ)(k:ℕ): ∀ᶠ B in atTop, ∀ᶠ p in atTop, ∀ᶠ q in atTop,Kx hd he hh t K N a U η B k p q δ:=
  ((Batch.M3 F R J P Z M H ν Ht hF Hq hd he hh hK hx hN hz hU ha hη k).and (eventually_gt_atTop 0)).mono fun _ H'=> H'.1.mono fun _ hp'=>at_cut F R J P Z M H ν Ht hF Hq hU H'.2 hK hx hN hz hQ hp hC hd he hh ha δ hv hp'
end YM.Integration.GradedFar.Auth
