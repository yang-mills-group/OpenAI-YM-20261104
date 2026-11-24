import YM.GradedFar.StampDuty
import YM.GradedFar.Minor
import YM.GradedFar.Intercept
/-!
# The actual formal trial with H and K on all its input slots

Probe ratios `[1/2,2]` both directions. Test arguments in cap h, no restriction on arity.
This supplies all point prices/coefficient identities; no quantitative calibration hypotheses.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Tariff.Billboard
open Function Filter Set PowerSeries
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 FVA2.Scale FVA2.Scale.Facets FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Book MS.Book.Program MS.Book.Convolve MS.Fleet MS.Menus
open YM.Integration.GradedFar.Neighbor YM.Integration.GradedFar.Tariff.Playbill FVA2.GradedFar.Cart
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}(Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    (ν:ℝ){hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true)
local notation "Post" => Scale.Measure.outlook (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
local notation "KΛ" => GroupS.gaugeN (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z) M ν
local notation "KΣ" => conversion (GroupS.gaugeN (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z) M ν)
local notation "Θ" => GroupS.ψ (WilsonPrescription.criterion Z) M ν
local notation "γ" => fun (T:ℝ)=> -Real.log T
variable {p q n h:ℕ}
local notation "V"=> Sec G h

abbrev Joggle := ↥(Icc (1/2:ℝ) 2)
abbrev Route:= ℝ× Joggle
abbrev clock : Filter Route:= trail ×ˢ ⊤
abbrev stretch (p:Route):ℝ:= p.2.val
abbrev next (p:Route):=p.1*stretch p
lemma everywhere {X:Route→Prop}: (∀ᶠ p in clock,X p) ↔ ∀ᶠ r in trail,∀ v:Joggle,X (r,v):=by
 rw [Filter.Eventually, Filter.mem_prod_top]; rfl
lemma running : Tendsto Prod.fst clock trail:= tendsto_fst
lemma stretch_pos (u:Joggle) : 0 < u.val:= lt_of_lt_of_le (by norm_num) u.property.1
lemma nextPath : Tendsto next clock trail:=by
 have h : ∀ᶠ p in clock,0 < next p := (running.eventually (self_mem_nhdsWithin (s:=Ioi 0))).mono (fun p hp=>mul_pos hp (stretch_pos _))
 apply tendsto_nhdsWithin_iff.mpr; refine ⟨squeeze_zero' (h.mono (fun _ h=>h.le)) (g:=fun p=> p.1*(2:ℝ)) ?_ ?_, h⟩
 · filter_upwards [running.eventually (self_mem_nhdsWithin (s:=Ioi 0))] with p h; exact mul_le_mul_of_nonneg_left p.2.property.2 (by exact h.le)
 simpa only [zero_mul] using (running.mono_right nhdsWithin_le_nhds).mul_const 2

local notation "τB"=> fun (T:ℝ)=> Θ (γ T)
def gateColumn (T:ℝ)(v:V)(a:Toon G h):PowerSeries ℂ:= PowerSeries.mk fun i=> coord a (coeff i (KΣ (γ T) h) v)
def votes (T:ℝ)(u:ListInput G n h)(a:Picks G (Ceiling n h)):=∏ i, gateColumn Z M ν T (u i) (a i)
private lemma recruitP (x:Stage n){t:ℝ}(he:0<t) : Facets.posing (γ t) x=⟨t•x.val,Work.A05.smul_conf he x.property⟩:= by apply Subtype.ext; simp [Facets.posing,Real.exp_log he]
include H
theorem travel_bill (x:Stage n)(u:ListInput G n h){T:ℝ}(ht:0<T):
    (sent Post h x.val u).subst (τB T)=∑ i: Picks G (Ceiling n h), votes Z M ν T u i * sent Post h (T•x.val) (basisWord i):=by
 let ψ:=τB T; let B:=KΛ (γ T) h
 let c:=Facets.posing (γ T) x; have hc:= (H.dilation ν).check
 have hP: actMark B (scaling (γ T) (Post h))=couple ψ (Post h):= hc.reads (γ T) h
 have hu(v:Stage n)(p:ListInput G n h): sent Post h v.val p= Reg.Point.story (Post h n v) p:=by ext k; rw [cashed Post p v.property,Reg.Point.story,coeff_mk]
 rw [hu x u, ← Reg.Point.moves (Post h n x) u (hc.led (γ T)).start]
 apply PowerSeries.ext; intro k; change coeff k (Reg.Point.story (couple ψ (Post h) n x) u)=_; rw [← hP]
 rw [Reg.Point.story,coeff_mk, actMark,seen,map_sum]; simp_rw [votes,Constants.admits,gateColumn,coeff_mk,
   cashed Post _ (Work.A05.smul_conf ht x.property)]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _
 rw [scale_at,recruitP x ht]; let p i:= coeff (j (some i)) (KΣ (γ T) h) (u i)
 have hp: Level.Dial h (γ T) ∘ pulseU j B u = p:= funext fun i=> (coeff_conversion ..).symm
 rw [hp]; exact basis_sum ( Post h n _ _ ) (d:=Ceiling n h) p
-- weather: bounded η over compact interval in these costs. demand for α columns all orders.
omit H in
lemma logHat : Charge (fun _=>0) (fun j:Joggle=>(γ j.val:ℂ)):=by
 letI : CompactSpace Joggle:= isCompact_iff_compactSpace.mp isCompact_Icc
 have hc:Continuous (fun j:Joggle=> (γ j.val:ℂ)):= Complex.continuous_ofReal.comp (continuous_subtype_val.log (fun i=>(stretch_pos i).ne')).neg
 obtain ⟨C,h⟩:= isCompact_univ.exists_bound_of_continuousOn hc.continuousOn; exact Charge.cap ⟨C, fun i=> h i (mem_univ i)⟩
lemma gatesPaid (v:V)(a:Toon G h): Feasible (fun i:Joggle=> ofPS (gateColumn Z M ν i.val v a)) (fun _=>0):=by
 intro k; -- coord(a) Dial_T
 have he: Charge (fun _=>0) (fun i:Joggle=> coord a (coeff k (KΛ (γ i.val) h) v)):=
    Neighbor.feasible_cash _ ((H.dilation ν).check.proper h k v (coord a)) logHat
 simp_rw [ofPS,gateColumn,coeff_mk,coeff_conversion,← columns_coord,dial_coord,Extent.token,neg_neg,
   fun i:Joggle=>Real.exp_log (stretch_pos i)]; refine (Charge.pow (Charge.cap ⟨2,?_⟩) a.size).mul he
 exact fun i=>by rw [Complex.norm_real, Real.norm_of_nonneg (stretch_pos i).le]; exact i.property.2
end YM.Integration.GradedFar.Tariff.Billboard
