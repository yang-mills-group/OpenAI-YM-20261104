import YM.GradedFar.Axil
import YM.GradedFar.Vase
import YM.GradedFar.Era
/-!
# Relative frame estimate even at negative log-scale stretch from dossier on upward ones

The home-path cocycle of this calendar gives the bounded inverse price before all orders. This
route bootstrap doesn't appeal to the stronger `G1Wide` grants. Exhibit the precise norm
convention for this argument.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Tariff.Billboard
open Function Filter Set PowerSeries
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 FVA2.Scale FVA2.Scale.Facets FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Fleet
open YM.Integration.GradedFar.Neighbor YM.Integration.GradedFar.Tariff.Playbill
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)(J P:ℝ→tower S)
   (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
   {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true)
local notation "Post" => Scale.Measure.outlook (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
local notation "Before"=> Scale.Measure.start (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
variable {n:ℕ} (h:ℕ)

def increasing : Set Route := {p | 1 ≤ stretch p}
def upGauge := clock ⊓ Filter.principal increasing
def downGauge := clock ⊓ Filter.principal increasingᶜ
lemma routes {Q:Type*}{u:Route→Q}{l:Filter Q}(hq:Tendsto u upGauge l)(hv:Tendsto u downGauge l): Tendsto u clock l := by
    refine tendsto_def.mpr fun P hp=> ?_; have ht: ∀ᶠ r in clock,r∈increasing→u r∈P:= eventually_inf_principal.mp (tendsto_def.mp hq P hp);
    have hw:∀ᶠ r in clock,r∉increasing→u r∈P:= eventually_inf_principal.mp (tendsto_def.mp hv P hp)
    exact (ht.and hw).mono fun i hi=>by by_cases h:i∈increasing; exact hi.1 h; exact hi.2 h
lemma reclaim (x:Joggle): x.val⁻¹∈Icc (1/2:ℝ) 2:=by
 obtain hp:= x.property; have hu:= stretch_pos x; constructor
 · rw [← one_div]; exact (le_div_iff₀ hu).mpr (by linarith only [hp.2]);
 rw [← one_div]; exact (div_le_iff₀ hu).mpr (by linarith only [hp.1])
def returnAt (i:Route): Route:= (next i, ⟨(stretch i)⁻¹, reclaim i.2⟩)
@[simp] lemma home (i:Route): next (returnAt i)=i.1:=by
 change i.1*stretch i*(stretch i)⁻¹ = _; rw [mul_assoc,mul_inv_cancel₀ (stretch_pos i.2).ne',mul_one]
lemma return_tend : Tendsto returnAt downGauge upGauge:= by
    have ht:= (tendsto_prod_iff'.mpr (And.intro nextPath (tendsto_top (f:=fun i=> (returnAt i).2))))
    apply tendsto_inf.mpr
    refine ⟨(show Tendsto returnAt clock clock from ?_).mono_left (show downGauge ≤ clock from inf_le_left),?_⟩
    · exact ht
    apply tendsto_principal.mpr; exact eventually_inf_principal.mpr (Eventually.of_forall (fun i hi=>
       (one_le_inv₀ (stretch_pos i.2)).mpr (le_of_not_ge hi)))

local notation "V"=>Sec G h
local notation "mark"=> Neighbor.stamp G h
local notation "Ops"=> Operation G h
local notation "D∼"=> stretching G h
local notation "γ" => fun (T:ℝ)=> -Real.log T
lemma forwards (i:Route): D∼ (γ (stretch i))*D∼ (Real.log (stretch i))=1:=by rw [stretch_mul,neg_add_cancel,Neighbor.flat]
lemma backwards (i:Route): D∼ (Real.log (stretch i))*D∼ (γ (stretch i))=1:=by rw [stretch_mul,add_neg_cancel,Neighbor.flat]
lemma undo_price (i:Route): ‖D∼ (Real.log (stretch i))‖≤ (2:ℝ)^h:= by
 obtain H:= billOne (G:=G) h (returnAt i); change ‖D∼ (-Real.log (stretch i)⁻¹)‖≤ _ at H; rwa [Real.log_inv,neg_neg] at H

def adapted (i:Route) := asset J h i * Level.Dial h (Real.log (stretch i))
lemma true_inverse (i:Route): mark (adapted J h (returnAt i))* mark (stripe J h i) = 1:=by
 unfold adapted stripe; rw [Neighbor.price,Neighbor.price]; rw [show Real.log (stretch (returnAt i))= -Real.log (stretch i) from Real.log_inv _,mul_assoc,← mul_assoc (mark (Level.Dial ..)), show mark (Level.Dial h (-Real.log (stretch i)))*mark (Level.Dial h (Real.log (stretch i)))=1 from forwards h i (G:=G),one_mul,← Neighbor.price]
 have he:asset J h (returnAt i)*asset J h i=1:=by unfold asset; rw [home]; ext1 v; exact (relative J i.1 (next i) h).symm_apply_apply v -- inspect orientation
 rw [he,stamp_one]
lemma twistJ (i:Route): mark (stripe J h i)=D∼ (Real.log (stretch i))*mark (adapted J h i)*D∼ (γ (stretch i)):=by
 unfold stripe adapted; rw [Neighbor.price, Neighbor.price]; change D∼ _ * _ = D∼ (Real.log (stretch i))*(mark (asset J h i)*D∼ (Real.log (stretch i)))*D∼ (γ (stretch i)); rw [mul_assoc,mul_assoc,backwards h i,mul_one]

abbrev Steady : Prop := Tendsto (fun i=> mark (stripe J h i)) clock (𝓝 1)
abbrev SteadyUp : Prop := Tendsto (fun i=> mark (adapted J h i)) upGauge (𝓝 1)
lemma SteadyUp.all (hv: SteadyUp J h) : Steady J h:=by
    apply routes
    · refine (twist_price hv (Eventually.of_forall (backwards h (G:=G))) (Eventually.of_forall (undo_price h (G:=G)))
        (Eventually.of_forall (billOne h (G:=G)))).congr (fun i=> (twistJ J h i).symm)
    exact switch_price (hv.comp return_tend) (Eventually.of_forall (true_inverse J h))

-- transfer from position-calibrated (W_j) through adjustment to physical H in the same solver.
local notation "jump"=> adjust_map J P
lemma cancel (_r s:ℝ) (x:V): assign J s h (jump s h x)= assign P s h x:= by
 change assign J s h ((assign J s h).symm (assign P s h x))=_; rw [LinearEquiv.apply_symm_apply]
lemma repair (i:Route): mark (asset P h i)=mark (adjust_map P J i.1 h)*mark (asset J h i)*mark (jump (next i) h):=by
 rw [← Neighbor.price,← Neighbor.price]; apply congrArg (mark)
 ext1 v; apply (assign P i.1 h).injective; change assign P i.1 h (relative P i.1 (next i) h v)=assign P i.1 h (adjust_map P J i.1 h (relative J i.1 (next i) h _))
 rw [atHome,cancel P J h 0,atHome]; exact (cancel J P h 0 (next i) v).symm
lemma transfer (i:Route) : mark (stripe P h i)=(D∼ (Real.log (stretch i))*mark (adjust_map P J i.1 h)*D∼ (γ (stretch i)))*
    mark (stripe J h i)*mark (jump (next i) h):=by
 unfold stripe; simp only [Neighbor.price]; rw [repair J P h]; change D∼ (Real.log (stretch i))*_=_* (D∼ (Real.log (stretch i))*_)*_; -- associativity
 let A:=D∼ (Real.log (stretch i)); let B:=D∼ (γ (stretch i)); let Q:=mark (adjust_map P J i.1 h); let k:= mark (asset J h i); let y:= mark (jump (next i) h)
 change A*(Q*k*y)= (A*Q*B)*(A*k)*y; simp only [mul_assoc]; rw [← mul_assoc B,forwards h i,one_mul]

variable (t:ℝ→ℝ)(ht:Coupling G t)(hw:widens J P Z h t)
include ht hw H
lemma jumpPath : Tendsto (fun i=> mark (jump i h)) trail (𝓝 1) := by
 apply plan_cpx; intro x; obtain ⟨v,rfl⟩:=(columns G h).surjective x; simp_rw [stamped]; apply tendsto_pi_nhds.mpr; intro i
 obtain hp:=(hw i v).lead (Coupling.conforms hG ht) (); have hu:coeff 0 (attends Z v i)= coord i v:=by
    rw [attends,coeff_mk,(H.details.toServed.toPosted.toQuoted.toContract.joint 0 h).2.2.scale.zero]; rfl
 rw [coeff_zero_eq_constantCoeff_apply] at hu; rw [hu] at hp; exact hp
lemma jump_inverse : Tendsto (fun i=>mark (adjust_map P J i h)) trail (𝓝 1):= by
 apply switch_price (jumpPath J P Z M H h t ht hw); apply Eventually.of_forall; intro i; rw [← Neighbor.price]; refine Eq.trans
   (congrArg (mark) (show jump i h*adjust_map P J i h=1 from ?_)) stamp_one
 ext1 x; apply (assign J i h).injective; change assign J i h (jump i h (adjust_map P J i h x))=_; rw [cancel J P h 0,cancel P J h 0]; rfl
lemma jump_steady (hs:Steady J h): Steady P h:= by
 obtain hA:= twist_price ((jump_inverse J P Z M H h t ht hw).comp running) (Eventually.of_forall (backwards h (G:=G))) (Eventually.of_forall (undo_price h (G:=G))) (Eventually.of_forall (billOne h (G:=G)))
 have hx:= (hA.mul hs).mul ((jumpPath J P Z M H h t ht hw).comp nextPath); rw [one_mul,one_mul] at hx; exact hx.congr fun i=> (transfer J P h i).symm
end YM.Integration.GradedFar.Tariff.Billboard
