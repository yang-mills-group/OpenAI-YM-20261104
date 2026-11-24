import YM.SchemeRG11.Saddle.Ghosted
import YM.SchemeRG11.Saddle.Peat
import YM.PertExtension.Normalized

/-!
# Real fixed positivity & normalized equivalence ingredients

Exact all marks; not relying on Full.pose existence.
-/
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.SchemeRG11.Sway
open scoped Classical ContDiff Topology Matrix.Norms.Frobenius
open Function Filter Lattice Pert.Orb PertExtension.Orb LocalH MeasureTheory Precision Push.Loops
open Local PertExtension.Series Radial Tested PertExtension.Chart
variable {G:Gauge}{n:Side}
lemma VF_stable : Stationary (action G n):= ⟨diff_action.of_le le_top, jets_action.1, fun i=>by
 unfold jet; rw [iteratedFDeriv_one_apply ..]; simp only [jets_action.2.1,zero_apply,mul_zero]⟩
lemma VF_heavy(x:Potential G n): Radial.jet (action G n) 2 x= form x x/2:=by
 unfold jet; rw [show (fun _ : Fin 2=>x)=![x,x] from funext fun i=>by fin_cases i <;> simp, jets_action.2.2]; norm_num [Nat.factorial]; ring
lemma VF_weight: Goal (action G n):=quadratic_min _ (fun u hu=>by rw [VF_heavy];exact half_pos (form_pos hu))
lemma fixing_at(a:Land G n): action G n a.val= wilson a.val:=by
 unfold Pert.Orb.action fixing; have h(x:Site n):takeDiv x a.val=0:= show (divL G n a.val).val x=0 from congrFun (congrArg Subtype.val a.property) x; simp only [h,norm_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,Finset.sum_const_zero,zero_div,add_zero]
lemma VL_smooth: ContDiffAt ℝ ω (fun a:Land G n=>action G n a.val) 0:=by exact ContDiffAt.comp (f:=g0 G n) 0 (by rw [map_zero]; exact diff_action) (ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=Land G n) (F:=Potential G n) (g0 G n)).contDiffAt
lemma VL_stable: Stationary (fun a: Land G n=> action G n a.val):=by
 refine ⟨VL_smooth.of_le le_top, VF_stable.base0,fun a=>?_⟩
 have h:= jetLinear (F:=Land G n) (Pert.Orb.action G n) VF_stable.smooth (g0 G n) 1 a
 exact h.trans (VF_stable.base1 a.val)
lemma VL_weight: Goal (fun a:Land G n=>action G n a.val):= by
 apply quadratic_min; intro u hu
 have h:= jetLinear (F:=Land G n) (Pert.Orb.action G n) VF_stable.smooth (g0 G n) 2 u
 change 0< Radial.jet (Pert.Orb.action G n ∘ g0 G n) 2 u; rw [h,VF_heavy]; exact half_pos (form_pos (fun he=> hu (Subtype.ext he)))

def costV (w:↥(Flow G n)):= (∑ x: Site n,‖w.val x‖^2)/4
lemma costV_smooth: ContDiffAt ℝ ∞ (costV (G:=G) (n:=n)) 0:=by
 let L(x:Site n):↥(Flow G n)→L[ℝ]G.Color:=((LinearMap.proj (R:=ℝ) x).comp (Mean G n).subtype).toContinuousLinearMap
 exact (ContDiff.sum fun i _=> ((contDiff_norm_sq ℝ).comp ((L i).contDiff))).contDiffAt.div_const _
lemma costV_sq(t:ℝ)(x:↥(Flow G n)):costV (t • x)= t^2*costV x:=by unfold costV; rw [← mul_div_assoc,Finset.mul_sum]; congr 1; refine Finset.sum_congr rfl fun i _=>?_ ; change ‖t • (x.val i)‖^2=_; rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
lemma costV_light: Goal (costV (G:=G) (n:=n)):= by
 apply quadratic_min; intro x hx; rw [jetSq costV_smooth costV_sq,if_pos rfl]; apply div_pos _ (by norm_num)
 have h: ∃ i,x.val i≠0:= by by_contra! h;exact hx (Subtype.ext (funext h))
 obtain ⟨i,hi⟩:=h; exact Finset.sum_pos' (fun j _=>sq_nonneg _) ⟨i,Finset.mem_univ _,pow_pos (norm_pos_iff.mpr hi) 2⟩
def main(G:Gauge)(n:Side)(p:Whole G n):= fiscal p.1 + costV p.2
lemma main_station :Stationary (main G n):= weaveSeed fiscal_stationary costV_smooth costV_sq
lemma main_goal (hp:Even n.val): Goal (main G n):= weaveCost fiscal_stationary costV_smooth (coercion hp) costV_light

abbrev priceAll(v: Potential G n):=Jacob v * FP v
lemma priceAll_smooth: ContDiffAt ℝ ω (priceAll (G:=G) (n:=n)) 0:= Pert.Orb.jacobian_smooth.mul FP_diff
lemma price_snap (hn:Admissible n){hp:Even n.val}(P:ChartRatio G)(R:LocalRatio P):∀ᶠ x:Whole G n in 𝓝 0,
 priceAll (graze hp x) * TraceCost hp x=(P.scale ^ Fintype.card (Cotree n))⁻¹ * jacobian P x.1:=by
 have ht: Tendsto (fun p:Whole G n=>p.1) (𝓝 0) (𝓝 0):=continuousAt_fst
 filter_upwards [graze_key hn (hp:=hp),ht.eventually (submergence R)] with x hx hp
 rw [show priceAll (graze _ x)* _= _ from hx,hp,← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ R.scale.ne'),one_mul]
lemma price_land (hn:Admissible n){hp:Even n.val}(e:Dir G n≃L[ℝ] Land G n)(he:e.toContinuousLinearMap=fderiv ℝ (steeple (G:=G) hp) 0)(P:ChartRatio G)(R:LocalRatio P):∀ᶠ A:Dir G n in 𝓝 0,
 priceAll (steeple hp A).val * cost (e.symm.toContinuousLinearMap ∘L fderiv ℝ (steeple (G:=G) hp) A)=(P.scale ^ Fintype.card (Cotree n))⁻¹ * jacobian P A:=by
 filter_upwards [steeple_key hn (hp:=hp) e he,submergence R] with A h ht
 change priceAll (steeple hp A).val*OuterCost e hp A=_
 rw [show priceAll (steeple hp A).val * _= _ from h,ht,← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ R.scale.ne'),one_mul]
lemma fiscal_graphed(hp:Even n.val): action G n ∘ graze hp=ᶠ[𝓝 0] main G n:=by
 filter_upwards [graze_div G hp,graze_eq G hp] with x hv h
 have hw: wilson (graze hp x)=fiscal x.1:=by rw [← energy_at,h, Wilson.energy_gauge];rfl
 change action G n (graze hp x)= _
 unfold Pert.Orb.action main; rw [hw]; change _+(∑ i:Site n,‖(dLin (graze hp x)).val i‖^2)/4= _; rw [hv]; rfl
lemma fiscal_sliced(hp:Even n.val):∀ᶠ A:Dir G n in 𝓝 0, action G n (steeple hp A).val= fiscal A:=by
 have ht:Tendsto (fun A:Dir G n=>(A,(0: ↥(Flow G n)))) (𝓝 0) (𝓝 0):=tendsto_id.prodMk_nhds tendsto_const_nhds
 filter_upwards [ht.eventually (fiscal_graphed hp),steeple_eq hp] with A h he
 rw [he, show action G n (graze hp (A,0))=main G n (A,0) from h];simp [main,costV]

/-- Observable contract for the formal identity at fixed regulator. -/
structure Watching (o:Wilson.Config G n→ℝ): Prop where
 gauge: ∀ t: Site n→G.El,(∀ x,t (-x)=t x)→ ∀ v, o (Lattice.gauge t v)=o v
 tame: ContDiffAt ℝ ∞ (o ∘ positiveLinks) 0
lemma watch_tree {hp:Even n.val}{o:Wilson.Config G n→ℝ}(h:Watching o) : ∀ᶠ x:Whole G n in 𝓝 0,o (positiveLinks (graze hp x))=o (representative x.1):=by
 filter_upwards [graze_eq G hp] with x he
 rw [he]; exact h.gauge _ (thrust_inv (swing G hp x)) _
lemma watch_land {hp:Even n.val}{o:Wilson.Config G n→ℝ}(h:Watching o): ∀ᶠ A:Dir G n in 𝓝 0,o (positiveLinks (steeple hp A).val)=o (representative A):=by
 have ht:Tendsto (fun A:Dir G n=>(A,(0: ↥(Flow G n)))) (𝓝 0) (𝓝 0):=tendsto_id.prodMk_nhds tendsto_const_nhds
 filter_upwards [ht.eventually (watch_tree (hp:=hp) h),steeple_eq hp] with A H hl; rw [hl];exact H
lemma watch_slick {hp:Even n.val}{o:Wilson.Config G n→ℝ}(h:Watching o): ContDiffAt ℝ ∞ (o ∘ representative) 0:=by
 let f:= branchL G hp
 have h1: o ∘ representative= (o ∘ positiveLinks) ∘ f:= funext fun i=> (congrArg o (bark_pos hp i)).symm
 rw [h1]; apply ContDiffAt.comp
 · rw [map_zero]; exact h.tame
 exact f.contDiff.contDiffAt
lemma watching_unit:Watching (1: Wilson.Config G n→ℝ):= ⟨fun _ _ _=>rfl,contDiffAt_const⟩
end YM.SchemeRG11.Sway
