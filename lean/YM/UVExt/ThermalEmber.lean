import YM.UVExt.RayMesh
import YM.UVExt.TagPrimitive
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Ambit
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Das

/-! Exact thermal profiles for unmasked integrand with moving fields, inverse variable normalized to ratio 1 at Rep. Held group arguments not dilated. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.UVExt.EnergyRay.Thermal
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 Shell Raw SliceRows Mask Coat Art Blaze Vine Polar Frond Silica Flux
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G:Gauge} {E : Type}[NormedAddCommGroup E][NormedSpace ℝ E]
variable {c f:Side} {S:StepData c f} {T:Tube G S} {F:Tree.Forest S.ratio} {P:Teller G}
variable (X:Coat T F) {C : E→Config G c} {y : E} {j d:ℕ} {a W A η : ℝ} {z : Air f G} {k : Finset ℕ} {Ñ : Precision.ChartRatio G} (R : Rep G f)
variable (hp : 0<R.beta) (hÑ : Ñ.scale≠0)
include hp
private lemma shimmer_scale (t : ℝ)(ht:0<t)i : shimmer X (scaled R t).beta i=Real.sqrt t*(shimmer X R.beta i) := by
 simp only [shimmer,Pi.smul_apply,smul_eq_mul]
 unfold gStep; rw [show (scaled R t).beta=t*R.beta from rfl,Real.sqrt_mul ht.le,inv_inv,inv_inv]; ring
-- test exact namespace.
def heatBase (X: Coat T F) (u : Directions G f) (V : Config G f) (Y:Stores S) := -(R.beta*(chalky X u V Y+crispy X Y))

lemma thermal_log (u : Directions G f) (H : Config G f) (z : Air f G) (i : Coat.LogIndex c f) (t : ℝ) (ht:0<t) :
    logMoment X a (scaled R t) Ñ u H (Real.sqrt t • z) i = (if isHotTag i then t else 1)*logMoment X a R Ñ u H z i := by
 dsimp only [logMoment]; rcases i with i|i|i <;> simp only [Sum.elim]
 · unfold frost; dsimp only [nest]; rcases i with i|i|i|i|i|i <;> simp only [Raw.space,Raw.regularFoot, isHotTag,Sum.elim,translateValue,pairValue,icicle,scaled,Bool.false_eq_true,↓reduceIte,one_mul] <;> try ring
 · dsimp only [Polar.whelp]; rcases i with i|i|i
   · simp only [Sum.elim,isHotTag,↓reduceIte]; unfold hover; dsimp only; split
     · simp
     change - (t*R.beta)*_*_ = t*_; ring
   all_goals simp only [Sum.elim,isHotTag,↓reduceIte,Bool.false_eq_true,one_mul]
 rcases i with i|i|i|i|i <;> simp only [spins, isHotTag,↓reduceIte,Bool.false_eq_true,Sum.elim,one_mul,major,entangled,PiLp.smul_apply,smul_eq_mul,qunique]
 · simp_rw [show t * (Polar.patch X a u i * ∑ j:G.ColorIndex, (WithLp.ofLp z (i,j))*shimmer X R.beta (i,j))  = Polar.patch X a u i * ∑ j,t*(WithLp.ofLp z (i,j) * shimmer X R.beta (i,j)) by rw [← Finset.mul_sum]; ring, shimmer_scale X R hp t ht]; apply congrArg _; apply Finset.sum_congr rfl; intro j hj; have h:=Real.sq_sqrt ht.le; linear_combination z (i,j)*shimmer X R.beta (i,j) * h
 · rw [circle_scaled _ _ _ _ ht hp]; ring

include hÑ
lemma unmasked_scaled (H : Stores S)(u : Directions G f) (V : Config G f) (t : ℝ) (ht:0<t): stock X a (scaled R t) W Ñ u V k H=Real.exp ((t-1)*heatBase R X u V H)*(Real.sqrt t)^seedPower X H * stock X a R W Ñ u V k H:= by
 unfold stock; split_ifs
 · have hp':0 < Real.sqrt t:=Real.sqrt_pos.mpr ht
   have he : Real.log (Coat.measure_g Ñ (scaled R t).beta)=Real.log (Coat.measure_g Ñ R.beta)-Fintype.card G.ColorIndex*Real.log (Real.sqrt t) := by
     rw [measure_scaled R Ñ t ht hp,Real.log_div (show Coat.measure_g Ñ R.beta ≠0 from mul_ne_zero hÑ (pow_ne_zero _ (by have := Real.pi_pos; unfold gStep; positivity))) (pow_ne_zero _ hp'.ne'),Real.log_pow]
   have hz : plumeLog X a (scaled R t) Ñ u V H = (t-1)*heatBase R X u V H+plumeLog X a R Ñ u V H + seedPower X H * Real.log (Real.sqrt t) := by unfold plumeLog; rw [he]; unfold heatBase scaled seedPower; push_cast; ring
   rw [hz,Real.exp_add,Real.exp_add,Real.exp_nat_mul,Real.exp_log hp']
   simp only [Contract.order,Contract.charges,Contract.covered,scaled]; ring
 simp
def chandelier (u : Directions G f) (V : Config G f) (z : Air f G) (p : Head S) : Primitive :=
 match p with
 | .inl i => .thermal ((ember X a R W Ñ u V z k d (.inl i) * Real.exp (-heatBase R X u V i) : ℝ):ℂ) (heatBase R X u V i) (seedPower X i)
 | .inr (.inl i) => .thermal (ember X a R W Ñ u V z k d p:ℝ) 0 0
 | .inr (.inr (.inl i)) => if isHotTag i then .split (logMoment X a R Ñ u V z i) else .thermal (ember X a R W Ñ u V z k d p:ℝ) 0 0
 | .inr (.inr (.inr _)) => .thermal (ember X a R W Ñ u V z k d p:ℝ) 0 0

lemma ember_def {b:Directions G f} {V : Config G f} {Y:Coat T F} {w:Air f G} (i : Head S) (r:ℝ) (hr:0<r):
    (chandelier (a:=a) (Ñ:=Ñ) (W:=W) (k:=k) (d:=d) Y R b V w i).run r=(ember Y a (scaled R r) W Ñ b V (Real.sqrt r • w) k d i : ℝ) := by
  rcases i with i|i|i|i
  · dsimp only [chandelier]; rw [Primitive.standard _ _ _ _ hr]
    simp only [ember,Sum.elim]; split
    · rw [unmasked_scaled Y R hp hÑ i b V r hr]
      rw [show (r-1)*heatBase R Y b V i = -heatBase R Y b V i+r*heatBase R Y b V i by ring,Real.exp_add]; push_cast; ring
    simp
  · simp only [chandelier, Primitive.basic]; unfold ember sheath; rfl /- ignored
simpa [Primitive.basic,chandelier,ember,Polar.sheath,scaled]-/
  · dsimp only [chandelier,ember,Sum.elim]
    rw [thermal_log Y R hp b V w i r hr]
    split <;> simp_all only [Primitive.run, Complex.ofReal_sub,Complex.ofReal_one, Complex.ofReal_mul,Complex.ofReal_exp,one_mul,Complex.ofReal_zero,Nat.cast_zero,zero_div,mul_zero,add_zero,Complex.exp_zero,mul_one]
  simp only [chandelier, Primitive.basic]; dsimp only [ember,Sum.elim]; unfold sprinkle; rcases i with (((i|i|i|i|i):_)|i)
  all_goals rfl

end YM.UVExt.EnergyRay.Thermal
namespace YM.UVExt.EnergyRay.Thermal
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision ConnectedActivityE6 Mask Coat ConnectedActivityE6.Art ConnectedActivityE6.Blaze Vine Polar Frond Silica Flux Zest
open ConnectedActivityE6 Raw Pulse Itinerary
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {E : Type}[NormedAddCommGroup E][NormedSpace ℝ E]
variable {c f:Side} {S:StepData c f} {T:Tube G S} {F:Tree.Forest S.ratio} {P:Teller G}
variable (X:ConnectedActivityE6.Coat T F) {C : E→Config G c} {y : E} {j d:ℕ} {a W A η : ℝ} {z : Air f G} {k : Finset ℕ} {Ñ : Precision.ChartRatio G} (R : Rep G f)
open Push.SectorMeasure.Oriented Push.SectorMeasure
variable {α : Type} (H : Glass P X C y j W) {Y: α→ F.Slice G} (U : α → Config G f) {V : E → Config G c} {u : α→ E→ Directions G f} -- fix
-- Copy finite V smooth cost calculation from Glass.bulk. No uniform constant needed for plank values here, only smoothness, enough on all α.
variable (hq : Room P S T X.x) (hu:Zest u y j)
include H hq hu
lemma coal_prepares (i : Stores S) : Zest (fun t z=> heatBase R (drive X (C z) (Y t)) (u t z) (U t) i) y j:= by
  have exert (p : Spot c f) (s : Signed) {u:α→E→Directions G f} (hp : Zest u y j) : Zest
      (fun t y=> Vine.costs (drive X (C y) (Y t)) (u t y) s p) y j := by
    refine Zest.total _ _ (fun i (_:i∈parents p)=>?_); unfold Vine.pot; change
      Zest (fun t y=> if X.selected s (spot S i) then ‖_‖^2 /2 else (0:ℝ)) _ _
    split_ifs
    next ht=> exact (H.fellows u hq (Y:=Y) (s,i) ht hp).wand (p:=fun y:G.Color=> ‖y‖^2/2)
                ((contDiff_norm_sq ℝ).div_const _)
    next => exact Zest.still _
  let s (t:α) z := drive X (C z) (Y t)
  have hU : Zest (fun t z=>chalky (s t z) (u t z) (U t) i) y j := (Zest.total univ _ (fun (v:Signed) _=> Zest.total
      (posted (turnStore v i) (200*X.B)) _ (fun i _=> ((H.canopy v i).1.via (fun t=>pull v 0 (U t))).plusminus (exert _ _ hu)))).scalar Raw.orientation
  have hv:Zest (fun t z=>crispy (s t z) i) y j := (Zest.total univ _ (fun (v:Signed) _=> Zest.total
      (posted (turnStore v i) (200*X.B)) _ (fun i _=> exert i v (H.settles (Y:=Y) hq)))).scalar Raw.orientation
  change Zest (fun t z=> -(R.beta*_)) _ _
  have hh:= (hU.together hv).scalar R.beta |>.against; exact hh

omit H hq hu
variable (w : α → E → Air f G) (η d)
abbrev tempo (z:ℂ) p (t:α) i:= chandelier (a:=a) (Ñ:=Ñ) (W:=W) (k:=k) (d:=d) (drive X (C i) (Y t)) R (u t i) (U t) (w t i) p |>.run z
abbrev perReal (θ:ℝ) p (t:α) i := ember (drive X (C i) (Y t)) a (scaled R θ) W Ñ (u t i) (U t) (Real.sqrt θ • w t i) k d p
variable (hw:Zest w y j) (hp:0<R.beta) (hÑ:Ñ.scale≠0)
include hw hÑ hp H hq hu

local notation "𝔥" zs:max "|" p:max "|" v:max => tempo (C:=C) (Y:=Y) (a:=a) (Ñ:=Ñ) (W:=W) (k:=k) (u:=u) X d R U w zs p v
local notation "𝔯" zs:max "|" p:max "|" v:max => perReal (C:=C) (Y:=Y) (a:=a) (Ñ:=Ñ) (W:=W) (k:=k) (u:=u) X d R U w zs p v
omit hw H hq hu in
lemma core_grain (i : Head S) (t:α) (H' : ∀ p, ContDiffAt ℝ (↑j) (fun v=> heatBase R (drive X (C v) (Y t)) (u t v) (U t) p) y) : match i with
 | .inl q => ∃ b:E→ℝ, CoalAt (fun s₀=>𝔯 s₀|(.inl q)|t) y j (seedPower X q) (fun s₀=>𝔥 s₀|(.inl q)|t) b
 | Sum.inr (.inr (.inl q)) => let h:Head S:=.inr (.inr (.inl q)); if isHotTag q then Fits (fun s₀=>𝔥 s₀|h|t) (fun s₀=>𝔯 s₀|h|t) .soot else ∃ b:E→ℝ, CoalAt (fun s₀=>𝔯 s₀|h|t) y j 0 (fun s₀=>𝔥 s₀|h|t) b
 | z => ∃ b:E→ℝ, CoalAt (fun s₀=>𝔯 s₀|z|t) y j 0 (fun s₀=>𝔥 s₀|z|t) b := by
  have hf (s:ℝ) (hs:0<s) i z : (𝔥 (↑s)|i|t) z=((𝔯 s|i|t) z:ℝ) := ember_def R hp hÑ i s hs
  let V z:= drive X (C z) (Y t); rcases i with Y'|i|i|i
  · refine ⟨fun z=>heatBase R (V z) (u t z) (U t) Y',⟨?_,?_⟩,Or.inl ?_,fun s h z=>?equal⟩
    · exact fun z => ember (V z) a R W Ñ (u t z) (U t) (w t z) k d (.inl Y') * Real.exp (-heatBase R (V z) (u t z) (U t) Y')
    · intros; unfold tempo chandelier; push_cast; rfl
    · exact H' Y'
    · exact hf s h _ z
  · exact ⟨0,⟨fun z=>(𝔯 1|(.inr (.inl i))|t) z,fun z v=>by unfold tempo perReal chandelier; simp only [scaled_one, Real.sqrt_one,one_smul]; rfl⟩, Or.inl contDiffAt_const, fun s h z=> hf s h _ z⟩
  · dsimp only; split
    next h=> refine ⟨fun v=> logMoment (V v) a R Ñ (u t v) (U t) (w t v) i,?_,fun s h z=> hf s h _ z⟩
             dsimp [tempo,chandelier]; simp only [h,if_pos, decide_true]; intros; rfl
    next h=> refine ⟨0,⟨fun z=>(𝔯 1|(.inr (.inr (.inl i)))|t) z,fun z v=>?_⟩, Or.inl contDiffAt_const, fun s h z=> hf s h _ z⟩
             unfold tempo perReal chandelier; simp only [scaled_one, Real.sqrt_one,one_smul,if_neg h]; rfl
  exact ⟨0,⟨fun z=>(𝔯 1|(.inr (.inr (.inr i)))|t) z,fun z v=>by unfold tempo perReal chandelier; simp only [scaled_one, Real.sqrt_one,one_smul]; rfl⟩, Or.inl contDiffAt_const, fun s h z=> hf s h _ z⟩
lemma tempo_form (i : Head S) (t:α) : match i with
 | .inl q => ∃ b:E→ℝ, CoalAt (fun s₀=>𝔯 s₀|(.inl q)|t) y j (seedPower X q) (fun s₀=>𝔥 s₀|(.inl q)|t) b
 | Sum.inr (.inr (.inl q)) => let h:Head S:=.inr (.inr (.inl q)); if isHotTag q then Fits (fun s₀=>𝔥 s₀|h|t) (fun s₀=>𝔯 s₀|h|t) .soot else ∃ b:E→ℝ, CoalAt (fun s₀=>𝔯 s₀|h|t) y j 0 (fun s₀=>𝔥 s₀|h|t) b
 | z => ∃ b:E→ℝ, CoalAt (fun s₀=>𝔯 s₀|z|t) y j 0 (fun s₀=>𝔥 s₀|z|t) b := by
  have hf (s:ℝ) (hs:0<s) i z : (𝔥 (↑s)|i|t) z=((𝔯 s|i|t) z:ℝ) := ember_def R hp hÑ i s hs
  let V z:= drive X (C z) (Y t); rcases i with Y'|i|i|i
  · refine ⟨fun z=>heatBase R (V z) (u t z) (U t) Y',⟨?_,?_⟩,Or.inl ?_,fun s h z=>?equal⟩
    · exact fun z => ember (V z) a R W Ñ (u t z) (U t) (w t z) k d (.inl Y') * Real.exp (-heatBase R (V z) (u t z) (U t) Y')
    · intros; unfold tempo chandelier; push_cast; rfl
    · obtain ⟨hh,hC,hz⟩:= coal_prepares X R H U hq hu Y'; exact (hz.self_of_nhds t).smooth
    · exact hf s h _ z
  · exact ⟨0,⟨fun z=>(𝔯 1|(.inr (.inl i))|t) z,fun z v=>by unfold tempo perReal chandelier; simp only [scaled_one, Real.sqrt_one,one_smul]; rfl⟩, Or.inl contDiffAt_const, fun s h z=> hf s h _ z⟩
  · dsimp only; split
    next h=> refine ⟨fun v=> logMoment (V v) a R Ñ (u t v) (U t) (w t v) i,?_,fun s h z=> hf s h _ z⟩
             dsimp [tempo,chandelier]; simp only [h,if_pos, decide_true]; intros; rfl
    next h=> refine ⟨0,⟨fun z=>(𝔯 1|(.inr (.inr (.inl i)))|t) z,fun z v=>?_⟩, Or.inl contDiffAt_const, fun s h z=> hf s h _ z⟩
             unfold tempo perReal chandelier; simp only [scaled_one, Real.sqrt_one,one_smul,if_neg h]; rfl
  exact ⟨0,⟨fun z=>(𝔯 1|(.inr (.inr (.inr i)))|t) z,fun z v=>by unfold tempo perReal chandelier; simp only [scaled_one, Real.sqrt_one,one_smul]; rfl⟩, Or.inl contDiffAt_const, fun s h z=> hf s h _ z⟩
def heatTax (i:Head S) := match i with
 | .inl p => seedPower X p
 | .inr (.inr (.inl z)) => if isHotTag z then 2 else 0
 | _ => 0
lemma ember_brush {V:ℝ→ℝ} (U':ℂ) (i:Head S) (t:α) {δ' γ:ℝ}
    (hd:0<δ') (hv : (4*(j+1):ℕ)*δ' ≤ U'.re) (ht:|U'.im|≤δ') (hs : ∀ r,0≤V r) (hs' : 0≤γ)
    (H': ∀ i' j':Fin (j+1), let r:=nodes U' δ' i' j'; Brush j (V r) γ (𝔯 r|i|t) y):
    Brush j (cash U' (δ:=δ') (n:=j) V*(deck U' (n:=j) (δ:=δ'))^heatTax X i) γ (𝔥 U'|i|t) y := by
    have hU:0<U'.re:=(show 0<(↑(4*(j+1):ℕ):ℝ)*δ' by positivity).trans_le hv
    have hh := tempo_form (a:=a) (Y:=Y) (k:=k) X d R H U hq hu w hw hp hÑ i t
    have hC i b := glance U' hd hv ht (fun z=>𝔥 z|i|t) (fun z=>𝔯 z|i|t) (W:=V) (x:=y) (b:=b) (n:=j) (heatTax X i) hs'
    rcases i with i|i|i|i
    · obtain ⟨b,h⟩:=hh; exact (hC (.inl i) b H' h).climb (pure U' _ hs (by unfold deck speed; positivity)) le_rfl
    · obtain ⟨b,h⟩:=hh; exact (hC (.inr (.inl i)) b H' h).climb (pure U' _ hs (by unfold deck speed; positivity)) le_rfl
    · dsimp only at hh; split_ifs at hh with hZ
      · dsimp [heatTax]; rw [if_pos hZ]; exact soot_jets U' hd hv ht H' hs' hh
      dsimp [heatTax]; rw [if_neg hZ]; obtain ⟨b,h⟩:= hh; exact (glance U' hd hv ht (x:=y) _ _ 0 hs' H' h).climb (pure U' _ hs (by unfold deck speed; positivity)) le_rfl
    · obtain ⟨b,h⟩:=hh; exact (hC (.inr (.inr (.inr i))) b H' h).climb (pure U' _ hs (by unfold deck speed; positivity)) le_rfl
omit hw H hq hu in
lemma harvest {V:ℝ→ℝ} (U':ℂ) (i:Head S) (t:α) (hG : ∀ p, ContDiffAt ℝ (↑j) (fun v=> heatBase R (drive X (C v) (Y t)) (u t v) (U t) p) y) {δ' γ:ℝ}
    (hd:0<δ') (hv : (4*(j+1):ℕ)*δ' ≤ U'.re) (ht:|U'.im|≤δ') (hs : ∀ r,0≤V r) (hs' : 0≤γ)
    (H': ∀ i' j':Fin (j+1), let r:=nodes U' δ' i' j'; Brush j (V r) γ (𝔯 r|i|t) y):
    Brush j (cash U' (δ:=δ') (n:=j) V*(deck U' (n:=j) (δ:=δ'))^heatTax X i) γ (𝔥 U'|i|t) y := by
    have hU:0<U'.re:=(show 0<(↑(4*(j+1):ℕ):ℝ)*δ' by positivity).trans_le hv
    have hh := core_grain (W:=W) (a:=a) (Y:=Y) (k:=k) X d R U w hp hÑ i t hG
    have hC i b := glance U' hd hv ht (fun z=>𝔥 z|i|t) (fun z=>𝔯 z|i|t) (W:=V) (x:=y) (b:=b) (n:=j) (heatTax X i) hs'
    rcases i with i|i|i|i
    · obtain ⟨b,h⟩:=hh; exact (hC (.inl i) b H' h).climb (pure U' _ hs (by unfold deck speed; positivity)) le_rfl
    · obtain ⟨b,h⟩:=hh; exact (hC (.inr (.inl i)) b H' h).climb (pure U' _ hs (by unfold deck speed; positivity)) le_rfl
    · dsimp only at hh; split_ifs at hh with hZ
      · dsimp [heatTax]; rw [if_pos hZ]; exact soot_jets U' hd hv ht H' hs' hh
      dsimp [heatTax]; rw [if_neg hZ]; obtain ⟨b,h⟩:= hh; exact (glance U' hd hv ht (x:=y) _ _ 0 hs' H' h).climb (pure U' _ hs (by unfold deck speed; positivity)) le_rfl
    · obtain ⟨b,h⟩:=hh; exact (hC (.inr (.inr (.inr i))) b H' h).climb (pure U' _ hs (by unfold deck speed; positivity)) le_rfl
end YM.UVExt.EnergyRay.Thermal
