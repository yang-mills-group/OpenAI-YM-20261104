import YM.GapsContact.Earn.Row
/-!
# Mesoscopic comparator in its unselected, point Gram

Real scalarization but peal observed against any complex multiplier. Exact same selection law,
compared eventually with both stencil output and canonical field. Computed only when probes have
the promised clearance (for all small enough lengths; for clarity actually work through positive ≤1).
Derivative prices (even though this execution path includes arbitrary resampling on the label unit spheres)
at fixed probe scales apply to the FIELD branch and polynomial peal, no differentiating max or selected
lengths. `deck` multilinearity in readers suffices. No statement on ghost contact outputs in a different
field scheme.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Seams
open Set Function Filter MeasureTheory Analysis Spec Table Extraction Lattice
open Frontier6 Frontier6.Tale Frontier6.Road Ascent Power Trace Trace.Terrace Trace.Pilot
open OPE Push.FiniteDetection Push.FiniteDetection.Free
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F: Final C f S)
variable {e d :ℕ}
variable {t r g a:ℝ}
universe u
variable {h:G.Simple}{A:EveryPhase.Almanac F}
variable (H:Roll.{u} F h A)
local notation "H₀"=> F.room.kernel
local notation "E!"=> F.sector.derivatives

abbrev dial (t:ℝ)(o:E4) := o - t • basis timeAxis
lemma dial_cost (o:E4)(ht:0<t): ‖dial t o-o‖=t:=by simp [dial,sub_eq_add_neg, add_comm,norm_smul,Real.norm_of_nonneg ht.le]
lemma dial_walk (o:E4)(p:E4)(t:ℝ): dial t o+p=dial t (o+p):=by unfold dial; abel
lemma dial_rack (o:E4)(ht:0<t)(hp:g≤ t):Balcony g t t (fun _ : Unit=>dial t o) o:=⟨hp,le_rfl,fun _=> (dial_cost o ht).symm.le, fun _ _ h=>(h (Subsingleton.elim ..)).elim⟩

local notation "X!"=> Spelling S
-- billing peal at bond. Use explicit basis LL when derivatives later. In `Spelling` do not assume ℝ-smul
-- harmonized: pass through a cast or commute in peal.
def bellframe (t:ℝ)(o:E4)(x:S.Field d): Spelling S:= letter S (dial t o) (⟨d,flipField F d x⟩:S.Tag)
lemma bell_response {x y:S.Field d}(ht:0<t) (o:E4): bond H₀ d t x y= (peal F none (letter S o ⟨d,x⟩ * bellframe F t o y)).re:= by
   let u:= t • basis timeAxis; let v:=dial t o; let f:=t • detectors; let z:= (![o,v]:Fin 2→ E4);
   let w:= (![⟨d,x⟩,⟨d,flipField F d y⟩]: Fin 2→ S.Tag); have he:o=v+u:=by unfold v dial u; abel
   have hf: ![(o:E4),v]= fun i:Fin 2=> f i + v:=by funext i; fin_cases i<;> simp [f,detectors,Kelvin.pole,u,he,add_comm] -- he loop?
   have hp:v≠o:= by intro h; have hh:=dial_cost o ht; change ‖v-o‖=_ at hh; rw[h,sub_self,norm_zero] at hh; exact ht.ne hh
   let A:= letter S o ⟨d,x⟩ * bellframe F t o y
   have hu:A= assembly S z w:=by unfold z w assembly; rw [Fin.prod_univ_two]; rfl
   rw [bonded]; change (valTwo S d f x (flipField F d y)).re=(peal F none A).re; rw [hu]; unfold z peal; rw [hf,translating F none v w (fun i:Fin 2=> f i)]; rw [examines S _ (hierarchy F none).laws.toSymmetric f w,if_pos (detector_in ht)]; exact congr_arg Complex.re ((knot_val ..).symm.trans (knotted ..)) -- elaboration?

def cropSpin (d:ℕ) : S.Field d →ₗ[ℝ] S.Field d where
   toFun v:= flipField F d v
   map_add' v w:= by unfold flipField; rw [map_add,map_add]
   map_smul' c v:=by unfold flipField; rw [←Complex.coe_smul, LinearMap.map_smulₛₗ,map_smul]; simp
-- reading identity as real linear functional even when some probe positions invalid (symbolic multilinearity)
def snapshot (d:ℕ) (t:ℝ)(o:E4)(X:Spelling S) : Module.Dual ℝ (S.Field d):= Complex.reLm.comp (((Tale.readingMap F (dial t o) d X none).restrictScalars ℝ).comp (cropSpin F d))
lemma snapshot_read (o:E4)(t:ℝ)(X:Spelling S)(x:S.Field d) : snapshot F d t o X x=(peal F none (X * bellframe F t o x)).re:=by rw [mul_comm X]; exact congr_arg Complex.re (Tale.reads F d none (dial t o) X (flipField F d x)) -- inspect args

def lookup (d:ℕ)(o:E4)(t:ℝ)(X:Spelling S) : S.Field d := if h:Bijective (Power.bond F.room.kernel d t) then (LinearEquiv.ofBijective (Power.bond F.room.kernel d t) h).symm (snapshot F d t o X) else 0
lemma graphCore (ht:0<t)(hT:Good H₀ d t)(o:E4)(X:Spelling S):Power.bond (H₀) d t (lookup F d o t X)=snapshot F d t o X:=by unfold lookup; rw [dif_pos (bankable H₀ ht hT)]; exact (LinearEquiv.ofBijective (bond H₀ d t) (bankable H₀ ht hT)).apply_symm_apply _
lemma graph_one (ht:0<t)(hT:Good H₀ d t)(o:E4)(x:S.Field d): lookup F d o t (letter S o ⟨d,x⟩)=x:=by apply (bankable H₀ ht hT).1; refine LinearMap.ext (fun y=>?_);  rw [graphCore F ht hT,snapshot_read,bell_response F ht o]
lemma graph_add (ht:0<t)(hT:Good H₀ d t)(o:E4)(X Y:Spelling S): lookup F d o t (X+Y)=lookup F d o t X+lookup F d o t Y:=by
   apply (bankable H₀ ht hT).1; rw [graphCore F ht hT,map_add,graphCore F ht hT,graphCore F ht hT]; refine LinearMap.ext (fun y=>?_);  rw [LinearMap.add_apply]; simp only [snapshot_read,add_mul,map_add,Complex.add_re]
lemma graph_smul (ht:0<t)(hT:Good H₀ d t)(o:E4)(c:ℝ)(X:Spelling S) : lookup F d o t ((c:ℂ) • X)=c • lookup F d o t X:=by
   apply (bankable H₀ ht hT).1; rw [graphCore F ht hT,map_smul,graphCore F ht hT]; refine LinearMap.ext (fun y=>?_);  rw [LinearMap.smul_apply]; simp only [snapshot_read,smul_mul_assoc,map_smul]; rw [Complex.coe_smul]; exact Complex.reLm.map_smul c _
lemma graph_sub (ht:0<t)(hT:Good H₀ d t)(o:E4)(X Y:Spelling S): lookup F d o t (X-Y)=lookup F d o t X-lookup F d o t Y:=by
   apply (bankable H₀ ht hT).1; rw [graphCore F ht hT,map_sub,graphCore F ht hT,graphCore F ht hT]; refine LinearMap.ext (fun y=>?_);  rw [LinearMap.sub_apply]; simp only [snapshot_read,sub_mul,map_sub,Complex.sub_re]

-- difference prices by probes, don't do triangle on BOTH terms. uses real multiplier, not fitted coefficient.
lemma one_duel (ht:0<t)(hT:Good H₀ d t)(o:E4)(X:Spelling S){C':ℝ}(hv:0 ≤ C')(hW:∀ x:S.Field d,cost F d t x ≤ 1→ (peal F none (X*bellframe F t o x)).re ≤ C'):
    cost F d t (lookup F d o t X) ≤ C':=by
   let x:=lookup F d o t X; by_cases he:x=0; · change cost _ _ _ x≤_; rw [he,cost_zero]; exact hv
   let T:= cost F d t x; have hp:0<T:= hT x he
   let y:= T⁻¹ • x; have hq: cost F d t y=1:=by unfold y; rw [paid_coin, chip_real, Real.norm_of_nonneg (by positivity),← paid_coin F]; exact inv_mul_cancel₀ hp.ne'
   refine le_trans ?_ (hW y hq.le); rw [← snapshot_read, ← graphCore F ht hT]; change _ ≤ (Power.bond _ d t x) y; unfold y; rw [map_smul,← bond_root _ ht,← paid_coin F]; change T ≤ T⁻¹*T^2; exact Eq.le (by field_simp)

lemma roughGraph (ht:0<t)(hT:Good H₀ d t)(x:S.Field d)(o:E4)(X:Spelling S){C':ℝ}(hp:C'≥0)(hW:∀ u:S.Field d,cost F d t u ≤ 1 → ‖peal F none ((X-letter S o ⟨d,x⟩)*bellframe F t o u)‖ ≤ C') :
    cost F d t (lookup F d o t X-x) ≤ C':=by
   refine ((show lookup F _ o t (X-letter _ _ _)=lookup F _ o t X-x from (graph_sub F ht hT ..).trans (congr_arg _ (graph_one F ht hT o x))).symm ▸ ?_) -- might orientation of ▸
   exact one_duel F ht hT o (X-letter _ o ⟨d,x⟩) hp (fun u hu=>(Complex.re_le_norm _).trans (hW u hu))

open OPE
variable {I J:Type*}[Fintype I][Fintype J]
-- graph raw exchange estimate incl scalars used unconstrained in derivative line
include H
lemma raw_graph (d:I→ℕ)(w:ℕ) :∃ (B:ℝ) (m:ℕ),1≤ B∧ ∀ (x:I→ E4)(v:I→ S.Tag)(g r t:ℝ)(o:E4), Shelf g r t→VisitS g r x o→ (∀ i,(v i).1=d i) → cost F w t (lookup F w o t (assembly S x v)) ≤ B*dock g^m * billSlots F g v:=by
   obtain ⟨B,m,hB,hV⟩:= raw_slots F H d (fun _:Unit=> w); obtain ⟨c,hc,hC⟩:= cash_spin F H w
   refine ⟨B*c,m,one_le_mul_of_one_le_of_one_le hB hc,fun x v g r t o hr hx hv=> one_duel F hr.period.2.2.1 (all_good F H t hr.period.2.2.1 w) o _ ?_ (fun y hy=>?_ )⟩
   all_goals
     have ht:=hr.period.2.2; have he:= dock_valid _ (show g∈ Ioc 0 1 from ⟨hr.credit,(hr.fit.trans hr.tie.2).trans ht.2⟩); have hk:= billSlots_pos F g v
   · exact mul_nonneg (by positivity) hk
   apply (Complex.re_le_norm _).trans
   let V'(_ :Unit) := (⟨w,flipField F w y⟩: S.Tag); rw [show bellframe F t o y= assembly S (fun _ : Unit=> dial t o) V' from by rw [assembly,Fintype.prod_unique]; rfl]
   have hy' : billSlots F t V' ≤ c:=by
      unfold billSlots crestSet; rw [Fintype.prod_unique]; exact (hC t ht y).trans (mul_le_of_le_one_right (zero_le_one.trans hc) hy)
   apply (hV o none g r t t x _ v V' hr hx (dial_rack _ ht.1 (hr.fit.trans hr.tie.2)) hv (fun _=>rfl)).trans; exact (mul_le_mul_of_nonneg_left hy' (show 0≤B*dock g^m * billSlots F g v from mul_nonneg (by positivity) hk)).trans_eq (by ring)

lemma raw_guess (d:I→ℕ)(e:J→ℕ)(w:ℕ) :∃ (B:ℝ)(m:ℕ),1≤ B∧ ∀ (x:I→ E4)(y:J→ E4)(v:I→ S.Tag)(u:J→ S.Tag)(g r t a:ℝ)(o:E4)(s:StateIndex F), Shelf g r t→VisitS g r x o→ Balcony g a t y o → (∀ i,(v i).1=d i) → (∀ i,(u i).1=e i) →
     let X:= assembly S x v; let Y:= assembly S y u;
     ‖peal F s ((X-letter S o ⟨w,lookup F w o t X⟩)*Y)‖ ≤ B*dock g^m * billSlots F g v * billSlots F a u := by
   obtain ⟨B,m,hB,hT⟩:= raw_slots F H d e; obtain ⟨C',p,hC,hV⟩:= raw_graph F H d w; obtain ⟨c,l,hc,hL⟩:= raw_letter F H e w
   refine ⟨B+c*C',max m (l+p),(le_add_of_nonneg_right (by positivity : 0 ≤ c*C') |>.trans' hB), ?_⟩
   intro x y v u g r t a o s hr hx hy hv hu X Y
   have ht: t ∈Ioc (0:ℝ) 1:= hr.period.2.2; have he:1≤ dock g:= dock_valid _ ⟨hr.credit, (hr.fit.trans hr.tie.2).trans ht.2⟩; have hh:= billSlots_pos F g v; have hf:= billSlots_pos F a u
   rw [sub_mul,map_sub,add_mul,add_mul (_*_ : ℝ), add_mul (_*_ * _ : ℝ)]; apply (norm_sub_le ..).trans; refine add_le_add ?_ ?_
   · apply (hT o s g r t a x y v u hr hx hy hv hu).trans; gcongr; exact le_max_left ..
   refine (hL o s g t a y _ u ht.2 hr.credit hy hu).trans ?_; apply mul_le_mul_of_nonneg_right _ hf; calc
      _ ≤ c*dock g^l * (C'*dock g^p * billSlots F g v) := mul_le_mul_of_nonneg_left (hV x v g r t o hr hx hv) (by positivity)
      _ = c*C'*dock g^(l+p)* billSlots F g v := by rw [pow_add]; ring
      _ ≤ _ := by gcongr; exact le_max_right ..
end YM.GapsContact.Seams
