import YM.MS.Charted
import YM.MS.PricedLine
/-!
# Test norms on kernel charts, single loop and tree

Use `bulk` flag when extending marked arguments. A translation invariant
(single insertion with a compensating external spur, for example) uses bulk
charts; if at anchor, arbitrary momentum allowed. No implicit pose. Finite
order and rank: say exactly which ranks are compared. Don't hide Taylor conditions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Plane
open Koszul Wire Function Set Finset Filter MeasureTheory Real
open scoped Topology ContDiff
variable {ι A P E F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable (m : A → ℤ) (h : ℤ) (a : ι → ℝ)

@[simp] def fieldDim {P : Type} (w : Legs (Mode A P)) : ℤ := (w.map (m ∘ Prod.fst)).sum
-- avoid unfolding in simp later
attribute [-simp] fieldDim
@[simp] lemma field_cons {P : Type} i (w : Legs (Mode A P)) : fieldDim m (i::w)=m i.1 + fieldDim m w:=by simp [fieldDim]
@[simp] lemma field_lift (L : F→L[ℝ] E) (w : Wire A E P) : fieldDim m (lift w L)=fieldDim m w:=by simp only [fieldDim,← List.map_map,lift_base]

abbrev Pool ι (A P : Type) := ι → Row A P ℂ

def Course (b : Bool) (w : Legs (Mode A P)) : Prop := b=true → net w=0

lemma attaches_course (b : Bool) (k v w : Wire A E P) (he : Split k v w) (hp : Course b w) (l : A) : Course b ((l,net k)::v) := by
   intro h; rw [net_cons]; exact (split_net he).trans (hp h)

lemma lift_course (b : Bool) (w : Wire A E P) (L : F →L[ℝ] E) (h : Course b w) : Course b (lift w L) := fun hx=> by rw [lift_net,h hx]; rfl
variable {m h a} (S : Scale ι) (b : Bool)

def Virt (f : Pool ι A P) (w : Wire A E P) (h : ℤ) (m : A → ℤ) := Bound S (Chart f w) fun i=> S.length i ^ (fieldDim m w-h)
def Light (a : ι → ℝ) (m : A → ℤ) (f g : Pool ι A P) (w : Wire A E P) (h : ℤ) := Like S.full S a (Chart f w) (Chart g w) fun i _=> S.length i ^ (fieldDim m w-h)

def Match (f g : Pool ι A P) (h : ℤ) (a : ι → ℝ) (m : A → ℤ) (r : ℕ) :=
   ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E], ∀ w : Wire A E P, Course b w → w.length = r → Light S a m f g w h

lemma match_agrees {f g l k : Pool ι A P} {r : ℕ} (hf : ∀ i w, Course b w → w.length=r → f i w=l i w) (hg : ∀ i w, Course b w → w.length=r → g i w=k i w) (h' : Match S b f g h a m r) : Match S b l k h a m r := by
  intro X _ _ w hw hr
  have Hx : ∀ x, Course b (sail w x):= fun x hb=>by rw [sail_net,hw hb]; rfl
  specialize h' X w hw hr; unfold Light at *; convert! h' using 1
  funext i x; exact (hf i _ (Hx x) ((sail_len w x).trans hr)).symm
  funext i x; exact (hg i _ (Hx x) ((sail_len w x).trans hr)).symm

variable [Fintype A]
namespace Flux
variable [MeasurableSpace P]
/-- Very simple one-loop operation. Prove integrability when using it. -/
def cycle (K : Flux A P ℂ) (μ : Measure P) (f : Row A P ℂ) : Row A P ℂ := fun w=> ∫ q, trc K q f w ∂μ
end Flux
open Flux
variable (a m)
abbrev Meter (K J : ι → Flux A P ℂ) (D : ι → Set P) (e : ℤ) := ∀ i j, Sharp S a D (fun k=> K k i j) (fun k=> J k i j) fun k=> S.length k ^ (e-m i-m j)

variable {b S a m p}
variable {p : Sector A} {K J : ι → Flux A P ℂ} {D : ι → Set P} {e : ℤ}
  {f g l k : Pool ι A P} {w : Wire A E P}

section cycle
variable (L : Meter (a:=a) (m:=m) S K J D e)
    (q : ℕ) (ha : ∀ i, (S.length i ^ q)⁻¹ ≤ a i) (hD : ∀ i p, p ∉ D i → 1≤‖p‖)
include L ha hD
lemma dot_line_value (hp : Course b w) (F : Match S b f g h a m (w.length+2)) :
   Value S a D (fun i (p:P×E)=> trc (K i) p.1 (f i) (sail w p.2)) (fun i (p:P×E)=>trc (J i) p.1 (g i) (sail w p.2)) fun i=> S.length i ^ (fieldDim m w - h + e) := by
   have hw i : 0≤ S.length i ^ (fieldDim m w-h+e) := zpow_nonneg (S.pos _).le _; have ha' i : 0 ≤ a i:= (inv_nonneg.mpr (pow_nonneg (S.pos i).le _)).trans (ha i)
   simp_rw [at_trc]; refine Value.sum _ (fun c _=> Value.sum _ (fun d _=> ?_) hw ha') hw ha'
   let M : P×E→L[ℝ] P := ContinuousLinearMap.fst ℝ P E; let N : P × E→L[ℝ] E:= ContinuousLinearMap.snd ℝ P E
   let W : Wire A (P×E) P:= (c,M)::(d,-M)::lift w N
   have H : Course b W:= fun hx=> by simp [W,lift_net,hp hx]
   have H' := F (P×E) W H (by simp [W]); unfold Light at H'
   convert ((L c d).value ha hD).mul H' using 1
   · funext; rw [Chart]; simp [W,M,N]
   · funext; rw [Chart]; simp [W,M,N]
   funext; simp only [W,field_cons,field_lift,← zpow_add₀ (S.pos _).ne']; ring_nf

variable [MeasurableSpace P] [BorelSpace P] [FiniteDimensional ℝ P]
lemma dot_line_cycle (hp : Course b w) (F : Match S b f g h a m (w.length+2)) (μ : Measure P) [μ.IsAddHaarMeasure] (h' : ∀ i, MeasurableSet (D i)) :
    Light S a m (fun i=>cycle (K i) (μ.restrict (D i)) (f i)) (fun i=>cycle (J i) μ (g i)) w (h-e+Module.finrank ℝ P) := by
   unfold Light; convert (dot_line_value L q ha hD hp F).integrates (fun i=> (zpow_nonneg (S.pos _).le _)) (fun i=>(inv_nonneg.mpr (pow_nonneg (S.pos i).le _)).trans (ha i)) h' μ using 1 <;> first | rfl | funext i p
   rw [← zpow_natCast, ← zpow_neg, ← zpow_add₀ (S.pos _).ne']; ring_nf
end cycle

lemma attach_cost {ζ : ℤ} {c d : Wire A E P} (L : Meter (a:=a) (m:=m) S K J D e)
    (hp : Course b w) (ha : ∀ i, 0≤ a i) (hw : Split c d w)
    (F : Match S true f g h a m (c.length+1)) (Q : Match S b l k ζ a m (d.length+1)) :
    Like S.full S a (fun i x=> attaches p (K i) (f i) (l i) (sail c x) (sail d x))
                   (fun i x=> attaches p (J i) (g i) (k i) (sail c x) (sail d x))
      fun i _=> S.length i ^ (fieldDim m w-(h+ζ-e)) := by
   unfold attaches; simp only [sail_degree,sail_net,neg_neg]
   let x := fieldDim m w-(h+ζ-e)
   have hx : (S.full (E:=E)).NN (fun i _=> S.length i ^ x):= fun i _ _=> zpow_nonneg (S.pos _).le _
   have Fs (u:A) (z : ℂ) := (show Like S.full S a (Chart f ((u,-net c)::c)) (Chart g ((u,-net c)::c)) (fun i _=> S.length i ^ (fieldDim m ((u,-net c)::c)-h)) from (F E _ (fun _=>by simp) rfl)).L (ContinuousLinearMap.mul ℝ ℂ z)
   have Fd (u : A) : Like S.full S a (Chart l ((u,net c)::d)) (Chart k ((u,net c)::d)) (fun i _=> S.length i ^ (fieldDim m ((u,net c)::d)-ζ)) := Q E _ (attaches_course b c d w hw hp u) rfl
   have H:= Koszul.split_sum (m ∘ Prod.fst) hw; change fieldDim m c+fieldDim m d=fieldDim m w at H
   refine Like.sum (s:=Finset.univ) (fun u _=> Like.sum (s:=Finset.univ) (fun v _=> Like.add ?_ ?_) hx ha) hx ha
   · convert! (((L u v).both.pull (-net c)).mul ((Fs u (cross (p v) (degree (field p) c))).mul (Fd v))) using 1 -- expect all defeq except exponent
     funext; simp only [field_cons,← zpow_add₀ (S.pos _).ne', ←H]; ring_nf
   convert! (((L u v).both.pull (net c)).mul ((Fs v (cross (p u) (p v ^^ degree (field p) c))).mul (Fd u))) using 1
   funext; simp only [field_cons,← zpow_add₀ (S.pos _).ne',←H]; ring_nf

lemma dot_line_tree {ζ : ℤ} (L : Meter (a:=a) (m:=m) S K J D e) (ha : ∀ i, 0 ≤ a i) (hw : Course b w) (F : ∀ n≤w.length, Match S true f g h a m (n+1)) (Q : ∀ n≤w.length, Match S b l k ζ a m (n+1)) :
    Light S a m (fun i=> tree p (K i) (f i) (l i)) (fun i=>tree p (J i) (g i) (k i)) w (h+ζ-e) := by
   unfold Light Chart tree; simp_rw [sail_scatter]
   refine gather_like w (fun i j H=>?_); have hj:=Koszul.split_length H
   exact attach_cost L hw ha H (F _ (by omega)) (Q _ (by omega))
end YM.MS.Plane
