import YM.RGComparison01.AuxPackage

/-!
# Restore the constructed centered vacuum cover term (still on auxiliary torus)

Explicit fixed-volume scalar separation. Primary traversal `ϕ` has no linear
term; hence recipe is polynomial in truly rescaled variables, without Laurent ambiguity.
No kinetic-reset cost at this stage.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.AuxCover
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open PhysicalNext.Repeat Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open Push.AbsoluteSums Fare Sienna AuxDesk Token AuxFabric AuxConstant AuxMiles AuxJets AuxWeigh AuxPackage WilsonStartup
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MatrixOrder
variable {G : Gauge} (A : ChartRatio G) {C σ Λ u a H D : ℝ} {k j n : ℕ}
    {c f: Side} {S:StepData c f} (T:Tube G S) (F:Forest S.ratio) (i:S.Choices) (ρ:Bid.Dir G c→AxisChart G F)
    (p:Before G σ C S.patch.J S.kernel (k+3))
local notation "Xs" => Positions (Uniform.Primary c G)
local notation "M" => Lapis.gram F T.up T.high ρ i
local notation "r" => orbit F ρ
local notation "φ" => Lapis.table F i T.up T.high

def off (β:ℝ) (x:Xs):= coverLog F T A i ρ β x-Lantern.shade M 0
def mainCover (x:ℝ×Xs):= φ (x.2,r x.2)
def extra (x:ℝ×Xs):= mist F A T.up (x.2,r x.2) + (Lantern.shade M x.2-Lantern.shade M 0)
def collector := ritual (mainCover T F i ρ) 2 + ritual (extra A T F i ρ) 0

variable (h : Golf (Lapis.table F i T.up T.high) (Lapis.mist F A T.up) (Lapis.orbit F ρ) (Lapis.gram F T.up T.high ρ i) k D u u H) (hp : p.Service F T.high T.up ρ) (hh : Larger (G:=G) S) (hf: T.up.Bounds T.high σ C Λ)
include A h
abbrev readAt (k:ℕ) (H:ℝ) := Lantern.clump k (1+H+(1+H)) H
lemma covers {x : ℝ×Xs} (hx:‖x‖ < u) : Brush k (readAt k H) 1 (mainCover T F i ρ) x ∧ Brush k (readAt k H+H) 1 (extra A T F i ρ) x:= by
  have hz:= _root_.norm_snd_le x; have hx': ‖x.2‖ < u:= hz.trans_lt hx
  have hv := h.curve x.2 hx'; have hC:= hv.nonneg
  let L:= ContinuousLinearMap.snd ℝ ℝ Xs; have hr : ‖L‖≤1:= ContinuousLinearMap.norm_snd_le ..
  have hu : Brush k (1+H) 1 L x:= (Brush.linearB (u:=1) L (hx'.le.trans h.small) (by simpa using hr) zero_le_one).climb (le_add_of_nonneg_right hC) le_rfl
  have ht:= Brush.reading L (hv.smaller (show k≤ k+2 by omega)) hr; rw [one_mul] at ht
  let f (x:ℝ×Xs):=(x.2,r x.2); have hw: Brush k (1+H+(1+H)) 1 f x:= hu.pair (ht.climb (le_add_of_nonneg_left zero_le_one) le_rfl)
  obtain ⟨hV,hH⟩:= h.color 0 0 x (by rw [norm_zero]; exact h.off) (by simp) ((_root_.norm_fst_le _).trans_lt hx) hx'
  rw [show Lantern.visit (orbit F ρ) 0 0 x=f x by simp [Lantern.visit,f]] at hV hH
  have hP:= Brush.reading L (h.gram x.2 hx').2 hr; rw [one_mul] at hP
  exact ⟨Lantern.composite hw (hV.smaller (by omega)), (Lantern.composite hw hH).gathering hP⟩

include hp hh hf
lemma plan_phase : FlatAt 2 (mainCover T F i ρ) 0:= by
  let U:= Uniform.paint F G; let g:= Lapis.combineH F (G:=G)
  let Y:= uncurry (tested F i T.high T.up)
  let f (x:ℝ×Xs):= U (g (x.2,r x.2)); have hx: f 0 = 0:= by
    have h0 : orbit F ρ 0 = 0:= Lapis.zeroO F T.up T.high ρ σ C p hp
    unfold f; change U (g ((0:Xs),r 0))=_; rw [h0,show ((0:Xs),0)=(0:Xs×Poll.Body (Precision.Key F G)) from rfl,map_zero,map_zero]
  have hV:=h.pos; have hR:= (h.curve 0 (by rw [norm_zero]; exact hV))
  have ht : ContDiffAt ℝ (↑(2:ℕ)) f 0:= U.contDiff.contDiffAt.comp _ (g.contDiff.contDiffAt.comp _ (contDiffAt_snd.prodMk ((hR.smaller (by omega : 2≤ k+2)).smooth.comp (f:=Prod.snd) (0:ℝ×Xs) contDiffAt_snd)))
  obtain ⟨hP,hZ,hE,hx'⟩:= price_identity F i hf hh.1
  change FlatAt 2 (Y ∘ f) 0
  apply FlatAt.comp _ _ ht; all_goals rw [hx]
  · intro i hi; interval_cases i
    · ext1 v; rw [iteratedFDeriv_zero_apply]; exact hZ
    ext1 v; rw [iteratedFDeriv_one_apply (𝕜:=ℝ), show fderiv ℝ Y 0=0 from hE]; rfl
  exact hP.of_le le_top

def sideFee (n k : ℕ) (b d : ℝ) := ritual_fee 2 n (readAt k b) 0 d+ritual_fee 0 n (readAt k b+b) 0 d
lemma channel (β:ℝ) (hb:0<β) (x:Xs) (hk:n+2<k) (hj:j≤k) (he : 1<a) (ht: a*gStep β≤u) (hx : ‖x‖<a*gStep β) : AuxStage.Points (sideFee n k H a) ((a*gStep β)⁻¹) (gStep β) n j (off A T F i ρ β) x (collector A T F i ρ):= by
  have hz :=gS β hb; have hu:0<a*gStep β:= mul_pos (zero_lt_one.trans he) hz.1; have hs:= ht.trans h.small
  let f:=mainCover T F i ρ; let g:=extra A T F i ρ
  have hf i (hi : i∈ball (0:ℝ×Xs) (a*gStep β)):= covers A T F _ ρ h (mem_ball_zero_iff.mp (ball_subset_ball ht hi))
  have hh : (gStep β)⁻¹^2=β:= by rw [inv_pow]; field_simp [hz.1.ne']; nlinarith [hz.2]
  have hQ : AuxStage.Points (ritual_fee 2 n (readAt k H) 0 a) (a*gStep β)⁻¹ (gStep β) n j (fun x:Xs=> ((gStep β)⁻¹)^2 * f (gStep β,x)) x (ritual (mainCover T F i ρ) 2):= ritual_P hk hj (((hf _ (mem_ball_self hu)).1.smaller hk.le).smooth) (plan_phase A T F i ρ p h hp (by assumption) (by assumption)) hz.1 he hs hx (fun x hx=>(hf x hx).1) (by rw [sub_self,zero_mul]; exact AuxCurtain.constant (u:=0) zero_le_one norm_zero.le)
  have hk': n+0<k:=by omega
  have hE := ritual_P hk' hj ((hf _ (mem_ball_self hu)).2.smaller hk'.le|>.smooth) (show FlatAt 0 g 0 from fun _ i=> (Nat.not_lt_zero _ i).elim) hz.1 he hs hx (fun x hx=> (hf x hx).2) (u:=0) (by rw [sub_self,zero_mul]; exact AuxCurtain.constant (u:=0) zero_le_one norm_zero.le)
  apply (hQ.add hE).adjust; refine Eventually.of_forall (fun i'=>?_); change _= (gStep β)⁻¹^2 * _ + (gStep β)⁻¹^0 * g _; rw [hh,pow_zero,one_mul]
  unfold f g off extra mainCover coverLog; ring
end YM.RGComparison01.AuxCover
