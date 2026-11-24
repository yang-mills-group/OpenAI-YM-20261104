import YM.RGLocalTaylor.Laminate.Coincidence
import YM.RGLocalTaylor.Mayer.Full

/-!
# Local taylor coefficients including arbitrary finite marker histories.
 No `Accounts` used for pricing larger than actually available in the configuration,
 this applies even with other-mark coincidences packed to the same roster/head.
 One bill per *true* mark insert, not a volume price passing to clustering.
 Non-starting characters retain their full supports and margin through the last
 slot. Conserve both mandatory and seed and alarm cost prices. Adaptation of
 `Mayer.Wing`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {η r q a Y W d C' A b s μ C v B : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R}


open PhysicalNext PhysicalNext.Repeat Lotus Daisy Greenbelt
open Blaze.March
namespace Laminate
open RG01.Survive Mayer
variable (Q':Team R) (p : Molecule S)
local notation "U!" => p \ Q'.signs S

abbrev frontLoad := Mayer.original H p (p \ Q'.signs S) (partner Q' H)

def scopeM (H : Cash W s μ L Q o C T R) (M m : ℕ) : Config G c→ℝ := if Start p then coefficient p (p \ Q'.signs S) H (partner Q' H) χ M m else 0

def excess (H : Cash W s μ L Q o C T R) (M : ℕ) := (frontLoad Q' p (H:=H)).onLog H χ p - ∑ m:Fin (M+1), scopeM Q' p (χ:=χ) H M m

def column (H : Cash W s μ L Q o C T R) (M : ℕ) (u:Orders M) := if Q'.signs S⊆p then if u.val=M+1 then excess Q' p H (χ:=χ) M else scopeM Q' p H (χ:=χ) M u.val else 0

lemma passport (H : Cash W s μ L Q o C T R) (M : ℕ) (hx:Q'.signs S⊆p) : ∑ t:Orders M,column Q' p H (χ:=χ) M t=(frontLoad Q' p (H:=H)).onLog H χ p:= by
  rw [Fin.sum_univ_castSucc,show column Q' p H (χ:=χ) M (Fin.last (M+1))=excess Q' p H (χ:=χ) M from (if_pos hx).trans (if_pos rfl)]
  simp_rw [column,if_pos hx]; have hv (u:Fin (M+1)): (if u.val=M+1 then excess Q' p H (χ:=χ) M else scopeM Q' p H (χ:=χ) M u.val)=scopeM Q' p H (χ:=χ) M u.val:= by exact if_neg ((u: Fin (M+1)).isLt.ne)
  simp_rw [Fin.val_castSucc,hv]; unfold excess; rw [add_sub_cancel]

variable {M : ℕ} {θ K α discount e uJ vJ ρ:ℝ} {N : Captain H j C' d v Y A b r B q n χ} (h : Awning H N.conduit A b discount e uJ vJ k l) (he : Approved K θ j M) (ht : Q.goal L s ≤ K) (hρ:1≤ρ) (hr : ρ*Q.goal L s≤1)
    (hA:1≤α) (hb: (M+4:ℝ)*r ≤ α) (hh:vJ ≤ α) (hx:Q'.signs S⊆p)
set_option quotPrecheck false
local notation "f₀" => partner Q' H
local notation "w₀" => coverWeight Q' S
local notation "Ξ" => N.conduit
local notation "w₁" => (1+H.shapeW p)^(l+j)
local notation "v'" => speedBill e uJ α j
abbrev budCost (Ξ' : Utopia H j v d r C' χ) (α uJ e :ℝ) (l : ℕ) := speedBill e uJ α j * (Q'.weight*(∏ i∈ p\Q'.signs S, Ξ'.fare i) * (1+H.shapeW p)^(l+j))
def invoice (Ξ' : Utopia H j v d r C' χ) (θ ρ α uJ e :ℝ) (M l : ℕ) :=
    if authorized H p ∧ Q'.signs S ⊆ p then budCost Q' p Ξ' α uJ e l*marking H p*spreadRate M θ ρ ^ p.card else 0
local notation "c₀" => budCost Q' p Ξ α uJ e l
local notation "p₀" => invoice Q' p Ξ θ ρ α uJ e M l

private lemma blaze_eq : blaze U!=blaze p:= by
  suffices he: ∀ i, Sum.inr (.inr (.inr i)) ∉ Q'.signs S by
    ext i; simp only [blaze,mem_toRight,Finset.mem_sdiff,he,and_true,not_false_eq_true]
  intro i hi; have hh := support_eq hi
  exact notMem_empty _ (hh ▸ (show i∈blaze _ from mem_toRight.mpr (mem_toRight.mpr (mem_toRight.mpr (mem_singleton_self _)))))
private lemma speed_pos {e uJ α:ℝ} (he:0≤e)(hu:0≤uJ)(ha:1≤α):0 ≤ speedBill e uJ α j:=by unfold speedBill; positivity

include hx
lemma compartments : p \ (p \ Q'.signs S)= Q'.signs S:= by ext i; simp only [Finset.mem_sdiff]; constructor; rintro ⟨ht,hi⟩; exact not_not.mp (fun he=>hi ⟨ht,he⟩); intro h; exact ⟨hx h,fun ht=>ht.2 h⟩
lemma totalFace : hitFace Ξ p (p \ Q'.signs S) w₀ * (Ξ).rad^(blaze p).card= Q'.weight * (∏ i∈U!, (Ξ).fare i) := by
  unfold hitFace; rw [(Ξ).remixes, blaze_eq, compartments Q' p hx, coverTotal,mul_assoc]

variable (hg:authorized H p)
include h hh
omit hx in
private lemma affordPartners (i) (hi:i∈ Q'.signs S):EstFactor Ξ i (partner Q' H i) A (w₀ i) α:= by
  obtain ⟨i,hy,rfl⟩:= mem_image.mp hi; unfold coverWeight partner; rw [chosenAt Q' _ _ _ i hy,chosenAt Q' _ _ _ i hy]; exact (afford h i).weaken le_rfl hh

include hA hg he ht hr hb hρ
omit he ht hρ hr hx in
lemma mergedPrice : CoveredAt Ξ (frontLoad Q' p (H:=H)) p A (hitFace Ξ p (p \ Q'.signs S) w₀) α:= by
  let f i := if i∈U! then (Ξ).tag i else w₀ i
  rw [show hitFace Ξ p (p \ Q'.signs S) w₀=∏ i∈p,f i from ?_]
  · unfold frontLoad Mayer.original; refine EstFactor.product (zero_le_one.trans hA) hg.2 (w':=f) (fun i hi=> ?_);
    unfold f; split; next h'=> exact (h.estimates_leg (own p) i).weaken le_rfl ((le_mul_of_one_le_left (zero_le_one.trans (Ξ).active) (show (1:ℝ)≤ M+4 by linarith only [Nat.cast_nonneg (α:=ℝ) M])).trans hb)
    next h'=> exact affordPartners Q' h hh i (Classical.byContradiction fun h=>h' (mem_sdiff.mpr ⟨hi,h⟩))
  rw [← prod_sdiff (s₂:=p) (s₁:=U!) sdiff_subset]; unfold hitFace; exact congr_arg₂ (·*·) (prod_congr rfl fun i hi=> (if_neg ((mem_sdiff.mp hi).2)).symm) (prod_congr rfl fun i hi=>(if_pos hi).symm)

omit hx hh hg he ht hr hb hρ in
lemma c0check : 0≤ c₀ := mul_nonneg (speed_pos h.earn h.bSc hA) (mul_nonneg (mul_nonneg Q'.profit (prod_nonneg fun _ _=> (Ξ).fares _)) (pow_nonneg (add_nonneg zero_le_one (H.positive_volume p)) _))
omit hx hg hh ht hr hb in
lemma invoice_check : 0≤p₀:= by unfold invoice; split; exact mul_nonneg (mul_nonneg (c0check Q' p h hA) (zero_le_one.trans (marking_ge ..))) (pow_nonneg (zero_le_one.trans (spread_pos hρ he.nonneg)) _); exact le_rfl
omit he ht hρ hr in
lemma admissible (U:Config G c)(hf:(roster p).flags=∅)(hp:Healthy (Pressure.temp s) (H.unionP p) U) : Ore U ((frontLoad Q' p (H:=H)).onLog H χ p) v (c₀ * discount^(blaze p).card) j:= by
  have hz:= hitFace_nonneg (p:=p) (w:=w₀) (z:=U!) (fun i hi=> (partnerFit (H:=H) (j:=j) (i:=i) (compartments Q' p hx ▸ hi)).2) (Ξ)
  convert! h.priced (mergedPrice Q' p h hA hb hh hg) hz hA (fit_original p) hf U hp using 1
  unfold budCost; rw [← totalFace Q' p hx,mul_pow]; ring

omit ht hr hb hh in
lemma sticker : stipend Ξ p (p \ Q'.signs S) α uJ e discount (((M+1:ℕ):ℝ)*(θ*ρ)) l w₀ ≤ p₀:= by
  let v:=spreadRate M θ ρ
  have ht:1≤v:= spread_pos hρ he.nonneg
  have hν:=c0check Q' p h hA
  unfold stipend invoice; rw [if_pos ⟨hg,hx⟩]; push_cast
  calc
    _ = (c₀ * discount^(blaze p).card)*v^(p \ Q'.signs S).card:= by unfold budCost; rw [← totalFace Q' p hx,mul_pow]; unfold v spreadRate; ring
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left ((pow_le_one₀ h.nonneg h.small).trans (marking_ge ..)) hν) (pow_le_pow_right₀ ht (card_le_card sdiff_subset)) (pow_nonneg (zero_le_one.trans ht) _) (mul_nonneg hν (zero_le_one.trans (marking_ge ..)))
-- from Mayer/Wing
omit hh hb hA hr ht he hx in
private lemma receipt_edge (ht' : ¬Start p) (hD : discount≤(ρ^(M+1))⁻¹) (hE: Real.exp (-Q.mark L μ s)≤ (ρ^(M+1))⁻¹) :
    discount^(blaze p).card ≤ (ρ^(M+1))⁻¹ * marking H p:= by
  have hm := marking_ge H p
  rcases warns hg ht' with hz|hv
  · have hh := Real.exp_le_exp.mpr (show Q.mark L μ s ≤ Q.mark L μ s*(Cash.numP p:ℝ) from le_mul_of_one_le_right H.laws.acquired.marked (by exact_mod_cast hz)); rw [Real.exp_neg] at hE
    exact (pow_le_one₀ h.nonneg h.small).trans (le_trans (Eq.le (by rw [inv_mul_cancel₀ (Real.exp_pos _|>.ne')] : 1=(Real.exp (Q.mark L μ s))⁻¹*Real.exp (Q.mark L μ s))) (mul_le_mul hE hh (Real.exp_pos _).le (by positivity)))
  exact (show discount^(blaze p).card ≤ discount by simpa only [pow_one] using pow_le_pow_of_le_one h.nonneg h.small hv).trans (hD.trans (le_mul_of_one_le_right (by positivity) hm))


variable (hD: discount≤(ρ^(M+1))⁻¹) (hE: Real.exp (-Q.mark L μ s)≤ (ρ^(M+1))⁻¹)(hf:(roster p).flags=∅)
include hD hE hf
omit hg hx
lemma asked (u:Orders M)(U:Config G c)(hp:Healthy (Pressure.temp s) (H.unionP p) U) : Ore U (column Q' p H (χ:=χ) M u) v ((ρ^u.val)⁻¹*p₀) j := by
  let p0 := p₀; have hQ(i :ℕ) : 0 ≤ (ρ^i)⁻¹*p₀:=mul_nonneg (by positivity) (invoice_check Q' p h he hρ hA)
  let a' i:=coefficient p U! H f₀ χ M i; have ht'(hs:Start p):Start U!:= fun i hi=>hs _ (sdiff_subset hi)
  let g:= ((frontLoad Q' p (H:=H)).onLog H χ p)
  have hZero (hx: column Q' p H (χ:=χ) M u=0): Ore U (column Q' p H (χ:=χ) M u) v ((ρ^u.val)⁻¹*p₀) j :=by rw [hx]; exact fun E _ _ _ _ _ _ _=> Brush.zi EventuallyEq.rfl (hQ _) zero_le_one
  by_cases hw : Q'.signs S⊆p; swap; · exact hZero (if_neg hw)
  by_cases hg:authorized H p
  swap;
  · 
    have hz' (i:ℕ): Laminate.scopeM Q' p H (χ:=χ) M i=0:= by
      unfold Laminate.scopeM; split; next=> exact funext fun _=> Finset.sum_eq_zero fun i _=> Insert.onLog_of_forbidden hg ..
      next=>rfl
    apply hZero; unfold column Laminate.excess; simp_rw [hz', show ((frontLoad Q' p (H:=H)).onLog H χ p)=0 from funext fun V=> Insert.onLog_of_forbidden hg ..]; simp only [sum_const_zero,sub_self,ite_self]
  have hh'(i) (hi:i∈p\U!):=affordPartners Q' h hh i (compartments Q' p hw ▸ hi)
  have hv(i) (hi:i∈p\U!) := partnerFit (H:=H) (j:=j) (i:=i) ((compartments Q' p hw) ▸ hi)
  let t:=(ρ^(M+1))⁻¹; have hq:0≤t:=by unfold t; positivity
  have hW (ht' : Start p):= remainder_cost h he ht hr hh' (fun i hi=> (hv i hi).2) (fun i hi=>(hv i hi).1) sdiff_subset (show Start _ from (fun i hi=> ht' _ (sdiff_subset hi))) hb rfl hρ hA hf hp -- infer N
  have hz:= sticker Q' p h he hρ hA hw hg
  intro E _ _ _ V x hU hV
  unfold column Laminate.excess Laminate.scopeM; rw [if_pos hw]; split
  next h0 =>
    by_cases hu : Start p
    · simp_rw [if_pos hu]; rw [h0]; exact ((hW hu) E V x hU hV).climb (mul_le_mul_of_nonneg_left hz hq) le_rfl
    simp_rw [if_neg hu,sum_const_zero,sub_zero]; rw [h0]; apply (Laminate.admissible Q' p h hA hb hh hw hg U hf hp E V x hU hV).climb _ le_rfl
    have hm : discount^(blaze p).card ≤ t*marking H p:= receipt_edge p (N:=N) h hρ hg hu hD hE
    have ht:= spread_pos (M:=M) hρ he.nonneg; let s:= (spreadRate M θ ρ)^p.card; let m:= marking H p
    unfold invoice; rw [if_pos ⟨hg,hw⟩]; calc
      _ ≤ c₀*(t*m):=mul_le_mul_of_nonneg_left hm (c0check Q' p h hA)
      _ = t*(c₀*m):=by ring
      _ ≤ t*(c₀*m)*s:=le_mul_of_one_le_right (mul_nonneg hq (mul_nonneg (c0check Q' p h hA) (Real.exp_pos _).le)) (one_le_pow₀ ht)
      _ = _:=mul_assoc ..
  split
  next hχ=> refine (coeff_cost h he ht hr hh' (fun i hi=> (hv i hi).2) (fun i hi=> (hv i hi).1) sdiff_subset (ht' hχ) hb rfl hρ hA hf hp u.val E V x hU hV).climb (mul_le_mul_of_nonneg_left hz (by positivity)) le_rfl
  exact Brush.zi EventuallyEq.rfl (hQ _) zero_le_one
end Laminate
end YM.RGLocalTaylor
