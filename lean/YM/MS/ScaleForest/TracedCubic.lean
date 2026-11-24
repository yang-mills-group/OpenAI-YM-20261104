import YM.MS.ScaleForest.SpinResolve
import YM.MS.ScaleForest.Angular
/-!
# Ghost/gluon projections at two cubic vertices, by *actual* sewing

Work on physical four-plane slice here; extension by `SpinResolve` as
appropriate. Throughout, momentum `p` external, `q` for the subsequent
integral loop, r the length scale on the bridge. Carry **actual** signs
and conventions of the quartic and cubic sectors. Reuse as much as possible
the specialized scaling calculation on these cubics; here we'll keep both
longitudinal and transverse probes and include the mask specifying which
bubble, as well as complete any required sums of these graphs. `beta`'s
projection doesn't account for the split here or Laurent pole insertion.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest.TwoPoint
open Function Filter Set Finset MeasureTheory Metric
open MS Plane Koszul Heat Flux Landau Tone Momentum Real Frame Wire Color Detect Native
open Book Convolve Logarithm Signal Landau.Detect.Mark Arts Motif Halo
open Rock Path Oceans Plum Alps Garment Arc Spin Train Pearl Dock Shine GraphSum
open City WilsonMS.BetaValue
open Complex (I)
open scoped Topology ContDiff BigOperators
variable {G : Gauge}

abbrev Km (r : ℝ) (S : Bool) : Rip G := pickLine S (radial G r)

variable (r : ℝ) (σ : Bool)

theorem selected_closed : closedF (Km (G:=G) r σ) false := by
  intro m a b q h; unfold Km pickLine at h; split at h; exact closure id (L_cl r) a b q h; contradiction

theorem selected_rev : reverseF (Km (G:=G) r σ) := by
  intro m i j q; unfold Km pickLine
  have hx := reverse_one (id : Momentum (L m)→_) (L_rev r) (fun _=>rfl) i j q
  change radial G r m i j (-q) = cross _ _ * radial G r m j i q at hx
  rw [hx]; by_cases he: radial G r m j i q=0; rw [he]; split_ifs <;> simp
  have hh := closure id (L_cl r) j i q he; rw [show parity i=parity j by grind]; split <;> simp

theorem Km0 (i j : BH G) : Km r σ 0 i j 0=0 := by unfold Km pickLine; split; exact line_zero ..; rfl

local notation "K₀" => Km (G:=G) r σ 0
local notation "℘" => HeatLine G r
local notation "γ" => field parity

private lemma ghost_degrees (l : Legs (Lane4 G)) : degree (field parity) l= if fieldDim ghostNo l%2=1 then true else false := by
  induction l with
  | nil => simp [fieldDim]
  | cons i w ih =>
    rw [degree_cons,field_cons,ih]
    rcases i with ⟨⟨⟨_ | i, _ | _⟩, u⟩, p⟩
    all_goals
      unfold ghostNo ghostChannel field parity Landau.p
      dsimp only
      split_ifs <;> first | rfl | omega

theorem cube_parity (p : SectorP 0) (i : Cfield G 0) (l : Legs (Lane4 G)) (ht : parity i ≠ degree (field parity) l) :
    Cubic G ((i,p)::l)=0 := cubic_charge _ (fun h=> by
      have he := ghost_degrees ((i,p)::l); rw [h, if_neg (by decide : ¬ (0:ℤ)%2=1),degree_cons] at he;
      unfold field at he; dsimp only at he; grind)

theorem hit_parity (l v : Legs (Lane4 G)) : HitM K₀ (Cubic G) l v =
    if degree (field parity) l=σ then HitM ℘ (Cubic G) l v else 0 := by
  unfold HitM
  rw [convertR (selected_rev r σ 0), convertR (law_S r)]
  have hu (i j : BH G) : radius parity K₀ i j (Cubic G) (Cubic G) l v = if degree (field parity) l=σ then
      radius parity ℘ i j (Cubic G) (Cubic G) l v else 0 := by
    unfold radius Km pickLine; dsimp only
    by_cases he : parity i=degree (field parity) l; · rw [he]; split <;> first| rfl|ring
    rw [cube_parity _ _ _ he]; split <;> simp
  simp_rw [hu]; split <;> simp

variable (p q : QP) (mu x y : Axis) (i a b : CI G)

def tridentMu (mu : Axis) (p q : QP) (x y : Axis) := trident (-(q+p)) q p x y mu

def twoG (r : ℝ) (p q : QP) (mu x y : Axis) : ℂ := ∑ u:Axis,∑ v:Axis, Lace r (q+p) u v *
  (tridentMu mu p q u x:ℂ)*(tridentMu mu p q v y:ℂ)

-- invariant color (NO A factors hidden)
theorem use_color (i a b k : CI G) : fColor k i a * fColor k i b = rune i a k * rune i b k := by
  rw [f_att,f_att,f_orient k i a,f_orient k i b]

theorem gauge_hit : HitM ℘ (Cubic G) [Detect.W x i q, Detect.W mu a p] [Detect.W y i (-q),Detect.W mu b (-p)] =
    2 * angle i a b * twoG r p q mu x y := by
  rw [clickWW,angle,Finset.mul_sum,Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _=> ?_
  unfold twoG; simp_rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _=> Finset.sum_congr rfl fun l _=> ?_
  rw [field_W k i a, field_W k i b, ← use_color,Lace_neg,
    show trident (q+p) (-q) (-p) l y mu= -trident (-(q+p)) q p l y mu from ?_]
  · unfold tridentMu; push_cast; ring_nf; rw [Complex.I_sq]; ring
  nth_rw 1 [← neg_neg (q+p)]; exact trident_flip ..

theorem ghost_hit : HitM ℘ (Cubic G) [Detect.C i q, Detect.W mu a p] [Detect.U x i (-q), Detect.W mu b (-p)] =
    if x=mu then 2* SpanH r (q+p) mu * angle i a b else 0 := by
  rw [hit_fade ℘ (law_S r),clickWC]
  change (1:ℂ) * _=_; rw [one_mul]; simp_rw [add_comm p q,Span_neg]
  simp_rw [show ∀ k:G.ColorIndex, Cubic G (Detect.C k (q+p):: [Detect.U x i (-q), Detect.W mu b (-p)])=_ from
    fun k=> wing_CUW k b i (q+p) (-p) mu x (-q) (by abel)]
  split
  · unfold angle; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _=> ?_; rw [f_att,f_att,angle_flip k a i]; ring
  simp

theorem angle_comm (i a b : G.ColorIndex) : angle i b a=angle i a b:= by simp only [angle,mul_comm]

theorem exchangeW : (2:ℂ)⁻¹ * Exchange K₀ [Detect.W x i q, Detect.W y i (-q), Detect.W mu a p,Detect.W mu b (-p)] =
    if σ then 0 else 2* angle i a b * (twoG r p q mu x y+twoG r (-p) q mu x y) := by
  let K := Km (G:=G) r σ 0
  obtain hx:= selected_rev (G:=G) r σ 0
  rw [book_exchange _ _ _ _ hx (by simp [net, Detect.W,qnote]),hit_light K hx _ _ _ (by simp [net,Detect.W,qnote]) (Km0 r σ), hit_parity, hit_parity]
  simp only [gauge_hit r p q mu x y i a b, show HitM ℘ (Cubic G) [W x i q,W mu b (-p)] [W y i (-q),W mu a p]= _ from
    (neg_neg p ▸ gauge_hit r (-p) q mu x y i b a), angle_comm i a b];
  cases σ
  · change ((2:ℂ)⁻¹) * (2 * ((0+1* (2* _ * twoG r p q mu x y)) + 1*1*(2* _ * twoG r (-p) q mu x y)))=_; rw [if_neg (by decide)]; ring
  change (2:ℂ)⁻¹ * (2 * ((0+1*(if false=true then _ else (0:ℂ)))+1*1*(if false=true then _ else (0:ℂ))))=_; simp

theorem exchangeC : (2:ℂ)⁻¹ * Exchange K₀ [Detect.C i q, Detect.U x i (-q), Detect.W mu a p, Detect.W mu b (-p)] =
    if σ=true ∧ x=mu then 2*angle i a b* (SpanH r (q+p) mu + SpanH r (q+ -p) mu) else 0 := by
  let K:=Km (G:=G) r σ 0; obtain hx:= selected_rev (G:=G) r σ 0
  rw [book_exchange _ _ _ _ hx (by simp [net,Detect.W,C,U,qnote]),hit_light K hx _ _ _ (by simp [net,C,U,qnote]) (Km0 r σ), hit_parity, hit_parity, ghost_hit,
      show HitM ℘ (Cubic G) [C i q,W mu b (-p)] [U x i (-q),W mu a p] =_ from (neg_neg p ▸ ghost_hit r (-p) q mu x i b a), angle_comm i a b]
  simp only [show ∀ b c : G.ColorIndex,∀ p q:QP,degree (field parity) [C b p,W mu c q]=true from fun _ _ _ _=> rfl,
    show ∀ b:G.ColorIndex,∀ q:QP, field parity (W mu b q)=false from fun _ _=> rfl,cross_false']; cases σ <;> by_cases h:x=mu <;> simp [h] <;> ring

-- transpose orientation for the final trace

theorem exchangeSym (u v : Lane4 G) (l : Legs (Lane4 G)) :
    Exchange K₀ (u::v::l)= cross (parity u.1) (parity v.1)*Exchange K₀ (v::u::l):= by
  exact (tree_sym (selected_closed r σ 0) (fund_one G 0).sym (fund_one G 0).sym) [] u v l
end YM.MS.ScaleForest.TwoPoint
