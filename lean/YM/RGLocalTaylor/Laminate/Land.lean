import YM.RGLocalTaylor.Laminate.Plot
/-!
# Panel for all priced scenarios. `column` billed before any masks/gauge.
 Includes payable weighted output (across ALL input marks & locations).
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


open PhysicalNext PhysicalNext.Repeat Lotus Daisy Greenbelt Blaze.March
namespace Laminate
open RG01.Survive Mayer Trees YM.Merge Palette

variable {ι: Type} [Fintype ι] (M':ι→Leaf R) (rA:ι→ℝ) (Ξ : Utopia H j v d r C' χ) (hP:Palette.Plot M' H rA)
    {α ρ e uJ vJ discount θ K : ℝ} {p : Molecule S} {M : ℕ}
set_option quotPrecheck false
local notation "a!" => Palette.sign M' S
local notation "K!'" => Tickets a!
local notation "l₀" => speedBill e uJ α j
abbrev packPrice (rA:ι→ℝ)(x:Finset ι) := ∏ i∈x,rA i
/-- printed receipt at this support, before orientation and growth in `ɑ` -/
abbrev launchFoot (Ξ : Utopia H j v d r C' χ)(p : Molecule S) (θ ρ α uJ e:ℝ)(M l:ℕ) := (∑ k:Tickets (Palette.sign M' S), packPrice rA k.val * Laminate.invoice (Palette.team M' k) p Ξ θ ρ α uJ e M l)
local notation "v_" => launchFoot M' rA
lemma layerFull (p:Molecule S) (he:authorized H p) : v_ Ξ p θ ρ α uJ e M l =
    l₀*(∏ j∈p,projectedWeight M' rA Ξ j) * (1+H.shapeW p)^(l+j) * marking H p * spreadRate M θ ρ^p.card:= by
  let s:= (1+H.shapeW p)^(l+j); let t:=marking H p; let w:=spreadRate M θ ρ^p.card
  unfold launchFoot projectedWeight; simp_rw [Tickets.expanded a! Ξ.fare (Palette.wages M' rA) p]; rw [mul_sum,sum_mul,sum_mul,sum_mul]; refine sum_congr rfl ?_
  intro k _; unfold Laminate.invoice budCost; simp only [he,true_and,Palette.label, Palette.worth];by_cases hx:k.reach⊆p
  · simp_rw [if_pos hx]; unfold Palette.wages; rw [prod_mul_distrib]; unfold packPrice; ring
  simp_rw [if_neg hx]; ring

local notation "reserve_" => width Q μ L s
abbrev first_price (Q : ConnectedActivityE6.Target G P) (L:Side) (μ s:ℝ) (l:ℕ) (z:ℝ) := Reserves.extract Q.ε l 0 0*Reserves.treeYield (z*width Q μ L s) (1/2) 0
local notation "τ" => spreadRate M θ ρ

variable (h : Awning H Ξ A b discount e uJ vJ k l) (he : Approved K θ j M)(hA:1≤α)(hρ:1≤ρ)
    (N : Captain H j C' d v Y A b r B q n χ)(hf:N.conduit=Ξ)
include h he hA hρ hP hf
lemma launch_nonneg (p : Molecule S): 0 ≤ v_ Ξ p θ ρ α uJ e M l := by
  subst Ξ; exact sum_nonneg (fun i _=> mul_nonneg (prod_nonneg (fun _ _=> hP.live _)) (invoice_check _ p h he hρ hA))

omit h he hA hρ hP hf in
private lemma speedP {e uJ α:ℝ} (he:0≤e)(hu:0≤uJ)(ha:1≤α):0 ≤ speedBill e uJ α j:=by unfold speedBill; positivity -- omit

variable (hx:degreePrice (radiusB s) (width Q μ L s) Q.δ ≤1/2)(hs:degreePrice (radiusB s) (spreadRate M θ ρ *width Q μ L s) Q.δ≤1/2)
include hx hs
lemma onSpace (w:ℝ)(hw:w≤Q.exp): Ac.Hit H.unionP (radiusB s) (fun p=> v_ Ξ p θ ρ α uJ e M l) w (l₀*first_price Q L μ s (l+j) τ) := by
  let E:= Mixed.lengths S (Q.costs L μ R.beta s C') (ConnectedActivityE6.lengths T R)
  have hE i:0≤ E i:= by rcases i with i|i; exact mul_nonneg Ξ.lives.extra (Nat.cast_nonneg _); exact Nat.cast_nonneg _
  let f:= projectedWeight M' rA Ξ; have ht:= paid_mark H f E (projected_pos M' rA Ξ hP) hE (rich M' rA Ξ hP hx) (zero_lt_one.trans_le (spread_pos hρ he.nonneg)) (fun i=>rfl) hs (l+j)
  have hz(p) := launch_nonneg M' rA Ξ hP h he hA hρ N hf p
  intro x; have hq:=speedP (j:=j) h.earn h.bSc hA; have hp:= budget_scale hq (ht x)
  refine budget_mono hp (fun i=>?_) (fun i=>?_)
  · split; next=> exact mul_nonneg (hz _) (Real.exp_pos _).le
    exact le_rfl
  dsimp only; split;
  next hh=>
    by_cases hV:authorized H i
    · apply le_trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hw (Nat.cast_nonneg _))) (hz i)); rw [layerFull M' rA Ξ i hV, if_pos ((H.attends i).2 hV.1)]; unfold f; apply le_of_eq;ring
    have hk : v_ Ξ i θ ρ α uJ e M l=0:= by unfold launchFoot Laminate.invoice; simp only [hV,false_and,↓reduceIte,mul_zero,sum_const_zero]
    rw [hk,zero_mul]; simpa only [if_pos hh] using hp.1 i
  simp [mul_zero]

abbrev offerBook (Ξ : Utopia H j v d r C' χ)(θ ρ α uJ e:ℝ)(M l:ℕ)(p:H.ThinP): ℝ:=2^j*((↑(M+2:ℕ):ℝ)*v_ Ξ p.val θ ρ α uJ e M l)
abbrev rent (Q:ConnectedActivityE6.Target G P)(L:Side)(μ s θ ρ α uJ e:ℝ)(j M l:ℕ):= Q.goal L s+(2^j*( (↑(M+2:ℕ):ℝ)*speedBill e uJ α j))*first_price Q L μ s (l+j) (spreadRate M θ ρ)
local notation "b'" => rent Q L μ s θ ρ α uJ e j M l
lemma installed {η w:ℝ} (hw:w+η ≤ Q.exp)(hη:0<η)(hg:degreePrice (radiusB s) b' η ≤1/2) : Trees.Ready H.smallAt (radiusB s) (offerBook M' rA Ξ θ ρ α uJ e M l) w b' η (1/2):= by
  have hh (p) := launch_nonneg M' rA Ξ hP h he hA hρ N hf p
  let p:= first_price Q L μ s (l+j) τ; let A:=(↑(M+2:ℕ):ℝ); let B:= (2:ℝ)^j; have hB:0≤B:=by unfold B; positivity
  have hA':0≤A:=Nat.cast_nonneg _
  have hp:= onSpace M' rA Ξ hP h he hA hρ N hf hx hs _ hw; have hz:0≤ l₀*p:= budget_nonneg (hp 0); have hg':0<Q.goal L s:=Daisy.arable H
  have hu:B*A*(l₀*p)≤b':= by rw [show b'=Q.goal L s+B*A*(l₀*p) by unfold rent; unfold B A p; ring]; linarith only [hg']
  refine ⟨add_pos_of_pos_of_nonneg hg' ?_,hη,hg,by norm_num,fun p=>mul_nonneg hB (mul_nonneg hA' (hh p.val)),fun x=>?_⟩
  · change 0 ≤ B*(A*l₀)*p; rw [← mul_assoc B A, mul_assoc (B*A)]; exact mul_nonneg (mul_nonneg hB hA') hz
  let f p:= v_ Ξ p θ ρ α uJ e M l
  have hf:= budget_scale (mul_nonneg hB hA') (budget_pull (fun i:H.ThinP=>Subtype.val i) Subtype.val_injective (hp x))
  convert! budget_loosen hf hu using 1; ext1 i; dsimp only; split
  next h'=> rw [if_pos (show x∈ H.unionP _ from h')]; unfold offerBook B A; rw [show H.smallAt i=H.unionP i.val from rfl]; ring
  next h'=> simp_rw [if_neg (show x∉ H.unionP _ from h'),mul_zero]
end Laminate
end YM.RGLocalTaylor
