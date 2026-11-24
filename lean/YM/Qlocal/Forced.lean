import YM.Qlocal.Regular
import YM.RGComparison01.Marks.Story

/-!
Real step: uniform *precalibration* forced exit price for arbitrary arrays
of Leaf (real signed, mixed marks, incl incoming forces, any sign, no q-rank restriction).
Same layout. Keeps the full `Palette` marked way for the narrow-step bills;
in particular not just vacuum term / not just absolutely estimating it as a constant.

Uses `CapK`-style common jet price before tests (`Paid` family). Adapted
from supplied `Comparison/Remainder/Watercourse` and `Medallion`, with credit
from `RGComparison01/Pledge.{Checks,Ringlet}` (Marks/...). Those proofs are from
different branches (incl conflicting restatements upstream), **do not** infer that
those entire sources compose in the checkout. Here NO inverse powers of g per
note are required to renew the credit -- budget at entry ≤ supplier's v₀ in Bench
(inverse also Geo at that stage when obtained from `Checks.bought`), forced
budget gets full seed reserve at that appointment. Needs applying on valid construction.

As for regular, we work before scaling the tags back to the announced
relative error factors. Works also at large marker count within this credit.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal
open Filter Function Lattice RG Wilson Finset MeasureTheory Matrix
open Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel
  Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03
  Animals Control Window Coat Footprint Pulse Itinerary Blaze Scroll Vine Polar Frond
  Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter Mixed Reserves
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider Gas
  Ursell Trees Height Sail PhysicalNext.Repeat.Lotus Team Merge
open AnalyticBridge VerifiedReset Collection Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open RGComparison01 RGComparison01.Pledge Checks Foreman Baked Palette Pillow Resin Season March
variable {G : Gauge} {ι Ω : Type} {c f L : Side} {S : StepData c f}
    {P : Teller G} {T : Tube G S} {R : RG.Rep G f}
    {W β μ C : ℝ} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
    {H : Cash W β μ L Q o C T R} {d r a e b kα δ : ℝ} {n j : ℕ} {χ₀ : Chi}


open Function Filter Lattice RG RG.Patch Pressure Ovens
open Mallow Motion Progress.DirectedRecipe Refrain Song
open Palette Blaze.March Multiple Ursell Trees Mixed Daisy OmitClusters Gas Switch

/- The analogue of CapK (and Motion.Pays). -/
abbrev WayK (Ω ι : Type) (G : Gauge) (n : Side) := Ω → ℝ → Finset ι → Code G n
structure UniformPays [Fintype ι] (A : Activities G c) (P : BudgetPoint)
    (K : WayK Ω ι G c) (w e : ℝ) : Prop where
  term x t : K x 0 t=A.K
  licensed x t T : t∈ Set.Icc (0:ℝ) 1 → (black A (K x t T)).ForcedFamily P
  credit : ∃ g:ℕ→ℝ, (∀ i,Paid (fun y:Ω × Config G c => fun t j=> K y.1 t j i y.2) (g i)) ∧
       Ac.Hit (fun i => (A.forced i).support) P.B g e w

lemma UniformPays.project [Fintype ι] {P:BudgetPoint} {A:Activities G c} {K:WayK Ω ι G c} (h:UniformPays A P K b a)(x:Ω): Motion.Pays A P (K x) b a:=by
 obtain ⟨v,hv,hV⟩:=h.credit
 refine ⟨h.term x,h.licensed x,v,fun i=>?_,hV⟩
 obtain ⟨q,h,H,hg⟩:= hv i; exact ⟨q,h,H,fun y=>hg (x,y)⟩

namespace MarkExit

variable (M : ι → Lotus.Leaf R) (N : Ω → ι → Lotus.Leaf R)
variable [Fintype ι] (Y:Cash W β μ L Q o C T R) (χ:Chi)
local notation "w'"=> Palette.sign M S
variable (h : Roster M N) (rA:ι→ℝ) (hp: ∀ i,0≤rA i)
def hue (p:Molecule S)(i:Tickets w') (Y':Ω×Config G c)(x:ℝ)(t: Finset ι) :=(∏ j∈ i.val,ways rA x t j)*act (N Y'.1) Y χ Y'.2 p (h.tickets S Y'.1 i)
include hp h in
lemma voice (p:Molecule S)(i:Tickets w'):
    Switch.Paid (hue M N Y χ h rA p i) (if i.reach ⊆ p then (∏ j∈i.val,wages M rA j)*∏ j∈p\i.reach,Y.text j else 0):=by
    have h₀(y:Ω): (h.tickets S y i).reach=i.reach:= by unfold Tickets.reach; change i.val.image (Palette.sign (N y) S)= _; rw [h.marks]
    split
    next hz=>
       let v:= ∏ j∈i.val,rA j; let z (y:Ω × Config G c):=v*act (N y.1) Y χ y.2 p (h.tickets S y.1 i); let w:= ∏ j∈p\i.reach,Y.text j
       have he : (∏ j∈i.val,wages M rA j)=v*(team M i).weight:=by rw [Palette.worth]; unfold Palette.wages; rw [prod_mul_distrib]
       have ht : 0≤ v:= prod_nonneg fun i _=> hp i; have hw:0≤ w:=prod_nonneg fun x _=> Y.positive x
       rw [he,mul_assoc]; apply Paid.congr (paidClick (ι:=ι) i.val (p:=z) (mul_nonneg ht (mul_nonneg (Team.profit _) hw)) (fun j=> ?_))
       · intro u x hz; ext v; unfold hue; rw [amplitudes]; unfold click z; split_ifs <;> ring
       unfold z; rw [norm_mul, Real.norm_of_nonneg ht]; apply mul_le_mul_of_nonneg_left _ ht; let g:= h.tickets S j.fst i
       have he:= act_norm (N j.fst) Y χ p (h.tickets S j.fst i) j.snd (show _ from h₀ j.fst ▸ hz)
       rw [h₀ j.fst] at he; exact he.trans (mul_le_mul_of_nonneg_right (Eq.le (h.weight_eq ..)) hw)
    next hz=>
       letI:Nonempty (Forest S.ratio):=Tree.select S.ratio S.patch.odd_side
       apply Paid.congr paidZero; intro u x hx; ext v; unfold hue; rw [show act (N u.1) Y χ u.2 p (h.tickets S u.1 i)=0 from Classical.byContradiction (fun he=>hz (h₀ u.1 ▸ (present (N u.1) Y χ u.2 (h.tickets S u.1 i) p (F:= Classical.ofNonempty) he).1)),mul_zero]; rfl
def polaroid (p:Molecule S):= fun u:Ω × Config G c=>vote (N u.1) Y χ rA p u.2
include hp h
lemma cameras (p : Molecule S): Paid (polaroid N Y χ rA p) (∏ i ∈p,toll M Y rA i):= by
   rw [show (∏ i∈p,toll M Y rA i)= _ from Tickets.expanded (Palette.sign M S) _ _ p]
   refine Paid.congr (Paid.sum univ _ _ (fun i _=> voice M N Y χ h rA hp p i)) ?_; intro u x hx; ext i
   simp only [Finset.sum_apply]; unfold hue polaroid vote color; rw [← Equiv.sum_comp (h.tickets S u.fst)]; rfl
lemma invites (p:Molecule S)(q:ℕ)(hn:q≤Cash.numP p): Paid (polaroid N Y χ rA p) (Palette.tune M Y rA q 0 p):=by
  rw [Resin.simpler M rA Y p]; split
  next hv=> exact cameras M N Y χ h rA hp p
  next hh'=>
    apply Paid.congr paidZero; intro x v hv; ext i; unfold polaroid Palette.vote Palette.color
    symm; refine Finset.sum_eq_zero (fun i _=> mul_eq_zero_of_right _ (show act (N x.1) Y χ x.2 p i = _ from ?_))
    by_contra hp
    letI : Nonempty (Forest S.ratio):= Tree.select _ S.patch.odd_side
    have ht:=(present (N x.1) Y χ x.2 i p (F:= Classical.ofNonempty) hp).2
    exact hh' ⟨ht.1,Nat.zero_le _,hn,Y.positive_volume p⟩
lemma accrued (i:Y.fragrances) : Paid (fun p:Ω×Config G c=> song (N p.1) Y χ rA i p.2) (lace M Y rA 0 i):=by
  let C: ℝ:=↑((i.1+1).factorial)
  let c:= coefficient Y.seam i.2/C
  have he: lace M Y rA 0 i= ‖c‖ *∏ j:Option (Fin i.1), tune M Y rA 0 0 ((i.2 j).val):= by
    unfold lace c C clusters; rw [Real.norm_eq_abs,abs_div, abs_of_nonneg (by positivity:0≤ (↑((i.1+1).factorial):ℝ))]; ring
  rw [he]; refine Paid.congr ((Paid.prod univ _ _ (fun (j : Option (Fin i.1)) _=> invites M N Y χ h rA hp ((i.2 j).val) 0 (Nat.zero_le _))).smul c) ?_
  intro U x hx; ext i'; unfold song Cash.trainedMill Gas.term; simp_rw [Pi.smul_apply,Finset.prod_apply,smul_eq_mul]; unfold c C; ring_nf; rfl
lemma accord (i:Y.Chapter) : Paid (fun p : Ω× Config G c=>fun t u=>Y.cologneMill (color (N p.1) Y χ p.2 (ways rA t u)) i) (grade Y.seam (fun i:Y.ThinP=>tune M Y rA 0 0 i.val) (fun i:Y.ThickP=>tune M Y rA 1 0 i.val) i) := by
   rcases i with i|i
   · exact invites M N Y χ h rA hp i.val 1 (Cash.forced_cost i.val i.prop.2)
   exact (MarkExit.accrued M N Y χ h rA hp i).neg

lemma porch (i:Y.Chainbook) : Paid (fun p:Ω×Config G c=> fete (N p.1) Y χ rA i p.2) (bold M Y rA 0 i):=by
  unfold bold; split
  next hi =>
    let d:= grade Y.seam (fun i:Y.ThinP=>tune M Y rA 0 0 i.val) (fun i:Y.ThickP=> tune M Y rA 1 0 i.val)
    let f j (p:Ω×Config G c) (t:ℝ)(u:Finset ι):=Y.cologneMill (color (N p.1) Y χ p.2 (ways rA t u)) j
    let F (j: ↥i.1) := (((↑((i.2 j + 1).factorial):ℝ)⁻¹) • (f j.val) ^ (i.2 j+1))
    let g := ∏ j,F j
    have hp : Paid g (manyW d i):= Paid.prod univ F _ fun j _=> by
      convert! ((accord M N Y χ h rA hp j.val).pow (i.2 j+1)).smul _ using 1
      simp [div_eq_mul_inv,mul_comm,d]
    refine Paid.congr (Paid.gate (X:={p:Ω×Config G c| Y.statesPool p.2 i}) hp) ?_
    intro U x _; ext p
    by_cases h:Y.statesPool U.2 i
    · rw [Set.indicator_of_mem (show U∈_ from h)]; unfold fete Cash.smilesMill; rw [if_pos ⟨hi.1,hi.2,h⟩]; unfold g manyW F; simp [f,div_eq_mul_inv,mul_comm]
    rw [Set.indicator_of_notMem (show U∉{p:Ω×Config G c| Y.statesPool p.2 i} from h)]; exact (if_neg (show ¬(_∧ _∧Y.statesPool U.2 i) from fun he=>h he.2.2)).symm
  next h=> refine Paid.congr paidZero (fun U x hx=>?_); ext i; exact (if_neg (show ¬(Y.Fresh _ ∧ Ac.Spark _ _ ∧ _) from fun y=> h ⟨y.1,y.2.1⟩)).symm


open Ovens
set_option quotPrecheck false
local notation "E0" => Q.mark L μ β
variable (b':BudgetPoint)(hx:b'.threshold=Pressure.temp β)(hz:b'.B=radiusB β)(γ:ℝ)(D:Match.Alliance Y Y 1 0)
local notation "VB" => (Beam.marquee Y b').read (Song.plusone Y D χ γ)
local notation "pay" => Real.exp (- E0)
variable {A B:ℝ}(hr:Resin.Ringlet Y M rA a e A B)
omit hp
include hx hz hr
theorem wages (hr₀:∀ x,Ringlet Y (N x) rA a e A B) : UniformPays (VB) b' (fun u=> Palette.shoot (N u) Y χ rA Y D) (pay*(2*B)) a:=by
  refine ⟨fun x=>(Story.forced (N x) rA Y D b' γ hx.symm (hr₀ x) hz).term,
    fun x=> (Story.forced (N x) rA Y D b' γ hx.symm (hr₀ x) hz).licensed,?_⟩
  let i:= Refrain.visa Y D; let u':=fun a: Refrain.Leaf Y=> bold M Y rA 0 a.val
  refine ⟨stuff i u',fun z=>?_, fun p=> ?_⟩
  · by_cases he:z∈Set.range i
    · obtain ⟨t,rfl⟩:=he; unfold i Palette.shoot shootK; simp_rw [stuffed]; exact porch M N Y χ h rA hr.pays t.val
    unfold Palette.shoot shootK; simp_rw [blank _ _ he]; unfold i at he; simp_rw [blank _ _ he]; exact paidZero
  refine transfer_budget i ?_ ?_ (budget_pull (fun i:Refrain.Leaf Y=>Subtype.val i) Subtype.val_injective (Resin.ern M rA Y hr p))
  · intro z; rw [stuffed,hz]; dsimp only; simp_rw [show ((VB).forced (i z)).support=_ from (Refrain.admitted Y D z).1]
    rfl
  intro j hj; rw [blank _ _ hj]; split; rw [zero_mul]; rfl
end MarkExit
end YM.Qlocal
