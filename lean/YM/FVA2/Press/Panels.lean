import YM.FVA2.Press.Prefix
/-!
# Stencils on the top Wilson prescription, and their rank fit
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Press
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Labels Source Source.Drops Bid Work XSpace
open MS MS.Koszul MS.Cylinder Lab MS.Native MS.Native.Sew MS.Book MS.Local.Physical MS.Rake MS.Lifting MS.Theater
open scoped BigOperators Topology ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge} {d:ℕ} {H:Hol G} (A:XSpace.Survey G H d)
local notation "E" => tilt A
local notation "P" => Labels.Pol G
local notation "ζ" => Subtype.val (p:=fun x: Edge Cover=>x∈ knots A)
-- Fits and rank property before applying to real forms
variable {p:Labels.Pol G} {u r:ℕ}
theorem ranks (hd:u≤d)(h:Theater.At p (u,r)) : From (sat A p).val r ∧ Fits (sat A p) (Theater.orbit G p) r u false := by
 let q(b:ℕ×ℕ)(p: Pol G): Prop := b.1 ≤ d → From (sat A p).val b.2 ∧ Fits (sat A p) (Theater.orbit G p) b.2 b.1 false
 refine axisI q (p:=p) h (fun c hu=>?_) (fun i hi=>?_) (fun x i f ht ih h=>?_) (fun x f g hf hg ih hk h=>?_) hd
 · rw [sat_constant,cus]; refine ⟨ ?_,?_⟩; · exact fun l hi=> by change (↑l.length:ℤ)<0 at hi; omega
   rw [show coin c=(c • coin (A:=MS.Landau.Lane4 G) (1:ℂ)) from funext (?_ : ∀ l, _ )]; · exact Fits.unit.smul c
   intro l; cases l; exact (mul_one c).symm; exact (mul_zero c).symm
 · rw [sat_zero,map_zero]; exact ⟨fun _ _=>rfl,Fits.zero _⟩
 · have h': generation i + x.1 ≤ d:= h; have hk:= ih (by omega); have hv: From (Integration.mounted A i).val 1:= by
      intro l hl; match l with
      | _::_=> simp at hl; omega
      | []=> simp [Integration.mounted,Sew.art,region,Integration.box0]
   rw [sat_l,bags]; change From _ (↑(1+x.2:ℕ):ℤ) ∧ Fits _ _ (1+x.2) ((generation i+x.1:ℕ):ℤ) false; unfold generation; push_cast; exact ⟨hv.pair hk.1,(Integration.field_Fit A i (by unfold generation at h'; omega)).take hk.2 hv hk.1⟩
 rw [sat_add,map_add]; exact ⟨(ih h).1.add (hk h).1,(ih h).2.add (hk h).2⟩
-- pre-test using exact same real fields as in `XSpace.Initialize` before W subtraction
variable (p) {n:Side}
def offered (n:Side)(x:Config G n): ℝ:= (wheel A p (expandAt 0 x)).re
lemma continuous_offered : Continuous (offered A p n):= by
 let f:= fun u: Config G n=> mapped A.looks (expandAt 0 u)
 exact Complex.continuous_re.comp ( ( Work.G05.snap_read_smooth d p ω ).continuous.comp (A.recover_smooth.continuous.comp (show Continuous f from continuous_pi (fun i=> (Slot.cont (A.looks i)).comp ( continuous_pi (fun j=> continuous_apply ..) )))))
lemma woke (h : p ∈ Labels.invariantSpace G) : Lattice.GaugeInvariant (offered A p n) := by
 intro u x; unfold offered; rw [expandAt_gauge]; exact congr_arg Complex.re (colored A p h _ _)
lemma thread_eq : offered A p n ∘ (Chart.nation (G:=G) («P»:=Site n))= pigment A p ∘ Sew.pull (G:=G) (Sew.thread (wrap n) ζ):= by
    funext x; unfold offered pigment wheel window; simp only [comp_apply,wheel]; rw [show mapped A.looks (pad A (Sew.pull (Sew.thread _ _) x))= _ from (looks ..).symm, reflecting]; rfl
lemma hot_σ : MS.Cylinder.Taylor.germ (offered A p n ∘ (Chart.nation (G:=G))):= by rw [thread_eq]; exact ( ( pigment_hot A p).comp (f:=⇑(Sew.pull (Sew.thread (wrap n) ζ))) (ContinuousLinearMap.contDiff ..)).contDiffAt
lemma billed : enters n (dot A p)= MS.Native.reads (offered A p n ∘ Chart.nation):= by rw [thread_eq]; exact Sew.enters_gorge _ _ (pigment_hot A p).contDiffAt
variable (h:p ∈ Labels.invariantSpace G)
/-- not assuming support-nonwrapping or metrics. -/
def page (p:P)(h:p∈Labels.invariantSpace G): Change.Stencil (dot A p) where
 obs:= offered A p
 gauge _:= woke A p h
 smooth _:= hot_σ A p
 continuous _:= continuous_offered A p
 billable _:= billed A p
variable {p}
lemma awake (hp:p∈Film0 G u r)(hh:u≤d): Studio.Aura (dot A p) r ∧ Fits (dot A p) (Theater.orbit G p) r u false:= by
 obtain ⟨hl,h0,h⟩:=(Theater.cinema p).mp hp; let w:= page A p h0; have ht:= ranks A hh hl; rw [sat_real A p h] at ht
 refine ⟨⟨ht.1,?_,?_⟩,ht.2⟩
 · exact MS.Native.Tune_port _ (pigment A p) (pigment_hot A p).contDiffAt
 intro k; exact ⟨offered A p k, Chart.when_invariant (w.gauge k), w.smooth k,w.billable k⟩
end YM.FVA2.Press
