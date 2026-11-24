import YM.Contacts.Model.Dirge
/-! Generalize `VerifiedReset.Isotropic` from entire census
 to single hinge translation and across Side for Cover template. -/
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Model.Slope
open Function Lattice Finset Filter Set PhysicalNext.Repeat Pressure Wilson MeasureTheory RG
open Slide (Stars)
open Trio (froth Mirrors Offer)
open AnalyticBridge VerifiedReset Push.AbsoluteSums Animals
open StressFlux (extend_two sign)
open Averaging (axes01 ray)
open scoped Topology NNReal InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{n m:Side}{z r:ℕ}{V:Lattice.Support m}
variable (hG:G.Simple)
private lemma reframe_ray (p q : PlaqAxes) (s : Signed) (hs : s.perm p.val.1 = q.val.1) (ht : s.perm p.val.2 = q.val.2) :
    reframe (ray q (G:=G)) s = (sign s p.val.1 * sign s p.val.2) • ray p := by
  ext1 j
  simp only [reframe,ray,orderedDir,Pi.smul_apply]
  by_cases hp : j=p
  · subst j; simp [hs,ht,q.property,not_lt_of_gt q.property]
  have h₁ : (s.perm j.val.1, s.perm j.val.2) ≠ q.val := fun h => hp (by
    have := s.perm.injective; apply Subtype.ext; apply Prod.ext <;> apply this <;> grind)
  have h₂ : (s.perm j.val.2, s.perm j.val.1) ≠ q.val := fun h => by
    have ha : j.val.1 = p.val.2 := s.perm.injective (by grind)
    have hb : j.val.2 = p.val.1 := s.perm.injective (by grind)
    exact lt_asymm p.property (show p.val.2 < p.val.1 by rw [← ha,← hb]; exact j.property)
  simp only [Subtype.ext_iff]; split_ifs <;> simp_all
private lemma tests_quad (q : PlaqAxes → PlaqAxes → ℝ) (hG : G.Simple) (a b : PlaqAxes) (u v : ℝ) :
    quad q (u • (ray a (G:=G))) (v • ray b) = q a b * (u*v) := by
  rw [quad, Finset.sum_eq_single_of_mem a (Finset.mem_univ _)]; swap
  · intro x _ hx; simp [ray,hx]
  rw [Finset.sum_eq_single_of_mem b (Finset.mem_univ _)]; swap
  · intro y _ hy; simp [ray,hy]
  simp [ray,real_inner_smul_left,real_inner_smul_right,spike_norm hG,mul_comm v u]

include hG
lemma turns_isotropic (p:Site n→PlaqAxes → PlaqAxes → ℝ)(ht:∀ (s:Signed)(b x:Site n)(w z:Flux G), quad (p (affine s b x)) w z= quad (p x) (reframe w s) (reframe z s)) (o:Site n)(a b:PlaqAxes): p o a b=if a=b then p 0 axes01 axes01 else 0:= by
  have he (x y : Site n) (d e i j : PlaqAxes) (s : Signed) (hd : s.perm i.val.1=d.val.1 ∧ s.perm i.val.2=d.val.2)
      (he : s.perm j.val.1=e.val.1 ∧ s.perm j.val.2=e.val.2) :
      p y d e = p x i j * ((sign s i.val.1 * sign s i.val.2) * (sign s j.val.1 * sign s j.val.2)) := by
    have h := ht s (y - s.act x) x (ray d) (ray e)
    rw [show affine s (y-s.act x) x = y by simp [affine],reframe_ray _ _ s hd.1 hd.2,reframe_ray _ _ s he.1 he.2,tests_quad _ hG] at h
    simpa [h] using (tests_quad (p y) hG d e 1 1).symm
  split
  next h => subst b; obtain ⟨t,ha,hb⟩ := extend_two a.val.1 a.val.2 a.property.ne
            simpa only [sign,Bool.false_eq_true,if_false,mul_one] using he 0 o a a axes01 axes01 ⟨t,fun _ => false⟩ ⟨ha,hb⟩ ⟨ha,hb⟩
  next hn =>
    have H (x : Axis) := he o o a b a b (Signed.mirror x) ⟨rfl,rfl⟩ ⟨rfl,rfl⟩
    simp only [sign,Signed.mirror,decide_eq_true_eq] at H
    have ha := H a.val.1; have hb := H a.val.2
    have H1 := a.property; have H2 := b.property
    have he : a.val.1 ≠ b.val.1 ∨ a.val.2 ≠ b.val.2 := by grind
    simp only [↓reduceIte,if_neg H1.ne,if_neg (Ne.symm H1.ne),one_mul,mul_one] at ha hb
    rcases (show (a.val.1 ≠ b.val.1 ∧ a.val.1 ≠ b.val.2) ∨ (a.val.2 ≠ b.val.1 ∧ a.val.2 ≠ b.val.2) by grind) with ⟨h₁,h₂⟩|⟨h₁,h₂⟩
    · simp only [if_neg h₁,if_neg h₂,mul_one,mul_neg] at ha; linarith
    simp only [if_neg h₁,if_neg h₂,mul_one,mul_neg] at hb; linarith

variable (z)
def addr (o:Site m) : RegularAddress m:= ⟨o,neighbors z o,(neighbors_mem ..).2 (separation_self _ ▸ Nat.zero_le _)⟩
def deposit (f:Offer G m):=coeff (f 0) 0 axes01 axes01
omit hG
lemma plus_no (o:Site m)(h:2≤z): expand (addr z o)=neighbors z o := union_eq_left.mpr (by intro u hu; apply (neighbors_mem ..).2; rw [halo_spec] at hu; simp only [Finset.mem_singleton,exists_eq_left] at hu; exact hu.trans h)
lemma holds (o:Site m)(hu:10*z< m.val): Nonwrapping (neighbors z o) o:= by intro u hx; rw [separation_comm]; exact lt_of_le_of_lt (Nat.mul_le_mul_left 10 ((neighbors_mem ..).1 hx)) hu

variable {z}
variable {f:Offer G m}{B:BudgetPoint}(hr:∀ i,B.Regular (neighbors z i) (f i))
include hG hr
lemma holder (hz:2≤z)(hu:10*z< m.val)(hm:Mirrors f)(o: Site m)(a b:PlaqAxes): projection (addr z o) (f o) a b= if a=b then deposit f else 0:= by
   have ht : deposit f= projection (addr z 0) (f 0) axes01 axes01:=Eq.symm (by rw [projection,plus_no z 0 hz,if_pos]; rfl; exact holds z 0 hu)
   rw [ht]; refine turns_isotropic hG (fun o=>projection (addr z o) (f o)) (fun s b x w z'=>quad_moves (G:=G) _ _ (by omega) (Turn.circle_wind ..) (show (addr z (affine s b x)).site=_ from rfl) hG (hr x) (hr _) (funext fun i=>(hm x s b i).symm) w z') _ _ _
omit hr
lemma pages_eq {F:Story G}(he:LocalOn (Lattice.box z) F)(u: Site m)(v:Site n) {B':BudgetPoint}
   (hu:B.Regular (neighbors z u) (pass F m u))(hv:B'.Regular (neighbors z v) (pass F n v))
   (hy:2*z< m.val)(hx:2*z<n.val)(f:LinearJet G): logHessian (pass F m u) (f.field u) (f.field u)=logHessian (pass F n v) (f.field v) (f.field v):= by
      unfold logHessian; erw [← Work.F03.line_second (germ_diff hu) (flat_critical hG hu),← Work.F03.line_second (germ_diff hv) (flat_critical hG hv)]; apply congr_arg (iteratedDeriv 2 · 0); funext t; apply he; rintro ⟨x,b⟩ ha hd; change x∈_ at ha
      have e {m:Side}(u:Site m)(hy:2*z< m.val)(i:Axis) : VerifiedReset.coord u (wrap m x+u) i=(x i:ℝ):= by
         unfold VerifiedReset.coord; rw [add_sub_cancel_right,show lift (wrap m x)=x from lift_eq_iff.mpr ⟨rfl,fun i=> by have hx₁:= (box_test.mp ha).1 i; have hx₂:= (box_test.mp ha).2 i; omega⟩]
      apply congr_arg (fun w:G.Color=> G.lieExp (t • w) * 1); change f.field u (wrap m x+u,b)=f.field v (wrap n x+v,b); unfold LinearJet.field; simp only [e u hy,e v hx]
lemma includes {F:Story G}(he:LocalOn (Lattice.box z) F) (hu:B.Regular (neighbors z 0) (pass F m 0)) {B':BudgetPoint} (hv:B'.Regular (neighbors z 0) (pass F n 0)) (hy:2*z< m.val)(hx:2*z<n.val): deposit (pass F m)=deposit (pass F n):=by
   have hh:=pages_eq hG he 0 0 hu hv hy hx (wedge axes01 (spike G)); rw [label_color _ hG hu,label_color _ hG hv] at hh; simpa only [real_inner_self_eq_norm_sq,spike_norm hG,one_pow,mul_one,deposit] using hh
end YM.Contacts.Model.Slope
