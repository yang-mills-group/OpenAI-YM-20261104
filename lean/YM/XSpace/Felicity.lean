import YM.XSpace.Topaz
/-! # Replace Wilson cubic by twice the minus part

 Exact to explicitly controlled terms and an exact finite difference.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Gland
open Function Set Filter Relief Sail Trace Chart2 Outline Mu Lattice Chiral Finsupp
open scoped Topology BigOperators Pointwise Classical
variable {G:Gauge} {S:Levee G}
-- Θ char alignment at bare unconditioned first density
local notation "M" => beamD false
local notation "W" => G.ColorIndex
lemma omega_a (a b c:Axis): Ω a a b c=0:=by have h:= e₁ a a b c; linarith
lemma omega_b (a b c:Axis): Ω a b c c=0:=by have h:= e₃ a b c c; linarith
private lemma dagger₁ (u v:PlaqAxes): dotI (six u) (endr v)*dotI (endr u) (six v)=0:=by by_cases h:six u=endr v; have he:endr u≠six v:=(ne_of_lt ((show six v<endr v from v.property).trans (h ▸ (show six u<endr u from u.property)))).symm; simp [dot_at,he]; simp [dot_at,h]
private lemma dagger₂ (u v:PlaqAxes): dotI (six u) (six v)*dotI (endr u) (endr v)= if u=v then 1 else 0:=by by_cases h:u=v; simp [h,dot_at]; have he:six u≠six v∨endr u≠endr v:= not_and_or.mp (fun p=> h (Subtype.ext (Prod.ext p.1 p.2))); rcases he with he|he <;> simp [h,he,dot_at]
abbrev ωZ (p q:PlaqAxes):ℂ:=↑(Ω (six p) (endr p) (six q) (endr q))
lemma aligned (u v:PlaqAxes): (∑ i:P, M i (six u) (endr u)* M i (six v) (endr v))= (if u=v then 1 else 0)- ωZ u v:=by
  unfold beamD ωZ; simp_rw [← Complex.ofReal_mul,← Complex.ofReal_sum]; rw [split4 false,sign_neg,dagger₁,dagger₂]; split_ifs <;> push_cast <;> ring
-- atom from projected minus basis avoids tensor covariance
abbrev aimed (G:Gauge)(σ:Bool)(t:Name G) := starlit σ t * stance σ t
abbrev farMinus (G:Gauge): Stamp G:= ∑ i:Name G, aimed G false i
def sync (u v:PlaqAxes)(a:W):= harmonic (six u) (endr u) a* mode (six v) (endr v) a
def propArc (G:Gauge):Stamp G:= ∑ a:G.ColorIndex,∑ i:PlaqAxes,∑ j:PlaqAxes,ωZ i j • sync i j a
lemma reward : (∑ i:PlaqAxes, εglows i G)-farMinus G = propArc G:= by
  unfold εglows farMinus; rw [Finset.sum_comm,Fintype.sum_prod_type]; rw [Finset.sum_comm (s:=(Finset.univ:Finset P)) (t:=(Finset.univ:Finset W)), ← Finset.sum_sub_distrib]; unfold propArc; refine Finset.sum_congr rfl fun a _=>?_ ; change (∑ i:PlaqAxes,sync i i a)- _=_; unfold aimed starlit stance; simp_rw [Finset.sum_mul, Finset.mul_sum, smul_mul_smul]; change _-(∑ i:P,∑ u:PlaqAxes,∑ v:PlaqAxes, (M i _ _*M i _ _) • sync u v a)=_; rw [Finset.sum_comm (s:=(Finset.univ:Finset P))]; rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]; simp_rw [← Finset.sum_smul, aligned, sub_smul, ite_smul,one_smul,zero_smul, Finset.sum_sub_distrib]; simp
lemma order_poly {T:Type*}[AddCommMonoid T] (p:Axis→Axis→T) (h:∀ i,p i i=0) : (∑ j:Axis,∑ i:Axis,p i j)= ∑ o:PlaqAxes, (p o.val.1 o.val.2+p o.val.2 o.val.1):=by
  classical
  let L: Finset (Axis×Axis):= Finset.univ.filter (fun i=>i.1 < i.2)
  let X:Finset (Axis × Axis) := Finset.univ.filter (fun i=> i.2 < i.1)
  let Y:Finset (Axis × Axis) := Finset.univ.filter (fun i=> i.1≠i.2)
  have ht: Y=L ∪ X:= Finset.ext fun i=> by simp [Y,L,X]
  have hp (f: Axis × Axis →T):∑ i∈L,f i=∑ i:PlaqAxes, f i.val := by unfold L PlaqAxes; generalize_proofs hz; exact (Finset.sum_subtype_eq_sum_filter ..).symm
  have hh : Disjoint L X:= Finset.disjoint_left.mpr (by intro i h q; simp [L] at h; simp [X] at q; exact (not_lt_of_gt h) q)
  let F i:= p (i:Axis×Axis).1 i.2; have hv : ∑ i∈X,F i=∑ i∈L,F (Prod.swap i):= by
    have hx : X=L.image Prod.swap:= Finset.ext fun ⟨i,j⟩=> by simp [X,L]
    rw [hx, Finset.sum_image]; intro i _ j _ h; exact (Equiv.prodComm Axis Axis).injective h
  calc _ = ∑ i:Axis×Axis, F i:= (Fintype.sum_prod_type_right ..).symm
       _ = ∑ i∈Y,F i:= Eq.symm (Finset.sum_subset (Finset.subset_univ _) (fun i _ hb=> by simp [Y] at hb; simp [F,hb,h]))
       _ = _ := by rw [ht,Finset.sum_union hh,hv,hp,hp, ← Finset.sum_add_distrib]; rfl
abbrev omega (a b c d:Axis):ℂ:= Ω a b c d
def arc (a b c d:Axis)(w:W) := omega a b c d • (hike a (av b w)*mode c d w)
abbrev lump (b c d y:Axis)(w:W):= (omega b c d y) • (harmonic b c w* mode d y w)
lemma twinSum (a b c d:Axis) (w:W): arc a b c d w+ arc b a c d w=lump a b c d w:=by
  unfold arc lump omega; rw [e₁ b a,Complex.ofReal_neg,lit,sub_mul,smul_sub]; simp [sub_eq_add_neg]
lemma same_arc (a b c d:Axis)(w:W): lump a b d c w=lump a b c d w:=by unfold lump omega; rw [e₃ a b d c,Complex.ofReal_neg,winded d c]; simp
abbrev polyArc (G:Gauge): Stamp G:=∑ a:G.ColorIndex,∑ b:Axis,∑ i:Axis,∑ c:Axis,∑ d:Axis,arc b i c d a
lemma collects (G:Gauge): polyArc G=(2:ℂ) • propArc G:=by
  unfold polyArc propArc; rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro i _; let P (x y: Axis): Stamp G:=∑ c:Axis,∑ d:Axis,arc x y c d i; change ∑ x:Axis,∑ y:Axis,P x y=_; rw [Finset.sum_comm,order_poly P (fun i=>by simp [P,arc,omega,omega_a]), Finset.smul_sum]; apply Finset.sum_congr rfl; intro x _; unfold P; rw [← Finset.sum_add_distrib]; simp_rw [← Finset.sum_add_distrib, twinSum]; rw [Finset.sum_comm,order_poly (fun i' j :Axis=> lump (six x) (endr x) i' j i) (fun a=>by simp [lump,omega,omega_b]), Finset.smul_sum]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [same_arc (six x) (endr x) (six j) (endr j) i,two_smul];rfl
end YM.XSpace.Gland
