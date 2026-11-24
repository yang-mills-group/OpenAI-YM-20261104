import YM.XSpace.ImageSmall
import YM.XSpace.FarLines

/-!
# Large-even-side image and coincident estimates through fixed stencils

Use *all* center cells in the tilted box. Image separation and support
comparisons survive up to the seams, no nearest-other images in these configurations.
Scalars only before Wick comparison; apply to every polynomial input later. No
requirement of signed-coordinate rotation symmetry of center averaging. (Cost
of physical rotations in later scheme won't come from assuming uniform regulator
invariance.) Use `Blank` to keep every power earned.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Cross
open Lattice Filter Set Function Expense Further.FreeCovariance.KP Next.Rank Beamer Maxwell Asymptotics
open scoped Topology BigOperators
variable {G : Gauge} {ι : Type*} {u : Filter ι} {g : ι → Mesh} {x y : ι → Cover}

def Centered (u : Filter ι) (g : ι → Mesh) (x : ι → Cover) := ∀ᶠ i in u,
    (nodes (g i):ℤ)≤ 16*x i 0 ∧ 16*x i 0 ≤ 5*nodes (g i)

lemma near_sector {k : ℕ} (p : Mesh) (x : Fin k→Cover) (c : Four ℝ) (hc : c∈p.Box) (K : Set (Points k))
    (h : p.Fits K) (hp : p.rel x c ∈ K) (i : Fin k) : (nodes p:ℤ) ≤16*x i 0 ∧ 16*x i 0≤5*nodes p:= by
  have ht:= abs_le.mp (h _ hp i 0); have hs:-(p.spacing*nodes p/16)≤p.spacing*(x i 0:ℝ)-c 0 ∧ p.spacing*(x i 0:ℝ)-c 0≤ p.spacing*nodes p/16 := ht; have hq : p.spacing*nodes p/8≤c 0:=hc.1 0; have hg:c 0≤p.spacing*nodes p/4:=hc.2 0; have hv:=p.positive
  have he:(nodes p:ℝ)≤16*(x i 0:ℝ) ∧ 16*(x i 0:ℝ)≤5*nodes p:=by constructor <;> nlinarith [hs.1,hs.2];
  exact_mod_cast he

private lemma is_far {n : Side} (x : Cover) (h : (n.val:ℤ)≤ 16*x 0) (he : 4*x 0 ≤ 3*n.val): n.val ≤ 16*pdist (wrap n x):= by
  set y:=wrap n x
  have hv : (n.val:ℤ) ∣ (lift y 0)-x 0 := (ZMod.intCast_eq_intCast_iff_dvd_sub ..).mp (show ((↑(lift y 0):ZMod n.val)) = (↑(x 0):ZMod n.val) from congr_fun (wrap_lift _) 0).symm
  have kpos:=n.pos; have hp:= component_le y 0
  by_cases H : lift y 0=x 0
  · omega
  have hs:n.val ≤ (lift y 0-x 0).natAbs:= by
    apply Nat.le_of_dvd (by omega)
    exact_mod_cast (Int.natAbs_dvd_natAbs.mpr hv)
  omega

lemma separated_images (C : Stretched u g) (H : Centered u g x) (K : Centered u g y) (v w : Address G):
    ∀ᶠ i in u, let R:=(g i).p; let p := faceOf R (x i+v.1) v.2.1; let q:=faceOf R (y i+w.1) w.2.1;
      nodes (g i) ≤ 16*separation p.1 (R.reflectedFace q).1 :=by
  let d:= v.1+w.1+step w.2.1.val.1+step w.2.1.val.2
  have he (i) : (faceOf (g i).p (x i+v.1) v.2.1).1- ((g i).p.reflectedFace (faceOf (g i).p (y i+w.1) w.2.1)).1=wrap (g i).p.side (x i+y i+d):=by simp only [Period.reflectedFace,faceOf,d,map_add,wrap_step]; abel
  filter_upwards [H,K,C.horizon.eventually_ge_atTop (16*(d 0).natAbs:ℝ)] with i hi hv hd
  have ht : 16*(d 0).natAbs ≤ nodes (g i):= by dsimp only [sides] at hd; exact_mod_cast hd
  dsimp only; rw [separation,he]; apply is_far <;> (unfold nodes at ht hi hv;  simp only [Pi.add_apply]; omega)

/-- All powers of spacing. -/
def Blank (u : Filter ι) (g : ι → Mesh) {E : Type*} [Norm E] (f : ι → E) := ∀ j : ℕ, f=O[u] fun i=> a g i^j
namespace Blank
variable {E X : Type*} [NormedAddCommGroup E] {p q : ι → E}
lemma sum (F : X → ι → E) (s : Finset X) (h : ∀ i∈s,Blank u g (F i)): Blank u g (fun i=>∑ j∈s,F j i) := fun k=> IsBigO.sum (fun i hi=>(h i hi k))
lemma const_mul {E : Type*} [NormedRing E] {p : ι → E} (h : Blank u g p) (c : E): Blank u g (fun i=> c*p i) := fun k=> (h k).const_mul_left c
lemma add (h : Blank u g p) (p' : Blank u g q): Blank u g (p+q):= fun k=> (h k).add (p' k)
lemma zero (u : Filter ι) (g : ι → Mesh) : Blank u g (fun _=>(0:E)):= fun _=>isBigO_zero _ _
lemma squared {p : ι → ℝ} (h : Blank u g (p*p)): Blank u g p:=by
  intro k; refine IsBigO.of_pow (n:=2) (by decide) ?_; rw [pow_two p]; exact (h (k*2)).congr_right (by intro i; simp [pow_mul])
lemma anyPower {p : ι → ℝ} (h : Blank u g p) (d : ℕ): Blank u g (fun i=>(a g i)⁻¹^d *p i):= by
  intro k; apply (IsBigO.mul (isBigO_refl (fun i=>(a g i)⁻¹^d) u) (h (d+k))).congr_right; intro i; rw [pow_add, inv_pow, inv_mul_cancel_left₀ (pow_pos (actual g i) d).ne']
lemma first_order (h : Blank u g p):Rate u g p 0:=by unfold Rate; simpa using (h 1)
-- don't erase rates multiplying a bounded polynomial.
end Blank

def extra (p : Period) (x y : Cover) (i j : Address G):= Bare.image (R:=p) (faceOf p (x+i.1) i.2.1) (faceOf p (y+j.1) j.2.1) i.2.2 j.2.2
lemma img (C : Stretched u g) (hx : Centered u g x) (hy : Centered u g y) (v w : Address G): Blank u g (fun i=> extra (g i).p (x i) (y i) v w):=by
  apply Blank.squared; intro k
  apply IsBigO.trans _ (C.invertible k); refine IsBigO.of_bound 64 ?_
  filter_upwards [separated_images C hx hy v w, C.horizon.eventually_ge_atTop 64] with i hi he
  set l:=nodes (g i); change 64 ≤ (l:ℝ) at he
  set R:=(g i).p; let p:= faceOf R (x i+v.1) v.2.1; let q:=faceOf R (y i+w.1) w.2.1; let f:=extra R (x i) (y i) v w
  let b:=l/32; have hs:64≤l:= by exact_mod_cast he
  change l ≤ 16*separation p.1 (R.reflectedFace q).1 at hi
  have h₁: b+1≤separation p.1 (R.reflectedFace q).1:= by unfold b; omega
  have hp:b*f^2 ≤ 1:= Harmonic.decay R p q v.2.2 w.2.2 b h₁
  have hg:(l:ℝ)≤64*b:=by exact_mod_cast (show l≤64*b by unfold b; omega)
  have he:0<(l:ℝ):= by linarith
  change ‖f*f‖ ≤ 64* ‖(l:ℝ)⁻¹‖
  rw [Real.norm_of_nonneg (mul_self_nonneg f),Real.norm_of_nonneg (inv_pos.mpr he).le, ← div_eq_mul_inv, le_div_iff₀ he]; nlinarith only [hp,mul_le_mul_of_nonneg_left hg (sq_nonneg f)]

def self (i j : Address G) := if i.2.2=j.2.2 then (Top.coverLine i.2.1 j.2.1 (i.1-j.1)).re else 0
lemma contact (C : Stretched u g) (x : ι → Cover) (v w : Address G) : Blank u g (fun i=>lag (g i).p (x i) (x i) v w-self v w):=by
  unfold self; simp only [lag_spectral, add_sub_add_left_eq_sub (_ : Cover)]
  split_ifs with h
  · intro j; refine IsBigO.trans ?_ (C.invertible j); obtain ⟨K,hK,H⟩:= Top.cover_price v.2.1 w.2.1; let t:= ‖rcast (v.1-w.1)‖
    apply IsBigO.of_bound (K*(1+t)); filter_upwards with i; change ‖Complex.re _-Complex.re _‖≤ _*‖(sides g i)⁻¹‖
    rw [← Complex.sub_re]; apply le_trans (Complex.abs_re_le_norm _)
    rw [Real.norm_of_nonneg (inv_pos.mpr (counted g i)).le,← div_eq_mul_inv]; exact H _ _
  simp only [sub_self]; exact Blank.zero u g

-- same in finite linear tests (unscaled here)
lemma weighted_blank (F : Module.Dual ℝ (Horizon G)) (h : bright F) (f : ι→Address G→ℝ) (H : ∀ i, Blank u g (fun j=> f j i)): Blank u g (fun i=> F (f i)):= by
  obtain ⟨m,hm⟩:=h; simp_rw [hm]; exact Blank.sum (fun i j=>m i*f j i) m.support fun i _=> (H i).const_mul _
lemma pull_blank (P Q : Module.Dual ℝ (Horizon G)) (h : bright P) (hp : bright Q) (f : ι→Bridge G) (H : ∀ p q : Address G, Blank u g (fun i=> f i p q)): Blank u g (fun i=> mourn P Q (f i)):=
  weighted_blank P h (fun i k=>Q (f i k)) (fun k=>weighted_blank Q hp (fun i=> f i k) (H k))
end YM.XSpace.Cross
