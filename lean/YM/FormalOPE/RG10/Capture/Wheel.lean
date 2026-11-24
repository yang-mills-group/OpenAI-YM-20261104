import YM.FormalOPE.RG10.Capture.Skin

/-!
# One finite-horizon cylinder (before contour/stress conversion)

`Letters` such as the full field-address alphabet through h, compatible lifts and representatives.
Doesn't presume arity-1 completeness or a Maxwell basis. `Cylinder` and `Reading` bind a single
choice of generator/frame/detectors on THIS regulator, e.g. a finite-period approximant to the
unnormalized-primary and projection supply. Use only with the appropriate RG08 projection at that
horizon and compatibility with regulator limits from RG08/09. Lifts retained to permit π inputs
that remember counts and branches for gauge/period/path testing; using these stronger data does
not require assuming canonical merging on different kernel supports.

`Reading` prepares a given finite cutoff computation, requiring identities THOUGH all formal
orders (cross-step budgets on answers needed only at requested orders), acceptable when the germ
data are themselves full series. No need for cross-cutoff choice in this layer. `progress` yields a
one-mark kernel with its additional data propagated; not asserting existence for arbitrary cover
auxiliaries or choice independence. Act neither in amplitude nor at real coupling.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Capture
open PowerSeries Finset Function Route Transit
open scoped Topology BigOperators Classical
variable {U T J : ℕ → Type} {K:ℕ→Type*} {ι α : Type*} {X : Type}
    [∀ i,AddCommGroup (K i)] [∀ i,Module Series (K i)]
local notation "Γ" => ι → Series

structure Cylinder (T U : ℕ → Type) (K : ℕ→Type*) (α ι : Type*)
    [∀ i,AddCommGroup (K i)] [∀ i,Module Series (K i)] where
  prints : ∀ i,K i→ₗ[Series] Skin T U α i
  carry : ∀ i,K (i+1) →ₗ[Series] K i
  column : ∀ i,(ι→Series) →ₗ[Series] K i
  probe : ∀ i,K i→ₗ[Series] (ι→Series)
  iso : ∀ _i:ℕ,(ι→Series)≃ₗ[Series](ι→Series)

namespace Cylinder
variable [hiT : ∀ i,Fintype (T i)]
    (F : Fibers T) [∀ i,Fintype (J i)] (V : Voyage U J) (W : Scale X U) (h s N : ℕ)
    (Z : Cylinder T U K α ι)

structure Reading (F : Fibers T) (V : Voyage U J) (W : Scale X U) (h s N : ℕ) (Z : Cylinder T U K α ι) : Prop where
  tests i (he : i∈Ico s N) A : Z.prints i (Z.carry i A) = upwards F W h i V (Z.prints (i+1) A)
  weave i (he : i∈Ico s N) v : Z.carry i (Z.column (i+1) v) = Z.column i (Z.iso i v)
  measures i (he : i∈ Icc s N) v : Z.probe i (Z.column i v) = v

def spin (i j : ℕ) : K j →ₗ[Series] K i := match j with
  | 0 => if h:i=0 then h ▸ LinearMap.id else 0
  | k+1 => if h : i=k+1 then h ▸ LinearMap.id else (spin i k).comp (Z.carry k)
def roll (i j : ℕ) : (ι → Series) ≃ₗ[Series] (ι → Series) := match j with
  | 0 => LinearEquiv.refl ..
  | k+1 => if i=k+1 then LinearEquiv.refl .. else (Z.iso k).trans (roll i k)
variable {i j k : ℕ}
omit hiT
lemma spin_next (h:i ≤ j) (v : K (j+1)) : Z.spin i (j+1) v= Z.spin i j (Z.carry j v) := by rw [spin,dif_neg (show i ≠ j+1 by omega)]; rfl
lemma roll_next (h:i ≤ j) (v : Γ) : Z.roll i (j+1) v= Z.roll i j (Z.iso j v) := by rw [roll,if_neg (show i ≠ j+1 by omega)]; rfl
@[simp] lemma spin_self (v:K i) : Z.spin i i v=v := by cases i<;>simp [spin]
@[simp] lemma roll_self (v:Γ) : Z.roll i i v=v := by cases i<;>simp [roll]
lemma spinning (h:i ≤ j) (h':j≤k) (x : K k) : Z.spin i k x= Z.spin i j (Z.spin j k x) := by
  induction k,h' using Nat.le_induction with
  | base=> simp
  | succ k h₁ ih=> rw [Z.spin_next (h.trans h₁),Z.spin_next h₁,ih]
lemma rollNow (h:i ≤ j) (h':j≤k) (x : Γ) : Z.roll i k x= Z.roll i j (Z.roll j k x) := by
  induction k,h' using Nat.le_induction generalizing x with
  | base=> simp
  | succ k h₁ ih=> rw [Z.roll_next (h.trans h₁),Z.roll_next h₁,ih]


def restore (φ : α) (b i : ℕ) : K i →ₗ[Series] Channel (U i) := (fingerprint φ W h b i).comp (Z.prints i)

-- compensation equation uses ≤ only. names to prevent taking hypothesis through wrong warp
variable {W F V h s N Z}
variable (H : Reading F V W h s N Z) (φ : α)
include H
include hiT
lemma Reading.smearing (b : ℕ) (h₁:s ≤ i) (h₂ : i ≤ j) (hN : j ≤ N) (P : K j) :
    V.yield i j (restore W h Z φ b j P)= restore W h Z φ b i (Z.spin i j P) := by
  induction j,h₂ using Nat.le_induction with
  | base=> simp [Voyage.sameHere]
  | succ j hm ih=>
    rw [Z.spin_next hm, V.send_next hm,← ih (by omega)]
    congr 1; unfold restore; dsimp only [LinearMap.comp_apply]; rw [H.tests j (mem_Ico.mpr ⟨h₁.trans hm,hN⟩), regroup]
lemma Reading.transaction (h₁:s ≤ i) (h₂ : i ≤ j) (hN : j ≤ N) (v : Γ) :
    Z.spin i j (Z.column j v) = Z.column i (Z.roll i j v) := by
  induction j,h₂ using Nat.le_induction generalizing v with
  | base=> simp
  | succ j hm ih => rw [Z.spin_next hm, Z.roll_next hm,H.weave j (mem_Ico.mpr ⟨h₁.trans hm,hN⟩), ih (by omega)]
omit H

variable (W h Z) {b : ℕ}
/-- Coordinates at b, before restoring. -/
def designated (R : K b) (s:ℕ) := (Z.roll s b).symm (Z.probe s (Z.spin s b R))
/-- Report full-output-vector prescription, to measurement k in its scale. -/
def report (R : K b) (s k : ℕ) := nominal ((W.μ b/W.μ k)^h) • (Z.roll s k).symm (Z.probe s (Z.spin s b R))

/-- Top with dimensionless engineering at k, roots globalized independently with the chosen
output probe φ. This is the auxiliary replacement, NOT a singleton given spectral field. -/
def coupon (k N : ℕ) (v : Γ) : Channel (U N) := restore W h Z φ k N (Z.column N ((Z.roll k N).symm v))
lemma coupon_impl (k : ℕ) (v : K b) : nominal ((W.μ b/W.μ k)^h) • restore W h Z φ k b v=restore W h Z φ b b v := by
  unfold restore fingerprint; dsimp only [LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]; rw [smul_smul];
  have hk:= W.positive k; have hb:=W.positive b
  rw [price,price, ← product_nom]; congr 1
  congr 1; simp_rw [div_pow]; field_simp
variable {W h Z}
include H
variable (hsb:s ≤ b) (hk:b ≤ k) (hN:k ≤ N) (R:K b)
include hsb hk hN
lemma Reading.meant : V.yield b N (coupon W h Z φ k N (report W h Z R s k)) = restore W h Z φ b b (Z.column b (Z.designated R s)) := by
  rw [coupon, ← Z.coupon_impl W h φ k, H.smearing φ k hsb (hk.trans hN) le_rfl,H.transaction hsb (hk.trans hN) le_rfl]; -- order inspect
  unfold report
  simp_rw [map_smul]; congr 3
  have he (w:Γ): Z.roll b N w=Z.roll b k (Z.roll k N w):=Z.rollNow hk hN w
  rw [he,LinearEquiv.apply_symm_apply]; unfold designated; apply (Z.roll s b).injective
  rw [← Z.rollNow hsb hk,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]

lemma Reading.residual (F : Channel (U N)) (hf : V.yield b N F=restore W h Z φ b b R) {t : ℕ} (hs:s ≤ t)(ht:t ≤ b) :
    V.yield t N (F-coupon W h Z φ k N (report W h Z R s k)) = restore W h Z φ b t (Z.spin t b (R-Z.column b (Z.designated R s))) := by
  rw [V.follows ht (hk.trans hN), map_sub (V.yield b N), hf,H.meant φ hsb hk hN R,← map_sub, H.smearing φ b hs ht (hk.trans hN)]

omit hk hN in
lemma Reading.zero_final (hb : b ≤ N) : Z.probe s (Z.spin s b (R - Z.column b (Z.designated R s)))=0 := by
  rw [map_sub,H.transaction le_rfl hsb hb,map_sub,H.measures s (mem_Icc.mpr ⟨le_rfl,hsb.trans hb⟩), designated,LinearEquiv.apply_symm_apply, sub_self]
end Cylinder
end YM.FormalOPE.RG10.Capture
