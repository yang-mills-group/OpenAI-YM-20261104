import YM.SharpGram.Annulus.Glass

/-!
# A Schur-step quantitative comparison contract

Eliminate lower-degree fields at both annular endpoints using their OWN
Gram. Don't assume quantitative full triangular matrix or fix/identify
Kabsch orientation. Use the *actual two-point physics* form and transport
ONLY this normalized quotient. Emit both directions. Equivalent to testing
a finite point Gram matrix through degree `d+1` at length pair exp(-n),
exp(-(n+1)), in the (actual, unselected state) normalized scale units, and
recording near-unit normalized R's (Löwner sense) on the independent
physical quotient. (Require separately d=0 step.) Consumers don't infer it
from an order zero estimate even around a radius ~ Lenses.Mantle.radius, much
less sporadic probes outside these dyads.

Weaker than assuming already-working point comparisons in a field basis with
uniform 1/(n+1) accurate near-isometry of the step; doesn't price rotations
or shear to lower dimensions. Affiliation with any RG03..05 result needs an
explicit payment of this rate AFTER residuals. Open hypothesis; nontrivial
matrix anchors unconditional in Glass (`strictSmall`); orientation not needed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram.Annulus
open Function Set Filter MeasureTheory Analysis Extraction Table Ward Climb RG Lattice
open Org Spec Next.UVStress Lenses Push.FiniteDetection.Free Weak.Portfolio
open scoped Topology ContDiff BigOperators Classical NNReal InnerProductSpace
set_option quotPrecheck false
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}{u:Filter (ℕ×ℕ)}
variable (F:Final C f S)
local notation "V!"=>F.sector.derivatives
local notation "σ"=>F.room.kernel.spin
variable {d : ℕ}
local instance (d : ℕ) : FiniteDimensional ℝ (S.Field d) := Module.Finite.trans ℂ _

-- scalar radius and time units
abbrev epoch : ℝ := Real.exp 1
abbrev plank (n : ℕ) := Real.exp (-(n:ℝ))
lemma plank_power (n : ℕ) : plank n = epoch⁻¹ ^ n := by
  rw [← Real.exp_neg,← Real.exp_nat_mul]; ring_nf
lemma epoch_ge : 1 < epoch:= by unfold epoch; norm_num
lemma plank_less (n : ℕ) : plank (n+1) ≤ plank n := Real.exp_monotone (neg_le_neg (by gcongr; omega))
lemma plank_limit : Tendsto plank atTop (𝓝 0) := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)

abbrev roomRate (d : ℕ) (n : ℕ) := form S σ d (plank n)
abbrev Valid (d n : ℕ) := positiveForm S σ d (plank n)

-- dual solving relative positive form, only numeric with Valid; default off-tail
-- LinearMap over REAL underlying for stable ellipse computations.
private def service (T : RealForm (S.Field d) (S.Field d)) : S.Field d →ₗ[ℝ] Module.Dual ℝ (S.Field d) :=
  LinearMap.mk₂ ℝ (fun x y=>T x y) (fun x y z=>by simp) (fun c x y=>by simp) (fun _ _ _=>by simp) (fun _ _ _=>by simp)
private lemma viable (n d:ℕ)(he:Valid F d n) : Bijective (service (S:=S) (roomRate F d n)):=by
  let M:=service (S:=S) (roomRate F d n)
  have hp : Injective M:= by
    apply LinearMap.ker_eq_bot.mp
    refine LinearMap.ker_eq_bot'.mpr fun x hx => by
      by_contra! hg
      have ht : roomRate F d n x x=0:= LinearMap.congr_fun hx x
      exact absurd ht (he x hg).ne'
  exact ⟨hp,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by change _=Module.finrank ℝ (Module.Dual ℝ _); rw [Subspace.dual_finrank_eq])).1 hp⟩

def liftA (d : ℕ) : S.Field d →ₗ[ℝ] S.Field (d+1):= ((V!).rise (Nat.le_succ d)).restrictScalars ℝ
private def serviceHigh (n d:ℕ) : S.Field (d+1) →ₗ[ℝ] Module.Dual ℝ (S.Field d):=
  (LinearMap.dualMap (liftA F d)).comp (service (S:=S) (roomRate F _ n)) -- check

def floorAt (d n:ℕ) : S.Field (d+1) →ₗ[ℝ] S.Field d := if he: Valid F d n then
    (LinearEquiv.ofBijective _ (viable F n d he)).symm.toLinearMap.comp (serviceHigh F n d) else 0
def cap (d n:ℕ) : Module.End ℝ (S.Field (d+1)) := LinearMap.id - (liftA F d).comp (floorAt F d n)
abbrev life {d:ℕ} (n:ℕ) (x:S.Field d) := Real.sqrt (roomRate F d n x x)
def charge {d:ℕ} (n:ℕ) (x:S.Field (d+1)) := life F n (cap F d n x)
lemma reflects_life (x:S.Field d) (n) : life F n (liftA F d x) = life F n x :=
    congr_arg Real.sqrt (inherit F.room.kernel (V!) F.phase.transport.injection F.phase.transport.rights (Real.exp_pos _) (Nat.le_succ d) x x).symm
lemma life_add (x y : S.Field d) {n} : life F n (x+y) ≤ life F n x + life F n y:= by
  let h:=roomRate F d n
  have ha (x:S.Field d):0≤ h x x:= positive F.room.kernel (Real.exp_pos _) x
  have he (x:S.Field d): life F n x ^ 2=h x x:=Real.sq_sqrt (ha x)
  let a:=life F n x; let b:=life F n y
  have hx : 0≤ a:=Real.sqrt_nonneg _;have hy :0 ≤ b:=Real.sqrt_nonneg _
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (add_nonneg hx hy)).mp
  have hv : h x y=h y x:= symmetric F.room.kernel (Real.exp_pos _) x y
  have ht : h (x+y) (x+y)=h x x + h y y + (h x y + h x y) := by simp only [map_add,_root_.add_apply,hv]; ring
  have hl (c:ℝ) := ha (c • x + y)
  have hp : h x y ≤ a*b := by
    have hg (c:ℝ) : 0 ≤ c^2 * a^2 + (2 * c * h x y) + b^2 := by
       specialize hl c; simp only [map_add,_root_.add_apply,map_smul,_root_.smul_apply,smul_eq_mul,← hv] at hl; dsimp only [a,b]; rw [he,he]; linarith only [hl]
    by_cases he:a=0
    · rw [he,zero_mul]
      simp_rw [he,zero_pow (by decide : (2:ℕ) ≠ 0),mul_zero,zero_add] at hg; by_contra! he
      specialize hg (-((1+b^2) / h x y)); field_simp at hg; nlinarith only [hg]
    have hA := lt_of_le_of_ne hx (Ne.symm he)
    suffices ht:(h x y)^2 ≤ (a*b)^2 by rw [sq_le_sq,abs_of_nonneg (mul_nonneg hx hy)] at ht; exact (le_abs_self _).trans ht
    specialize hg (-(h x y / a^2)); field_simp at hg; nlinarith only [hg]
  rw [he,ht]
  -- Add polarization
  nlinarith only [hp,show a^2=_ from he x, show b^2=_ from he y] -- definitional? check
lemma fledge {n:ℕ}(he:Valid F d n)(x : S.Field (d+1)) : service (S:=S) (roomRate F d n) (floorAt F d n x) = serviceHigh F n d x := by
   unfold floorAt; rw [dif_pos he]; exact (LinearEquiv.ofBijective _ (viable F n d he)).apply_symm_apply _
lemma retro {n:ℕ}(he:Valid F d n)(x:S.Field d) : floorAt F d n (liftA F d x) = x := by
   apply (viable F n d he).1; rw [fledge F he]
   refine LinearMap.ext fun v=>?_
   exact (inherit F.room.kernel (V!) F.phase.transport.injection F.phase.transport.rights (Real.exp_pos _) (Nat.le_succ d) x v).symm
lemma leaves {n:ℕ}(x:S.Field (d+1)) : cap F d n x=x-liftA F d (floorAt F d n x) := rfl
lemma recombine {n:ℕ}(x:S.Field (d+1)) : x= liftA F d (floorAt F d n x)+cap F d n x := by rw [leaves]; abel
lemma drops {n:ℕ}(he:Valid F d n)(x:S.Field (d+1)) : floorAt F d n (cap F d n x)=0:= by rw [leaves,map_sub,retro F he,sub_self]
lemma paled {n:ℕ}(he:Valid F d n)(x:S.Field d):cap F d n (liftA F d x)=0:= by rw [leaves,retro F he,sub_self]
lemma patch {n n':ℕ}(he:Valid F d n)(x:S.Field (d+1)) : cap F d n (cap F d n' x)=cap F d n x:= by rw [leaves (n:=n') F x,map_sub,paled F he,sub_zero]
lemma pythag {n:ℕ}(he:Valid F d n)(x:S.Field (d+1)) : life F n x ^ 2= (life F n (floorAt F d n x))^2 + (charge F n x)^2 := by
   let g:= roomRate F (d+1) n
   have hp (x:S.Field (d+1)): life F n x ^ 2=g x x := Real.sq_sqrt (positive F.room.kernel (Real.exp_pos _) _)
   let A:= liftA F d (floorAt F d n x); let c:= cap F d n x
   have hr : g c A=0:= by
      have hz:= fledge F he (cap F d n x)
      rw [drops F he x,map_zero] at hz
      exact LinearMap.congr_fun hz.symm (floorAt F d n x)
   have hf : g A c= g c A:= symmetric F.room.kernel (Real.exp_pos _) _ _
   rw [hp, ← reflects_life F, hp, charge,hp]; nth_rw 1 [recombine (n:=n) F x]; conv_lhs=> arg 2; rw [recombine (n:=n) F x] -- exact
   change g (A+c) (A+c)=g A A+g c c; simp [hf,hr]
lemma floor_le {n:ℕ} (he:Valid F d n)(x:S.Field (d+1)) : life F n (floorAt F d n x) ≤ life F n x := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mp; rw [pythag F he x]; exact le_add_of_nonneg_right (sq_nonneg _)
lemma cap_le {n:ℕ} (he:Valid F d n)(x:S.Field (d+1)) : charge F n x ≤ life F n x := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mp; rw [pythag F he x]; exact le_add_of_nonneg_left (sq_nonneg _)
lemma up (d : ℕ) :∀ (x:S.Field d)(n), life F n x ≤ life F (n+1) x:= fun x n=> Real.sqrt_le_sqrt (expands F.room.kernel d x _ _ (Real.exp_pos _) (plank_less n))

section contract
abbrev dial (n:ℕ) : ℝ := n+1
abbrev precision (n:ℕ) := dial (n+1)/dial n
lemma dial_pos (n):0<dial n:= by unfold dial; positivity

-- n! local detector ratio. Honest facts on physical pair in quotient, not a statement about fixed-label transport.
structure Fits : Prop where
  vacuum : ∃ K:ℕ, ∀ᶠ k in atTop, ∀ x:S.Field 0,
     life F (k+1) x ≤ precision k ^ K * life F k x
     -- inverse monotone by kernel
  quota (d : ℕ) : ∃ K:ℕ, ∀ᶠ k in atTop, ∀ x : S.Field (d+1),
      charge F (k+1) x ≤ epoch^(d+1) * precision k^K * charge F k x ∧
      charge F k x ≤ epoch⁻¹ ^ (d+1) * precision k^K * charge F (k+1) x
-- exp(d)*((1+1/(1+k))^K) etc. Enough for log. Testable.
end contract
end YM.SharpGram.Annulus
