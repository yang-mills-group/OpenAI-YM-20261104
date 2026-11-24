import YM.RG11Proof.Bridge.Removal

/-!
# Triangular leading Gram absorption

When a common regulator has not already furnished the `frame0 : ≈ I`
condition of `RegControl`: sufficient to furnish near-I leading on the
diagonal and forbidden part of a triangular ranking, and simultaneous
paired reads beside attached residuals with lower-row induction costs. This
is useful also for power divergent lower-weight counterterms at LEADING in
slot-rescaled fields. Use rank e.g. lex(engineering grade, slot degree), with
hypothesis near-I for outputs of equal or greater rank. Use reflection and
strict positivity on the specified *quotient*. This file is an algebraic rate
argument, no sharp Gram estimates for actual readout.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Bridge
open PowerSeries YM.PertExtension.Position YM.RG11.Jets YM.RG11.Formal YM.RG11.Rate Filter
open scoped BigOperators Classical

variable {α J : Type*} {k : Budget α} [Fintype J] [DecidableEq J]
variable (Z : α → Square J ℝ) (A R : Square J ℝ)

-- R fixed matrix of reflection test (row label at the **lower** detector
-- point -> full reflected partner). Need R supported at that level (or
-- below), NOT commuting Z with every symmetry at the cutoff for this lemma.
def gramAt (i j:J) := ∑ l,R j l*A i l

def Positive : Prop := ∀ x:J→ℝ, x≠0 → 0<∑ j,x j*(∑ i,x i* gramAt A R i j)

-- Introduce this rank for the *induction on the leading conversion*, can
-- include extra gradings (slot number) beyond the requested filtration rule.
variable {d:J→ℕ}
def priceRow(i:J)(a:α) :=∑ j:J,|Z a i j|

def Done (k : Budget α) (Z : α→Square J ℝ) (i:J) := ∀ j, Near k (fun a=>Z a i j) ((1:Square J ℝ) i j)

-- This is the pair-reading criterion after applying `Saves.values` at
-- order zero and conversion on only **one** possibly unbounded slot (use
-- rows at j lower than i as detectors). See `Leading.lean`. No request
-- to bound i-row in these comparisons. Errors multiplying it are allowed
-- at budget rate.
def Comparison (k : Budget α) (Z : α → Square J ℝ) (A R : Square J ℝ) (d : J → ℕ) :=
   ∀ i,(∀ l, d l<d i → Done k Z l) → ∀ j, d j<d i →
    Carry k (priceRow Z i) (fun a => ∑ l, Z a i l * gramAt A R l j) (fun _=>gramAt A R i j)

private abbrev Lower (d : J → ℕ) (i : J):= {l:J // d l < d i}

private def matchL (d:J→ℕ) (i : J) : (Lower d i→ℝ) →ₗ[ℝ] Lower d i→ℝ where
  toFun x j := ∑ l:Lower d i,x l* gramAt A R l j
  map_add' _ _:= funext fun j=> by simp [Pi.add_apply,add_mul,Finset.sum_add_distrib]
  map_smul' _ _:= funext fun j=> by simp [Pi.smul_apply,mul_assoc,Finset.mul_sum]

-- Useful calculus with subtype restriction.
omit [DecidableEq J] in
private theorem lowerSum (P : J→ Prop) [DecidablePred P] (f : J→ℝ): (∑ i:J, if P i then f i else 0)=∑ i:{j:J//P j},f i.val:=by
  simp_rw [←Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

omit [DecidableEq J] in
private theorem inj_lower (Q : Positive A R) (i:J) : Function.Injective (matchL A R d i) := by
  apply LinearMap.ker_eq_bot.mp
  apply (LinearMap.ker_eq_bot' (f:=matchL ..)).mpr
  intro x hx
  by_contra he
  let f (j:J):= if h:d j<d i then x ⟨j,h⟩ else 0
  have hh (j:Lower d i):f j=x j:=dif_pos j.property -- need proof
  have hb:f≠0:= fun h => he (funext fun j=> (hh j).symm.trans (congrFun h j))
  have hu(v : J→ℝ): (∑ j,f j*v j)=∑ j:Lower d i,f j*v j:=by
    rw [← lowerSum (P:=fun j=>d j<d i) (f:=fun j=>f j*v j)]; apply Finset.sum_congr rfl; intro j _
    split;· rfl
    unfold f; split <;> simp_all
  have H := Q f hb
  simp_rw [hu (v:=fun j=> ∑ i_1, f i_1 * gramAt A R i_1 j)] at H -- binder use
  simp_rw [fun j : Lower d i=>hu (fun l=> gramAt A R l j),hh] at H
  have hz (j:Lower d i) : ∑ l,x l*gramAt A R l j=0:= congrFun hx j
  simp_rw [hz,mul_zero, Finset.sum_const_zero] at H; linarith

-- Absorb W in ∑ |Z_ij| on ALL J via restore equations extended by unit
-- readings for already paid coordinates. Uses RATE premise on diagonal and
-- forbidden section (`orient`), not just a compactness limit.
theorem gram_leading {A R:Square J ℝ} (hg:Positive A R) {d:J→ℕ}
    (diag : ∀ i l, d i ≤ d l → Near k (fun a=>Z a i l) ((1:Square J ℝ) i l))
    (comp : Comparison k Z A R d) : ∀ i, Done k Z i := by
  suffices ∀ n,∀ i : J, d i=n → Done k Z i from fun i=> this _ i rfl
  intro n; induction n using Nat.strong_induction_on with
  | _ n hi =>
  intro i hN
  have hS (l : J)(hl:d l < d i) : Done k Z l := hi _ (hN ▸ hl) l rfl
  let W := priceRow Z i
  let p : Square J ℝ:=1
  -- Subtract the known row identity and discard its high component at Carry
  -- precision, obtaining the linear system on the lower coordinates.
  let Δ(a:α)(j:J):=Z a i j-p i j
  have he(j:Lower d i) : Carry k W (fun a=> ∑ l:Lower d i,Δ a l * gramAt A R l j) (fun _=>0):=by
    have hf(b:J→ℝ):∑ l,p i l*b l=b i:=by classical simp [p,Matrix.one_apply,ite_mul]
    have hh:= (comp i hS j j.property).sub (Carry.refl (k:=k) (w:=W) (fun _=> gramAt A R i j))
    have h : Carry k W (fun a=> ∑ l:J, Δ a l* gramAt A R l j) (fun _=>0):= by
      convert! hh using 1
      · ext a; unfold Δ; simp only [sub_mul,Finset.sum_sub_distrib]; rw [hf]
      simp
    rw [show (fun a => ∑ l:Lower d i,Δ a l * gramAt A R l j) = (fun a=>∑ l:J, if d l<d i then Δ a l*gramAt A R l j else 0) from funext fun _=> Eq.symm (lowerSum ..)]
    apply Carry.trans _ h
    refine carry_sum (fun l _=> ?_)
    by_cases he:d l<d i
    · simp_rw [if_pos he]; exact Carry.refl _
    simp_rw [if_neg he]
    have hx : Near k (fun a=> Δ a l) 0:= by
      have hq:=(diag i l (le_of_not_gt he)).sub (Near.const ((1:Square J ℝ) i l))
      change Near k (fun a=> Δ a l) _ at hq; rwa [sub_self] at hq
    have hx': NearFn k _ _:= hx
    exact Carry.symm (by simpa only [zero_mul] using (hx'.carry _).mul_bounded (Bounded.const (gramAt A R l j)))
  obtain ⟨L,hL⟩ := LinearMap.exists_leftInverse_of_injective (matchL A R d i)
     (LinearMap.ker_eq_bot.mpr (inj_lower (d:=d) _ _ hg i))
  have hX (l:J): Carry k W (fun a=> Z a i l) (fun _=> p i l):= by
    by_cases hl:d l<d i
    swap;· exact NearFn.carry (diag _ _ (le_of_not_gt hl)) _
    let j:Lower d i:=⟨l,hl⟩
    let U := (LinearMap.proj (R:=ℝ) j).comp L
    have hU (x:Lower d i→ℝ): U (matchL A R d i x)=x j:=congrFun (LinearMap.congr_fun hL x) j
    have hh:=carry_linear U he
    have h0 : U (fun _=>0)=(0:ℝ):= map_zero _
    change Carry k W (fun a=>U (matchL A R d i (fun j=> Δ a j.val))) (fun _=>U (fun _=>0)) at hh -- syntax ..
    simp_rw [hU,h0] at hh
    unfold Carry at hh ⊢; simpa only [j,Δ, sub_zero] using hh
  exact (absorb (y:=fun a l=>Z a i l) (u:=p i) hX).2
end YM.RG11.Bridge
