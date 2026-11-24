import YM.RG11Proof.Scale.CS
/-!
# Result at finite jet precision

For convenience, even if grade consistency of Z is only through N, may
use prefix changes with Z agreeing through N but arbitrarily extended as
identity-near graded/lawful matrices, since right and left hand sides only
use that precision GIVEN β_B anchored. No assuming matched (N+1)-jet!
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG11.Scale
open scoped BigOperators Classical Topology
open PowerSeries YM.PertExtension.Position YM.RG11.Jets
variable {J P:Type*}[Fintype J]{width:P→ℕ}

section
-- β anchored kills price of N+1
theorem through_weighted {f g: PowerSeries ℝ}{N}{u v:PowerSeries ℝ}(he:Through N f g)(hh:Through N u v)(h:Anchored u):
   Through N (u * derivative ℝ f) (v*derivative ℝ g):=by
  intro k hk
  rw [coeff_mul,coeff_mul]
  refine Finset.sum_congr rfl ?_; intro z hz
  have hz:= Finset.HasAntidiagonal.mem_antidiagonal.mp hz
  by_cases hez:z.1=0
  · rw [←hh z.1 (by omega),hez,coeff_zero_eq_constantCoeff_apply,show constantCoeff u=0 from h]; simp
  rw [hh z.1 (by omega),coeff_derivative,coeff_derivative,he (z.2+1) (by omega)]

theorem through_call {N}{A B:ArrayAt J ℝ width}{μ:PowerSeries ℝ}(hμ:Anchored μ)(D: Square J (PowerSeries ℝ)){v:Mark J width}
    (h:∀w,Through N (A ⟨v.1,w⟩) (B ⟨v.1,w⟩)): Through N (call μ D A v) (call μ D B v):= by
  apply Through.sub (through_weighted (h v.2) (Through.refl _) hμ)
  unfold orbit; exact Through.sum (fun _ _=>Through.sum (fun _ _=>(Through.refl _).mul (h _)))

-- obligations on b ANY degree, incl constant
def vertical {L:Constraints ℝ J}(u:Square J (PowerSeries ℝ)) : Prop:=∀ k,piece k u∈L.vary
namespace vertical
variable {L:Constraints ℝ J}{p q:Square J (PowerSeries ℝ)}

protected theorem add (h:vertical (L:=L) p)(h':vertical (L:=L) q):vertical (L:=L) (p+q):=by intro k; rw [piece_add]; exact L.vary.add_mem (h k) (h' k)

protected theorem sub (h:vertical (L:=L) p)(h':vertical (L:=L) q):vertical (L:=L) (p-q):=by
  intro k; rw [show piece k (p-q)=piece k p-piece k q by ext i j; simp]; exact L.vary.sub_mem (h k) (h' k)

theorem waive (c:PowerSeries ℝ)(h:vertical (L:=L) p): vertical (L:=L) (c • p):=by
  intro k
  have he : piece k (c • p)=∑ z∈Finset.HasAntidiagonal.antidiagonal k, coeff z.1 c • piece z.2 p:= Matrix.ext fun i j=>by simp [Matrix.sum_apply,Matrix.smul_apply,coeff_mul]
  rw [he]; exact Submodule.sum_mem _ (fun z _=>L.vary.smul_mem _ (h _))

theorem comp {c:PowerSeries ℝ}(hz:Anchored c)(h:vertical (L:=L) p): vertical (L:=L) (subs c p):=by
  intro k; rw [piece_subs hz]; exact Submodule.sum_mem _ fun b _=>L.vary.smul_mem _ (h b)

protected theorem flash (h:L.Lawful q): vertical (L:=L) (flash q):=by
   intro k
   have he : piece k (Scale.flash q)=((k+1:ℕ):ℝ) • piece (k+1) q:= Matrix.ext fun i j=>by simp [coeff_derivative,Matrix.smul_apply,mul_comm]
   rw [he]; exact L.vary.smul_mem _ (h.positive (by omega))

theorem right (h:vertical (L:=L) p)(hw:L.Lawful q): vertical (L:=L) (p*q):=by
   intro k
   rw [piece_mul]
   refine Submodule.sum_mem _ ?_
   intro v _; by_cases hX:v.2=0
   · rw [hX,hw.baseline,mul_one]; exact h _
   exact L.both (h v.1) (hw.positive (by omega))

theorem left (h:vertical (L:=L) p)(hw:L.Lawful q):vertical (L:=L) (q*p):=by
   intro k
   rw [piece_mul]; refine Submodule.sum_mem _ ?_
   intro v _; by_cases hX:v.1=0
   · rw [hX,hw.baseline,one_mul]; exact h _
   exact L.both (hw.positive (by omega)) (h v.2)
end vertical

-- orientation. N may be zero even though detection needs A through 1.
theorem transports {L:Constraints ℝ J}(p:Change ℝ J)(hZ:L.Lawful p.Z)(hp:Anchored p.g)
    {w:J→ℕ}(he:graded w p.Z)(E : Keeper width)
    {N} {A B : ArrayAt J ℝ width}(hx:Sees L A)(hm:∀ v,Through N (p.act A v) (B v))
    {β μ:PowerSeries ℝ}{b m:Square J (PowerSeries ℝ)}(ha:Stem N E w A μ m)(hb:Stem N E w B β b)
    (hβ:Anchored β)(hM:vertical (L:=L) m)(hB:vertical (L:=L) b):
   Through N (β*derivative ℝ p.g) (PowerSeries.subst p.g μ) ∧
     MatThrough N (β • (flash p.Z)) (b*p.Z - p.Z * subs p.g m):=by
  let U:= β • (flash p.Z)- b*p.Z+p.Z * subs p.g m
  have hv : vertical (L:=L) U:= ((vertical.waive _ (vertical.flash hZ)).sub (hB.right hZ)).add ((hM.comp hp).left hZ)
  let y:=β*derivative ℝ p.g-PowerSeries.subst p.g μ
  have hu := erase_redefs U y p hx hv hZ.baseline hp (N:=N)
  have H (v) : Through N (call β b (p.act A) v) (p.act (call μ m A) v):=by
    refine (through_call hβ b (fun i=>hm ⟨v.1,i⟩)).trans ((hb v).symm.trans ?_)
    have heq:Through N (euler E w B v) (euler E w (p.act A) v):= ((hm _).sub ((Through.refl _).mul (hm v))).symm
    rw [←sends_engineering p A w E hp he] at heq
    exact heq.trans (Change.EquivJet.refl.act hp fun i=>ha ⟨v.1,i⟩)
  specialize hu (fun v=> by
     rw [←next_left p A β μ b m hp] -- let-p via refolding?
     exact sub_self (p.act (call μ m A) v) ▸ (H v).sub (Through.refl _))
  constructor
  · intro i hi; have he: coeff i (β*derivative ℝ p.g-PowerSeries.subst p.g μ)=0:= (hu i hi).2
    exact sub_eq_zero.mp ((map_sub (coeff i) _ _).symm.trans he)
  apply MatThrough.of_piece; intro i hi
  have heq (z v:Square J (PowerSeries ℝ)):piece i (z-v)=piece i z-piece i v:= Matrix.ext fun j k=> by simp
  have hq: piece i (β • (flash p.Z)- b*p.Z+p.Z * subs p.g m) = 0:= (hu i hi).1
  rw [piece_add,heq] at hq
  rw [heq]; apply sub_eq_zero.mp; rw [← hq]; abel
end
end YM.RG11.Scale
