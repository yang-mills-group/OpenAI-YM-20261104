import YM.RG11Proof.Scale.Grades
import YM.RG11Proof.Scale.Retag
import YM.RG11Proof.Jets.Detector

/-!
# Kill all lowering outputs after separated scale homogeneity

Need exact engineering-polynomial laws at the dilated tested profiles
for BOTH separation schemes, same λ=exp(-u) geometry. Applies only after
performing mass-independent adjustment if needed. Our proof uses simultaneous
ALL-horizon `Free` detector rigidity (incl mixed fields) and a largest-power
estimate, not 2pt engineering-diagonal Gram assumptions on interacting
fields. Includes finite-power version; no requirement on degrees of the logs
or any uniform-in-order assertion.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.RG11.Scale
open scoped BigOperators Classical Topology
open PowerSeries Filter YM.PertExtension.Position YM.RG11.Jets

variable {J P:Type*}{width:P→ℕ}[Fintype J](w:J→ℕ)(s:ℝ→Keeper width)

def bulk (v:Mark J width): ℝ:= ∑ i:Fin (width v.1),(w (v.2 i):ℝ)

/-- Final engineering form on each finite demand. Does not include derivatives;
for them use same rule on derivative tests/labels (or prescribed variant with
the appropriate shift if dilating an already differentiated coefficient instead).
Widths may include 0, sum of field weights in ℝ; e.g. normalized unit scalar 1
has weight 0. -/
def Engineering (A : ArrayAt J ℝ width) (N:ℕ) : Prop:=
   ∀ k ≤ N, ∀ v:Mark J width,(fun u : ℝ=> coeff k (A ((s u).move v)))∈beam (bulk w v)

section
variable {w s}

-- Multiplying on right by a series independent of u.
theorem fixed_factor {A:ℝ→PowerSeries ℝ}(Q:PowerSeries ℝ){w':ℝ}{k:ℕ}
    (he:∀ i≤k,(fun u=>coeff i (A u))∈beam w'):
    (fun u=>coeff k (A u * Q))∈beam w':=by
    simp_rw [coeff_mul]
    have H : (fun u : ℝ=>∑ z∈Finset.HasAntidiagonal.antidiagonal k, coeff z.1 (A u) * coeff z.2 Q)=
        ∑ z∈Finset.HasAntidiagonal.antidiagonal k, coeff z.2 Q • (fun u : ℝ=>coeff z.1 (A u)):=funext fun _=>by simp [mul_comm]
    rw [H]
    apply Submodule.sum_mem; intro z hz
    refine Submodule.smul_mem _ _ (he _ ?_)
    have ht:=Finset.HasAntidiagonal.mem_antidiagonal.mp hz; omega

theorem fixed_comp {A:ℝ→PowerSeries ℝ}{p:PowerSeries ℝ}(h:Anchored p){w':ℝ}{k:ℕ}
   (he:∀ i≤k,(fun u=>coeff i (A u))∈beam w'):
   (fun u=>coeff k (PowerSeries.subst p (A u)))∈beam w':=by
   simp_rw [coeff_compose k _ _ h]
   have H : (fun u : ℝ=> ∑ i∈Finset.range (k+1), coeff i (A u)* coeff k (p^i))=
        ∑ i∈Finset.range (k+1),coeff k (p^i) • (fun u : ℝ=>coeff i (A u)):= funext fun _=>by simp [mul_comm]
   rw [H]
   refine Submodule.sum_mem _ (fun i hi=> Submodule.smul_mem _ _ (he _ ?_)); have ht:=Finset.mem_range.mp hi; omega

theorem Engineering.act {N}(p:Change ℝ J)(hp:Anchored p.g)(hZ:graded w p.Z)
    {A:ArrayAt J ℝ width}(h:Engineering w s A N): Engineering w s (p.act A) N:=by
  intro k hk v
  simp_rw [Keeper.move_act, Change.act, PertExtension.Position.insert,map_sum]
  let R (i:Fin (width v.1)→J)(u:ℝ):PowerSeries ℝ:= PowerSeries.subst p.g ((A ∘ (s u).move) ⟨v.1,i⟩)
  let Q (i:Fin (width v.1)→J):PowerSeries ℝ:= ∏ j, p.Z (v.2 j) (i j)
  change (fun u=>∑ i:Fin (width v.1)→J, coeff k (R i u * Q i))∈beam _
  rw [show (fun u=>∑ i:Fin (width v.1)→J, coeff k (R i u*Q i))=(∑ i:Fin (width v.1)→J,(fun u=>coeff k (R i u*Q i))) from funext fun u=>by rw [Finset.sum_apply]]
  apply Submodule.sum_mem; intro i _
  by_cases hc:∀ j,w (v.2 j)=w (i j)
  · apply fixed_factor; intro l hl; apply fixed_comp hp; intro n hn
    have he: bulk w v=bulk w (⟨v.1,i⟩:Mark J width):=Finset.sum_congr rfl fun j _=> by rw [show (⟨v.1,i⟩:Mark J width).2 j=i j from rfl,hc j]
    rw [he]; exact h n (hn.trans (hl.trans hk)) ⟨v.1,i⟩
  obtain ⟨j,hc⟩:=not_forall.mp hc
  have he : Q i = 0:= Finset.prod_eq_zero (Finset.mem_univ j) (@hZ (v.2 j) (i j) hc)
  rw [he]; simp only [mul_zero,map_zero]
  exact (beam _).zero_mem

-- On a strictly lowering orbit pass even the logs.
theorem lowers_orbit {N}(v:Mark J width){D:Square J ℝ}(hd:∀ i j,w i≤w j → D i j=0)
     {A:ArrayAt J ℝ width}(h:Engineering w s A N):
     (fun u=>orbit (fun z=>constantCoeff (A z)) ((s u).move v) D)∈passes (bulk w v):=by
  simp_rw [Keeper.move_orbit, orbit, Function.comp_apply]
  let R (i:Fin (width v.1))(j:J)(u:ℝ):=constantCoeff (A ((s u).move ⟨v.1,Function.update v.2 i j⟩))
  have H : (fun u : ℝ=> ∑ i,∑ j:J,D (v.2 i) j * R i j u) = (∑ i,∑ j:J, D (v.2 i) j • R i j):=by ext; simp
  rw [show (fun u : ℝ=> ∑ i,∑ j:J,D (v.2 i) j * constantCoeff _)=(∑ i,∑ j:J, D (v.2 i) j • R i j) from H]
  apply Submodule.sum_mem; intro i _; apply Submodule.sum_mem; intro j _
  by_cases he:w (v.2 i)≤w j
  · rw [hd _ _ he,zero_smul]; exact (passes _).zero_mem
  let b:Mark J width:= ⟨v.1,Function.update v.2 i j⟩
  apply Submodule.smul_mem; apply trail (v:=bulk w b)
  · unfold bulk; change (∑ k:Fin (width v.1),(w (Function.update v.2 i j k):ℝ))<_
    apply Finset.sum_lt_sum
    · intro k _; by_cases hm:k=i
      · subst k; simp; omega
      simp [Function.update_of_ne hm]
    exact ⟨i,Finset.mem_univ i,by simp; omega⟩
  simpa only [coeff_zero_eq_constantCoeff_apply] using h 0 (Nat.zero_le N) b

/-- Scale consistency at power k and stamps from earlier powers give vanishing
of the off-diagonal-weight FRAME via the *free* detector. No triangular
orientation of the ruler needed since the same ruler is used. -/
theorem match_stamp {L : Constraints ℝ J}(hl:Permits J w L){N}{p: Change ℝ J}(hZ:L.Lawful p.Z)(hp:Anchored p.g)
    {A B:ArrayAt J ℝ width}(ha:Engineering w s A N)(hb:Engineering w s B N)
    (h0:s 0=Keeper.id width)
    (hm:∀ v, Through N (p.act A v) (B v))
    (hf:Free L A):
    ∀ k≤N, graded w (piece k p.Z):=by
  intro k hk
  induction k using Nat.strong_induction_on with
  | h k ih=>
    by_cases ht:k=0
    · subst k; rw [show piece 0 p.Z = 1 from hZ.baseline]; exact graded.one
    let q:Change ℝ J:= ⟨p.g,isolate w p.Z⟩
    let D:=piece k p.Z-isolate w (piece k p.Z)
    have hd:D∈L.vary:=L.vary.sub_mem (hZ.positive (by omega)) (hl.split (hZ.positive (by omega)))
    suffices D=0 by rw [sub_eq_zero.mp this]; exact graded.isIsolated _
    have hq (v:Mark J width) : orbit (fun z=>constantCoeff (A z)) v D = coeff k (B v)-coeff k (q.act A v):=by
      have he:∀ i j,Strike k (q.Z i j) (p.Z i j) (D i j):=by
        intro i j
        have Hm(n): piece n q.Z=isolate w (piece n p.Z):=graded.piece_isolate p.Z n
        constructor
        · intro b H
          have e:=Hm b |>.trans (graded.invariant (ih b H (H.le.trans hk)))
          exact congrArg (fun A:Square J ℝ=> A i j) e
        change piece k q.Z i j + _ = piece k p.Z i j
        rw [Hm k]; change isolate w (piece k p.Z) i j + (piece k p.Z i j - isolate w (piece k p.Z) i j) = _; ring
      have H := (pencil_action (A:=A) (p:=q) (q:=p) (n:=k) (by omega) hp
           (show nearId q.Z by change piece 0 (isolate w p.Z)=_; rw [graded.piece_isolate,hZ.baseline,graded.isolates_one])
            (Strike.same _) he v).value
      change _ + (orbit (fun z=>constantCoeff (A z)) v D + tangent (A v)*0) = _ at H
      rw [mul_zero,add_zero,hm v k hk] at H
      rw [←H]; ring
    have hdone : (⟨D,hd⟩:L.vary)=0:=by
       apply hf; intro v
       have H : (fun u : ℝ=>orbit (fun z=>constantCoeff (A z)) ((s u).move v) D)∈beam (bulk w v):= by
         simp_rw [hq]; exact Submodule.sub_mem _ (hb k hk v) (ha.act q hp (graded.isIsolated _) k hk v)
       convert! negligible H (lowers_orbit v (D:=D) (fun i j hij=> ?_) ha) 0 le_rfl using 1
       · rw [h0,Keeper.move_id]
       dsimp [D,isolate]; split <;> rename_i hd
       · exact sub_self _
       change piece k p.Z i j - 0 = _
       rw [hl.lowers (hZ.positive (by omega)) i j (lt_of_le_of_ne hij hd),sub_zero]
    exact congrArg Subtype.val hdone
end
end YM.RG11.Scale
