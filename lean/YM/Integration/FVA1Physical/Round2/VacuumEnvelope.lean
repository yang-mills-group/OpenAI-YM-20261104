import YM.Integration.FVA1Physical.Round2.PhysicalVacuumRate

/-! Put the supremum over independent field tests inside the anchored
sum. A single envelope has to pay all address tuples simultaneously. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2
open Lattice Push Push.Uniform MSbar MSbar.Lis MSbar.Whisk MSbar.CrossH
open Filter RG Wilson Precision MSbar.Midpoint PhysicalNext.Repeat.Legato
open scoped BigOperators Classical Topology
variable {G : Gauge} {n : Side}

private theorem polynomial_envelope {σ : Type} [Fintype σ] [DecidableEq σ]
    {site : σ → Site n} {a w Z : ℝ} {s q m : ℕ} (P : Cacao.Pot σ)
    (ha : 0 ≤ a) (hw : 0 < w) (tok : Tokew site a s m 0 P Z)
    (deg : P.totalDegree ≤ m+1) :
    JetTab site a s w (Metric.closedBall 0 w) (clue P) q (w^(q+1)*(Z*(1+w)^(m+1))) := by
  let ball := Metric.closedBall (0 : Positions σ) w
  have maxima (l : List σ) : ∃ y ∈ ball, ∀ z ∈ ball, |buoy (clue P) z l| ≤ |buoy (clue P) y l| := by
    have cont : ContinuousOn (fun z : Positions σ => |buoy (clue P) z l|) ball := by
      intro z _
      have sm := smooth l.length 0 (l.map bolt) ((helm P _).contDiffAt (x:=z)) (by simp)
      exact sm.continuousAt.abs.continuousWithinAt
    obtain ⟨y,hy,hm⟩ := (isCompact_closedBall (0 : Positions σ) w).exists_isMaxOn
      (show ball.Nonempty from ⟨0,Metric.mem_closedBall_self hw.le⟩) cont
    exact ⟨y,hy,fun _ h => hm h⟩
  choose y hy hm using maxima
  refine ⟨by have hZ := tok.1; positivity,fun l => w^(q+1)*|buoy (clue P) (y l) l|,?_,?_⟩
  · intro l _
    refine ⟨mul_nonneg (pow_nonneg hw.le _) (abs_nonneg _),fun z hz => ?_⟩
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hm l z hz) (pow_nonneg hw.le _)
  intro i
  have phase := Bakery.spice_fund (x:=(0 : Positions σ)) ha (Cacao.pdeg i deg) (tok.2 i) hw.le q
  have estimate := phase.2 (fun l => y (i::l)) (fun l => hy (i::l))
  refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left estimate (pow_nonneg hw.le _))
  rw [← sheen]
  apply stitch
  intro l _
  dsimp only
  rw [Bakery.valor_eq,← tasteful, tours]
  change w^(q+1)*|Whisk.read (y (i::l)) (i::l) P| *_ =
    w^(q+1)*(Measuring.swipe site a s (i::l)*|Whisk.read (y (i::l)) (i::l) P|)
  ring

private theorem envelope_add_scaled {σ : Type} [Fintype σ] {site : σ → Site n}
    {a w B Z : ℝ} {s q k : ℕ} {S : Set (Positions σ)} {F H : Positions σ → ℝ}
    (J : JetTab site a s w S F q B) (K : JetTab site a s w S H q Z) (c : ℝ)
    (hw : 0 < w) (hk : q+1 ≤ k) (sm : ∀ x ∈ S, ContDiffAt ℝ k F x)
    (sh : ∀ x ∈ S, ContDiffAt ℝ k H x) :
    JetTab site a s w S (F+fun z => c*H z) q (B+|c| *Z) := by
  obtain ⟨hB,f,supF,rowF⟩ := J
  obtain ⟨hZ,h,supH,rowH⟩ := K
  refine ⟨add_nonneg hB (mul_nonneg (abs_nonneg _) hZ),fun l => f l+|c| *h l,?_,?_⟩
  · intro l hl
    obtain ⟨fp,fs⟩ := supF l hl
    obtain ⟨hp,hs⟩ := supH l hl
    refine ⟨add_nonneg fp (mul_nonneg (abs_nonneg _) hp),?_⟩
    intro x hx
    have hk' : (l.map bolt).length ≤ k := by simpa [hl] using hk
    change |roc (F+fun z => c*H z) (l.map bolt) x| *w^(q+1) ≤ _
    rw [addedL k _ _ _ (sm x hx) (contDiffAt_const.mul (sh x hx)) hk',wed k _ c H (sh x hx) hk']
    calc
      _ ≤ (|buoy F x l|+|c*buoy H x l|)*w^(q+1) :=
        mul_le_mul_of_nonneg_right (abs_add_le ..) (pow_nonneg hw.le _)
      _ = _ := by rw [abs_mul,add_mul,mul_assoc]
      _ ≤ _ := add_le_add (fs x hx) (mul_le_mul_of_nonneg_left (hs x hx) (abs_nonneg c))
  intro i
  simp_rw [add_mul,mul_assoc,pockets,sheen]
  exact add_le_add (rowF i) (mul_le_mul_of_nonneg_left (rowH i) (abs_nonneg c))

/-- A single majorant dominates all field configurations for every address,
and its weighted row sum pays the first omitted Taylor coefficient. -/
theorem truncated_vacuum_envelope (Q : Rep G n) (A : Rolling.Nesting G n) {g a b w h B Z : ℝ} {s m q p : ℕ}
    (hg : 0 ≤ g) (ha : 0 ≤ a) (hab : a ≤ b) (hw : 0 < w) (hh : 1 ≤ h) (hq : q+1 ≤ m)
    (J : JetTab (Measuring.chart n G) a s w (Metric.closedBall 0 w) (Aqua.film Q A g (p+1)) q B)
    (sm : ∀ x ∈ Metric.closedBall 0 w, ContDiffAt ℝ m (Aqua.film Q A g (p+1)) x)
    (H : Tin (Measuring.chart n G) b s (p+2) h (PowerSeries.coeff (p+1) A) Z)
    (deg : (PowerSeries.coeff (p+1) A).totalDegree ≤ (p+2)+1) :
    JetTab (Measuring.chart n G) a s w (Metric.closedBall 0 w) (Aqua.film Q A g p) q
      (B + g^(p+1)*(w^(q+1)*(Z*(1+w)^(p+3)))) := by
  let P := PowerSeries.coeff (p+1) A
  have tok := (Tin.weightTok (zero_lt_one.trans_le hh) hh H).soft hab ha
  have U := polynomial_envelope (q:=q) P ha hw tok deg
  rw [film_truncate Q A g p]
  simpa only [abs_of_nonneg (pow_nonneg hg (p+1))] using
    envelope_add_scaled J U (g^(p+1)) hw hq sm (fun _ _ => (helm P _).contDiffAt)

end YM.Integration.FVA1Physical.Round2
