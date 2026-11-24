import YM.Integration.WilsonThermometerUnitFilingBranches

/-! At any older date the full pinned ordinary input retains its source height, independently of how many higher Taylor grades a later listener requests. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingPinnedPole
open Filter Finset Lattice Laurent RG Precision Wilson Input WilsonCoeffUV
open WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Shard
open WilsonCoeffUV.Soil WilsonCoeffUV.Embroider WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open Org PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonThermometerUnitFilingPinned
open scoped Classical BigOperators
variable {G:Gauge} {W:Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

omit [CompleteSpace W] in
private theorem charged {g:ℝ}(gp:0<g)(cold:g≤1)(e r h:ℕ)(a:W)(silent:h+e<r→a=0):
    ‖(g^e/g^r) • a‖ ≤ (1/g^h)*‖a‖:=by
  by_cases rank:r ≤ h+e
  · have t:g^e*g^h≤g^r:=by
      rw [←pow_add]
      exact pow_le_pow_of_le_one gp.le cold (by omega)
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right ((div_le_div_iff₀ (pow_pos gp _) (pow_pos gp _)).2
      (by simpa only [one_mul] using t)) (norm_nonneg _)
  · simp only [silent (lt_of_not_ge rank),smul_zero,norm_zero,mul_zero,le_refl]

theorem recapped (R:Run G)(simple:G.Simple){N b v h H:ℕ}{X:Era G W}(auth:Auth h X)
    (bn:b≤N)(vb:v≤b)(height:h≤H):
    march R.family.path.levels R.metals.O N b v H X=march R.family.path.levels R.metals.O N b v h X:=by
  let A:=R.family.path.levels;let O:=R.metals.O
  change march A O N b v H X=march A O N b v h X
  induction vb using Nat.decreasingInduction with
  | self=>rw [top,top]
  | of_succ i live ih=>
    rw [step _ _ _ _ _ _ _ live,step _ _ _ _ _ _ _ live,ih]
    exact (verseExpand A (live.trans_le bn) simple R.alloy.B.ratio
      (enrolled A O auth simple R.alloy.B.ratio bn (Nat.succ_le_of_lt live)) height).symm

theorem original (R:Run G)(simple:G.Simple){N b v h H:ℕ}{X:Era G W}(auth:Auth h X)
    (bn:b≤N)(vb:v≤b)(height:h≤H){g:ℝ}(gp:0<g)(cold:g≤1):
    let Y:=march R.family.path.levels R.metals.O N b v H X
    (∀ n:Side,∀ e r z,‖(g^e/g^r) • Y.1 n e r z‖ ≤ (1/g^h)*‖Y.1 n e r z‖) ∧
      ∀ e r z,‖(g^e/g^r) • Y.2 e r z‖ ≤ (1/g^h)*‖Y.2 e r z‖:=by
  intro Y
  have pay:Auth h Y:=by
    dsimp only [Y]
    rw [recapped R simple auth bn vb height]
    exact enrolled _ _ auth simple R.alloy.B.ratio bn vb
  constructor
  · intro n e r z
    exact charged gp cold e r h _ (fun beyond=>congr_fun (pay.span n e r beyond) z)
  · intro e r z
    apply charged gp cold
    intro beyond
    have van:Y.2 e r=0:=(pay.wing e r).exten (Bends.zero.congr
      (Eventually.of_forall fun n=>(pay.span n e r beyond).symm))
    exact congr_fun van z

variable {I ι:Type} [Fintype I] [DecidableEq ι] {D:ι→ℕ}

omit [CompleteSpace W] in
theorem stamped (R:Run G)(simple:G.Simple){N b h:ℕ}(bn:b≤N)(K k:ι→ℕ)
    (X:I→Outerm G D)(stock:∀i,Wellness k (X i))(mask:I→Finset ι)
    (seat:I→ι→ Cover)(read:(i:I)→Pen D (mask i)→L[ℝ]W)(weight:I→ℝ)(cap:∀i,mass k (mask i)≤h):
    let A:=R.family.path.levels
    let O:=R.metals.O
    Auth h (∑i:I,weight i • tuftV (read i) (levelsO ((Gears A O K k N N b (X i)) (seat i)) (mask i))):=by
  intro A O
  refine Auth.sum (fun i _=>?_)
  have live:=Cog (K':=K) A O (N:=N) (b:=N) le_rfl (X i) (stock i) simple R.alloy.B.ratio bn
  exact (((placedO _ (live.level' _) _).tuft (read i)).μ (weight i)).tall (cap i)

end YM.Integration.WilsonThermometerUnitFilingPinnedPole
