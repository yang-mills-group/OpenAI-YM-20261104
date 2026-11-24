import YM.RG01Estimate.CensusTail

/-!
# Fugacity for special kinds of optional vertices in the absolute hit estimate

Book additional marks in the estimates ONLY (not physical source tags). This lets us
extract very uneven weights even after the cluster coefficients are priced with
full-union polynomial/derivative costs. Use optional supplies before the second
cluster sum (there would not in general be enough *support* surplus in the sense of
changing the final support payments by hand).
-/
set_option autoImplicit false
noncomputable section

namespace YM.RG01Estimate.Expense

open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Window Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open PhysicalNext PhysicalNext.Repeat Height Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {R : RG.Rep G f} {μ q C' d v Y A b r B s α a δ e i w D : ℝ} {k j n ℓ : ℕ} {χ : Chi}
    {H : Cash W s μ L Q o α T R}

private def raised (b : Mixed.Costs) (D : ℝ) : Mixed.Costs :=
  { b with optionalHit := D*b.optionalHit, rootHit := D*b.rootHit }
private lemma buy_scale (b : Mixed.Costs) (B : ℕ) (h : b.Buy S.patch.L ℓ B) (hD : 1 ≤ D)
    (hh : 0 ≤ Packets.totalCharge S.patch.L b.cap ℓ B b.packetRatio 0)
    (hv : degreePrice B (D*b.rootHit) b.reserveTree ≤ b.q) : (raised b D).Buy S.patch.L ℓ B := by
  have he : 0 ≤ D:= zero_le_one.trans hD
  refine ⟨h.eps,h.δ,mul_pos (zero_lt_one.trans_le hD) h.γ,h.capture,h.extra,h.marked,h.price,h.packet,
    ?_,hv,h.grows⟩
  change _+D*b.optionalHit ≤ D*b.rootHit
  apply le_trans _ (mul_le_mul_of_nonneg_left h.combined he)
  rw [mul_add]; exact add_le_add_left (le_mul_of_one_le_left hh hD) _

-- multiply the optional fugacity into the wallet
variable (Z : Alphabet c f → ℝ) (U : Utopia H j v d r C' χ)

def Supports := Sales (radiusB s) Q.relative Q.ε (footprints T R Q.halo (radiusB s))
      (fun i=> Z i * U.flair i) (Sum.elim (Raw.forcedExtra R) (Sum.elim (exCharge T R) fun _=>0)) (Q.goal L s)

local notation "tail" => Q.costs L μ R.beta s C'
lemma lifted_accounts (h : Supports Z U) (hv : 1 ≤ D) :
    Mixed.Accounts S Q.halo (radiusB s) (raised tail D) H.birth
      (fun i=> D * (Z i * U.flair i)) (ConnectedActivityE6.lengths T R) (steamP S tail) := by
  have hf := h.shift (zero_le_one.trans hv) (z:=fun i=>D*(Z i*U.flair i))
    (fun i=> mul_nonneg (zero_le_one.trans hv) (h.nonneg i)) (fun _=> le_rfl)
  exact ⟨U.accrues.packetBound,hf.nonneg,U.accrues.extra,hf.hit⟩

variable (p' : Molecule S)
def toll (D : ℝ) (x : Head S) := Sum.elim (fun _=> (1:ℝ)) (fun i=> D* Z i) x
def sumT (D : ℝ) (p : Molecule S) := ∏ i∈p,toll Z D i

-- bound without turning mark inside exponential
lemma vertex_hit (h : Supports Z U) (hv : 1 ≤ D)
    (hs : degreePrice (radiusB s) (D*(Q.costs L μ 1 s 0).rootHit) Q.δ ≤ 1/2) :
    Ac.Hit H.unionP (radiusB s) (fun p=> sumT Z D p * U.meant p n) Q.exp
      (D * Q.overture L μ s n) := by
  let t:= Utopia.meant U; let g x:= D*(Z x*U.flair x)
  let X:= tail; let b:= radiusB s; let X':= raised X D
  have hx : 0 ≤ Packets.totalCharge S.patch.L X.cap Q.halo b X.packetRatio 0:= by
    unfold Packets.totalCharge
    have h₁ : 0 ≤ X.cap:= U.lives.capture
    have h₂ : 0 ≤ (1-X.packetRatio)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr U.lives.packet.2.2.le)
    have h₃ : 0 ≤ X.packetRatio := le_trans (by unfold Packets.ratioCost Packets.oneCost; positivity) U.lives.packet.2.1
    positivity
  have he:= Mixed.mixed_hit S Q.halo b X' H.birth g (ConnectedActivityE6.lengths T R) (steamP S X)
    (buy_scale X b U.lives hv hx hs) (lifted_accounts Z U h hv) 0 n 0 0
  have hG : ∀ i : Head S,toll Z D i*U.fare i=Mixed.costs S Q.halo b (steamP S X) g i:= by
    rintro (x|y)
    · unfold toll; simp only [Sum.elim, one_mul]; rfl
    unfold toll; simp only [Sum.elim]; rw [mul_assoc]; rfl
  have hh : ∀ p : Molecule S, sumT Z D p*U.meant p n = Mixed.selected S Q.halo b X' H.birth g
      (ConnectedActivityE6.lengths T R) (steamP S X) 0 n 0 0 p := by
    intro p; unfold Utopia.meant; split_ifs
    next ht=>
      unfold Mixed.selected
      rw [if_pos (show Mixed.Allowed S Q.halo b X' H.birth _ 0 0 0 p from ht),← mul_assoc, sumT,← prod_mul_distrib]; simp_rw [hG]; rfl
    next ht=>
      unfold Mixed.selected
      rw [if_neg (show ¬ Mixed.Allowed S Q.halo b X' H.birth _ 0 0 0 p from ht), mul_zero]
  simp_rw [hh]; rw [show D*Q.overture L μ s n=X'.ceiling 0 n 0 0 from ?_]; exact he
  unfold X' raised X; unfold ConnectedActivityE6.Target.overture ConnectedActivityE6.Target.quantum Mixed.Costs.ceiling
      Reserves.extract Reserves.treeYield
  dsimp only [ConnectedActivityE6.Target.costs,Buy.quote]; ring

variable (N : Captain H j C' d v Y A b r B q k χ)

lemma repriced (hD : 1 ≤ D) (hZ : ∀ i, 0 ≤ Z i) (hp : Supports Z N.conduit) (ha : Armada Q L μ a s i B j k)
    (hs : degreePrice (radiusB s) (D*(Q.costs L μ 1 s 0).rootHit) Q.δ ≤ 1/2)
    (ht : degreePrice (radiusB s) (D*salary Q L μ B s j k) i ≤ 1/2) :
    Ready H.smallAt (radiusB s) (fun z:H.ThinP=> sumT Z D z.val*N.stone z) (a+i)
      (D * salary Q L μ B s j k) i (1/2) := by
  let m (u:Molecule S):=sumT Z D u
  let f z:=m z*N.conduit.meant z k
  have hr : Ac.Hit H.unionP (radiusB s) f Q.exp _ := vertex_hit Z N.conduit hp hD hs
  have hD':0<D:=zero_lt_one.trans_le hD; have hB:=N.balance
  have hm (u:Molecule S) : 0 ≤ m u := by
    apply Finset.prod_nonneg; rintro (x|y) _; exact zero_le_one
    exact mul_nonneg hD'.le (hZ _)
  have hmk z : 0 ≤ sumT Z D (Subtype.val (p:=fun (p:Molecule S)=> _) z)*N.stone z:=
    mul_nonneg (hm z.val) (N.stone_pos z)
  have hE := ha.earned
  refine ⟨by unfold salary; positivity,ha.delta,ht,by norm_num,hmk,fun x=>?_⟩
  have hy:= budget_scale (show 0≤(2:ℝ)^j*B by positivity) (budget_pull
    (fun z:H.ThinP=>z.val) Subtype.val_injective (hr x))
  refine budget_loosen (budget_mono hy (fun z=> ?_) (fun z=> ?_)) ?_
  · dsimp only; split
    next => exact mul_nonneg (hmk _) (Real.exp_pos _).le
    exact le_rfl
  · dsimp only; split
    next hx =>
      rw [if_pos (show x∈H.unionP z.val from hx), ← mul_assoc, show 2^j*B*f z.val=m z.val*N.stone z by unfold f Captain.stone; ring]
      exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right ha.little (Nat.cast_nonneg _))) (hmk z)
    exact hy.1 z
  unfold salary; nlinarith only [mul_pos hD' hE]

def clusterCost (D : ℝ) (z : H.fragrances) := ∏ i,sumT Z D (z.2 i).val
lemma cluster_eq (z : H.fragrances) : clusterCost Z D z * N.design z=
    clusters H.seam (fun u:H.ThinP=> sumT Z D u.val*N.stone u) z.2 := by
  unfold Captain.design clusters clusterCost; rw [Finset.prod_mul_distrib]; ring

-- generalized budget at weighted marker tags
lemma at_radii (hD : 1 ≤ D) (hZ : ∀ i, 0 ≤ Z i) (hp : Supports Z N.conduit) (ha : Armada Q L μ a s i B j k)
    (hs : degreePrice (radiusB s) (D*(Q.costs L μ 1 s 0).rootHit) Q.δ ≤ 1/2)
    (ht : degreePrice (radiusB s) (D*salary Q L μ B s j k) i ≤ 1/2) :
    Ac.Hit (Captain.reachability (H:=H)) (radiusB s) (fun z=> clusterCost Z D z * N.markΦ z n) a
        (collars G i s j n*(D*salary Q L μ B s j k*(1-1/2)⁻¹)) := by
  intro x
  have hh:=log_hit_tail _ _ _ H.testS (repriced Z N hD hZ hp ha hs ht) (add_nonneg ha.gain ha.delta.le) 0 x
  simp only [pow_zero,mul_one] at hh
  let v:=collars G i s j n
  have hi:=ha.delta
  have h₀:0≤ shiftG s:= by unfold shiftG; positivity
  have hv:0 ≤ v:= by unfold v collars Reserves.polyPrice; positivity
  have hθ (z:H.fragrances) : 0 ≤ clusterCost Z D z:= by apply Finset.prod_nonneg; rintro i _; apply Finset.prod_nonneg; rintro (i|i) _; exact zero_le_one; exact mul_nonneg (zero_le_one.trans hD) (hZ i)
  have hf:= budget_scale hv hh
  refine budget_mono hf (fun z=> ?_) fun z=> ?_
  · split
    next => exact mul_nonneg (mul_nonneg (hθ z) (mul_nonneg (pow_nonneg (by positivity) _) (N.pvc _))) (Real.exp_pos _).le
    exact le_rfl
  · dsimp only; split
    next hx=>
      rw [if_pos (show 0 ≤ z.fst ∧ x∈unionOf H.smallAt z.snd from ⟨Nat.zero_le _,hx⟩), ← cluster_eq Z]
      let m:=clusterCost Z D z
      let c:ℝ:=coverNumber (radiusB s) (reachability (H:=H) z)
      have hg:0≤c:= Nat.cast_nonneg _
      change m * ((shiftG s*(1+c))^(n*j)*N.design z) * Real.exp (a*c) ≤ v*(m*N.design z*Real.exp ((a+i)*c))
      calc
        _ ≤ m*((shiftG s^(n*j)*(Reserves.polyPrice i (n*j)*Real.exp (i*c)))*N.design z) * Real.exp (a*c) := by
          rw [mul_pow]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (polynomial_cost hi hg _)
              (by positivity)) (N.pvc _)) (hθ _)) (Real.exp_pos _).le
        _ = _ := by rw [add_mul a i c, Real.exp_add]; unfold v collars; ring
    exact hf.1 z

-- version with explicit weighted above used later to pay simultaneous extractions
lemma conditional (hD : 1 ≤ D) (hZ : ∀ i, 0 ≤ Z i) (hp : Supports Z N.conduit) (ha : Armada Q L μ a s i B j k)
    (hs : degreePrice (radiusB s) (D*(Q.costs L μ 1 s 0).rootHit) Q.δ ≤ 1/2)
    (ht : degreePrice (radiusB s) (D*salary Q L μ B s j k) i ≤ 1/2)
    (E : H.fragrances → Prop) (hw : 0 < w) (he : ∀ z, E z → w ≤ clusterCost Z D z) :
    Ac.Hit (Captain.reachability (H:=H)) (radiusB s) (fun z=> if E z then N.markΦ z n else 0) a
        (w⁻¹*(collars G i s j n*(D*salary Q L μ B s j k*(1-1/2)⁻¹))) := by
  intro x
  have h₀:0≤ shiftG s:= by unfold shiftG; positivity
  have he' z : 0≤N.markΦ z n:= mul_nonneg (pow_nonneg (by positivity) _) (N.pvc z)
  have h:=budget_scale (inv_pos.mpr hw).le (at_radii Z N hD hZ hp ha (n:=n) hs ht x)
  refine budget_mono h (fun z=>?_) fun z=> ?_
  · dsimp only; split
    next =>
      apply mul_nonneg _ (Real.exp_pos _).le
      split
      next => exact he' _
      next => rfl
    exact le_rfl
  dsimp only; split
  next hx=>
    by_cases hh:E z
    · rw [if_pos hh]; apply le_trans _ (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (he z hh) (he' z)) (Real.exp_pos _).le)
        (inv_pos.mpr hw).le)
      rw [mul_assoc w, inv_mul_cancel_left₀ hw.ne']
    rw [if_neg hh,zero_mul]; simpa only [hx,if_true] using h.1 z
  simp
end YM.RG01Estimate.Expense
