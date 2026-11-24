import YM.RG01Estimate.Fates
import YM.RG01Estimate.StepRate

/-!
# Second-tier tallies preconditions & numerical purchase

Rate is a comparison to the numeric coupling, not footing per-L charges across
unprepared calendars. The next constructor can request these receipts before
Beta & cuts. Simultaneous over all periods c/f in the specified Teller environment.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Fate
open Function Filter Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Window Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Shoot Precision SectorMeasure Oriented Reserves
open PhysicalNext PhysicalNext.Repeat Height Beam Brim
open Next.Scheduling
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Expense Reprice
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {R : RG.Rep G f} {μ s a α : ℝ} {j m : ℕ} {χ : Chi}
    {H : Cash W s μ L Q o α T R}

/-- Two extra occurrences per requested power (reuse cluster tail). -/
abbrev steps (r:ℕ):ℕ := 3+2*(r+1)
/-- beta grading to be paid, release an extra beta^-1/32 in the intersection tails. -/
def aim (r:ℕ) : ℝ := (r+1:ℕ)/ (2:ℝ)
def spruce (r : ℕ) := -(aim r) - (1/32:ℝ)
def tender (r : ℕ) := -(aim r)+(17/64:ℝ)
def target (r : ℕ) (G : Gauge) (L : Side) (s : ℝ) := betaF G s L ^ spruce r
def debt (r : ℕ) (G : Gauge) (L : Side) (s : ℝ) := betaF G s L ^ tender r
/-- Weight to compensate the inherited vertex. This leaves enough room for the
other vertex in the nonisolated case. -/
def bill (Q : YM.ConnectedActivityE6.Target G P) (r : ℕ) := aim r - (5/16:ℝ) + Q.rate

def wE (Q : YM.ConnectedActivityE6.Target G P) (L : Side) (r : ℕ) (s : ℝ) := betaF G s L ^ bill Q r
def wK (Q : YM.ConnectedActivityE6.Target G P) (L : Side) (r : ℕ) (s : ℝ) := Height.grow G L s * wE Q L r s


/-- Before appointments; K, C all uniform in R, precision high, `frame`
for old-E specialist. -/
def Admission (Q : YM.ConnectedActivityE6.Target G P) (L : Side)
    (W μ a : ℝ) (o : Target.Order G W) (j m r : ℕ) (χ : Chi) (x : ℝ) :=
    let D:=Height.grow G L x
    let Ξ:=target r G L x
    let X:=wE Q L r x; let Y:=wK Q L r x
    1 ≤ betaF G x L ∧ ∀ (c f : Side) (S : StepData c f) (T : Tube G S), Stamp T →
      ∀ (R : Rep G f) (C : ℝ) (H : Cash W x μ L Q o C T R),
      (∃ (C' d v t A b r' B q i : ℝ) (k : ℕ) (N : Captain H j C' d v t A b r' B q k χ),
        Ac.Hit (Captain.reachability (H:=H)) (radiusB x) (fun z=> @ite ℝ (high z (steps r)) (Classical.propDecidable _) (N.markΦ z m) 0) a Ξ ∧
        Armada Q L μ a x i B j k) ∧
      ∀ E : Set ℕ, Inherit.Debits R E (debt r G L x) →
        ∃ (C' d v t A b r' B q : ℝ) (k : ℕ) (N : Captain H j C' d v t A b r' B q k χ),
          let Z z:= D^2*X ≤ clusterCost (H:=H) (Reprice.weigh c f E X Y) D z
          1≤X ∧ 1≤D ∧ Ac.Hit (Captain.reachability (H:=H)) (radiusB x) (fun z=> if Z z then N.markΦ z m else 0) a Ξ

section
variable (Q : YM.ConnectedActivityE6.Target G P) (hv : Q.rate+3/8<0)

private lemma ptr (r : ℝ) (u:ℕ) (G : Gauge) (L : Side) :
    Rate G L (-r*(u:ℝ)) (fun x=> ((betaF G x L ^ r)⁻¹)^u) := by
  suffices h : Rate G L (-r) (fun x=> (betaF G x L^r)⁻¹) from h.pow _
  apply Rate.power.congr; filter_upwards [Delay.shift_pos G L] with x hx
  rw [Real.rpow_neg hx.le]
include hv in
private lemma circling (a : ℝ) (ha : 0≤a)(hp:a<Q.exp) (hm : 0<μ) {B:ℝ→ℝ}(hB:Rate G L 0 B) (j k m : ℕ) :
    ∃ i : ℝ,
      Rate G L Q.rate (fun s=> collars G i s j m*(salary Q L μ (B s) s j k*(1-1/2)⁻¹)) ∧
        ∀ᶠ x in atTop, 1 ≤ betaF G x L ∧ 1≤grow G L x ∧ Armada Q L μ a x i (B x) j k ∧
          degreePrice (radiusB x) (grow G L x*(Q.costs L μ 1 x 0).rootHit) Q.δ ≤ 1/2 ∧
          degreePrice (radiusB x) (grow G L x*salary Q L μ (B x) x j k) i ≤ 1/2 := by
  obtain ⟨i,hg,h⟩:= Armada.ensemble Q L hm a ha hp j k hB
  have hs : Rate G L Q.rate (fun x=>salary Q L μ (B x) x j k) := by
    have he:= ((Rate.const 1).add (hB.mul_left (2^j:ℝ))).mul (Q.rate_none L hm 0 k 0); rw [zero_add] at he; exact he
  have hu:= pressureYoung G L (i:=i) hs (by linarith only [hv]); have ht:= pressureYoung G L (i:=Q.δ) (Q.rate_root L hm (β:=1) (C:=0)) (by linarith only [hv])
  refine ⟨i, by simpa using! hg m 0,?_⟩
  filter_upwards [(YM.Work.E09.betaF_growth G L).eventually_ge_atTop 1,h, hu, ht] with x hx h hp hv
  exact ⟨hx,Real.one_le_rpow hx (by norm_num),h,hv,hp⟩

-- assign the kinetic Beacons arbitrary exponent without reference to the actual trajectory.
private lemma sails (n : ℕ) (Q : YM.ConnectedActivityE6.Target G P) (L : Side) (μ : ℝ) (hm : 0<μ) :
    ∀ᶠ x in atTop, Height.grow G L x ^ n ≤ Real.exp (Q.mark L μ x) ∧ Height.grow G L x ^ n ≤ Real.exp (Q.ε*till x) := by
  have h : Rate G L (3/8*n) (fun x=> Height.grow G L x^n):= (Rate.power (G:=G) (a:=3/8)).pow _
  let v:= -1 - (3/8:ℝ)*n
  have he (u w:ℝ→ℝ)(hy:Rate G L v u)(ht : ∀ x,u x= (Real.exp (w x))⁻¹):∀ᶠ x in atTop, Height.grow G L x ^ n ≤ Real.exp (w x):= by
    filter_upwards [(h.mul hy).below (by unfold v; ring_nf; norm_num) 1 zero_lt_one] with x hx
    have hv:= (le_abs_self _).trans hx
    rw [ht,← div_eq_mul_inv] at hv; exact (div_le_one (Real.exp_pos _)).mp hv
  have hp : Rate G L v (fun x=> Real.exp (-Q.mark L μ x)) := by
    apply (Rate.monitor_cutoff (show 0<μ/4 by linarith) (show (0:ℝ)<2 by norm_num)).congr
    apply Eventually.of_forall; intro x; dsimp only; rw [Real.rpow_two]; change Real.exp (- Delay.hatWin _ _ _ _ _) = _
    -- likely defeq lhs opposite
    unfold Delay.hatWin; congr 1; ring
  have hT := Rate.cutoff (G:=G) (L:=L) Q.usable (a:=v)
  exact (he _ _ hp (fun x=> Real.exp_neg _)).and (he _ _ hT (fun x=> by rw [neg_mul]; exact Real.exp_neg _))

lemma expense_pos (r : ℕ) (hr : 2≤r) : 0 ≤ bill Q r := by
  unfold bill aim
  have hv:= Q.start
  push_cast; have h : (2:ℝ) ≤ r := Nat.cast_ofNat (R:=ℝ) (n:=2) ▸ (Nat.cast_le.mpr hr : ((2:ℕ):ℝ) ≤ r)
  linarith only [h,hv]

lemma admit_stage (Q : YM.ConnectedActivityE6.Target G P) (hv : Q.rate+3/8<0) :
    ∃ n : ℕ, ∀ L : Side, n ≤ L.val → ∀ (W μ a:ℝ), 0<W → 0<μ → 0≤a → a<Q.exp →
      ∀ (o : Target.Order G W) (j m r : ℕ), 2≤r → ∀ χ,
        ∀ᶠ x in atTop, Admission Q L W μ a o j m r χ x := by
  obtain ⟨i,hI⟩:= takeover P Q
  obtain ⟨k,hK⟩:= Passport.passport P Q
  refine ⟨max i k,fun L hL W μ a hw hm ha hz o j m r hr χ=>?_⟩
  have hk:∀ᶠ x in atTop,1 ≤ betaF G x L := (YM.Work.E09.betaF_growth G L).eventually_ge_atTop _
  by_cases he : ∃ D : Patch,D.L=L ∧ D.J=P.j ∧ D.Branches P.bind G
  swap; · exact hk.mono fun x hx=> ⟨hx,fun _ _ S T _ R C H=> (he ⟨S.patch,H.laws.data.funds.length_eq,H.laws.data.funds.funds.atStep,H.laws.data.funds.funds.kernel⟩).elim⟩
  obtain ⟨D,hD,hF,Hd⟩:= he
  obtain ⟨A₀,a₀,C,d,v,t,r',B,q,l,hB,-,hp⟩:= hI L ((le_max_left ..).trans hL) D Hd j χ W hw μ hm o
  obtain ⟨i',hO,hpa⟩:= circling Q hv a ha hz hm hB j l m
  have htR : Rate G L (- (3/8:ℝ)*(steps r)) (fun x=> (Height.grow G L x^steps r)⁻¹) := by
    simp_rw [← inv_pow]; exact ptr (3/8:ℝ) (steps r) G L
  let X:= wE Q L r; let Y:= wK Q L r
  have ht:Rate G L (3/8) (Height.grow G L):= Rate.power
  have hh:Rate G L (bill Q r) X:= Rate.power
  have hE:∀ᶠ x in atTop,1 ≤ X x:= hk.mono fun x hx=> Real.one_le_rpow hx (expense_pos Q r hr)
  have hg:∀ᶠ x in atTop,1≤Y x:= (hk.and hE).mono fun x hx=> one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hx.1 (by norm_num)) hx.2
  have hG : Rate G L (tender r) (debt r G L):= Rate.power
  obtain ⟨A',a',C',d',v',t',r'',B',q',l',hB',hp'⟩:= hK L ((le_max_right ..).trans hL) D Hd _ _ _ (by unfold bill tender; linarith only : tender r+bill Q r < Q.rate) (add_nonneg (by norm_num : 0 ≤ (3/8:ℝ)) (expense_pos Q r hr)) _ X Y hG hh (ht.mul hh) hE hg χ j W μ hw hm o
  obtain ⟨i'',hO',hpa'⟩:= circling Q hv a ha hz hm hB' j l' m
  let u x:= Height.grow G L x ^2 * X x
  have hU : Rate G L (- (3/8:ℝ)* (2:ℕ)+ -(bill Q r)) (fun x=> (u x)⁻¹):= by
    have hv' : Rate G L (-(bill Q r)) (fun x=> (X x)⁻¹):= by
      apply Rate.power.congr; filter_upwards [Delay.shift_pos G L] with x hx
      rw [Real.rpow_neg hx.le]; rfl
    apply Rate.congr (hv'.mul (ptr (3/8:ℝ) 2 G L)|>.weaken (le_of_eq (add_comm _ _)))
    filter_upwards with x; unfold u; rw [mul_inv_rev]; rw [grow]; simp
  have h₁ : -(3/8:ℝ)*steps r+(3/8+Q.rate)<spruce r:= by unfold spruce aim steps; push_cast; have h:0≤(r:ℝ):= Nat.cast_nonneg _; linarith only [hv,h]
  have h₂ : -(3/8:ℝ)*(2:ℕ)+ -(bill Q r)+(3/8+Q.rate)<spruce r:= by unfold spruce bill; push_cast; linarith only
  filter_upwards [hp, hp',hpa,hpa',htR.mul (ht.mul hO) _ h₁,hU.mul (ht.mul hO') _ h₂,hE,
    sails (steps r) Q L μ hm] with x hx hx' ⟨hx₀,hθ,hA,hy,hh₀⟩ ⟨_,_,hA',_,hh₁⟩ he' hf hv' ⟨hΨ,hΩ⟩
  unfold Admission
  intro D₀ Ξ X Y'
  refine ⟨hx₀,fun c f S T hT R Cx H=> ?_⟩
  have hS:= H.laws.data.funds.patch hD hF
  obtain ⟨N,hN⟩:= hx c f S T hS hT R Cx H
  constructor
  · refine ⟨C,d x,v x,t x,A₀,a₀,r' x,B x,q x,i',l,N,?_,hA⟩
    intro i
    apply budget_loosen (VacuumCensus.charge_predicate N _ (Height.grow G L x^steps r) hA hθ hN hy hh₀
      (pow_pos (zero_lt_one.trans_le hθ) _) (fun _ h=> rich _ _ hθ hΨ hΩ h) i)
    have he := (le_abs_self _).trans he'
    unfold Ξ target; apply le_trans _ he; apply le_of_eq; ring
  intro E hE
  obtain ⟨N,hP⟩:= hx' c f S T hS hT R _ H E hE
  refine ⟨C', d' x,v' x,t' x,A',a',r'' x,B' x,q' x,l',N,?_⟩; intro x'
  refine ⟨hv',hθ,fun i=>?_⟩; apply budget_loosen (conditional (Reprice.weigh c f E (wE _ _ _ x) (wK _ _ _ x)) N hθ
    (fun i=> zero_le_one.trans (ones E hv' (one_le_mul_of_one_le_of_one_le hθ hv') _)) hP hA' hy hh₁ x'
    (show 0<u x from mul_pos (pow_pos (zero_lt_one.trans_le hθ) _) (zero_lt_one.trans_le hv')) (fun i hi=> hi) i)
  have hg:= (le_abs_self _).trans hf; unfold Ξ target; apply le_trans _ hg; apply le_of_eq; ring
end
end YM.RG01Estimate.Fate
