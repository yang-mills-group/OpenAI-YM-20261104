import YM.FormalBulk08.Flat.Account

/-!
# A quantitatively priceable quadratic supply I

Nested costs specified using the actual Patch sizes, `Row.strip` and `Levels`,
not a fixed-L history. Gives the rates before any post-L or stronger plateau
restrictions: only numerical cost choices at a stage/pair-of-stages remain to
combine with polynomial/log allowances in schedules.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Flat
open Filter Set Function Lattice Laurent Bloch Exterior Precision RG Next.Free UVExtension.Free Work.F08
open scoped Topology BigOperators
variable {G : Gauge} {t j : ℕ}

def ratioR (S : Schedule) (N i : ℕ) (ξ : ℝ) : ℝ := (S.a N / S.a i)^ξ
lemma ratioR_pos (S : Schedule) (N i) (ξ) : 0<ratioR S N i ξ := Real.rpow_pos_of_pos (div_pos (S.a_pos _) (S.a_pos _)) _
lemma ratioR_le_one (S : Schedule) (N i) (ξ) (hp : i≤N) (hx : 0≤ξ) : ratioR S N i ξ ≤ 1 :=
  Real.rpow_le_one (div_nonneg (S.a_pos _).le (S.a_pos _).le) ((div_le_one (S.a_pos i)).mpr (S.strictAnti.antitone hp)) hx
lemma ratioR_pow (S : Schedule) (N i ξ) (n : ℕ) : ratioR S N i ξ ^ n = ratioR S N i (ξ*n) := by
  unfold ratioR; rw [Real.rpow_mul (div_nonneg (S.a_pos _).le (S.a_pos _).le),Real.rpow_natCast]
lemma ratioR_sqrt (S : Schedule) (N i ξ) : Real.sqrt (ratioR S N i ξ)=ratioR S N i (ξ*(1/2:ℝ)) := by
  unfold ratioR; rw [Real.sqrt_eq_rpow, Real.rpow_mul (div_nonneg (S.a_pos _).le (S.a_pos _).le)]
lemma ratioR_fineR (A : Levels G) (N i : ℕ) (hp : i≤N) : ratioR A.S N i (1/2:ℝ)=fineR A N i := by
  let S:=A.S; let L:=S.steps i (N-i)
  have hh : S.a N / S.a i=(L.val:ℝ)⁻¹ := by
    have h : S.a N*(L.val:ℝ)=S.a i:= S.embeds_scale (S.toDepth hp 0)
    rw [← h]; field_simp [(S.a_pos N).ne']
  unfold ratioR; rw [hh,← Real.sqrt_eq_rpow, Real.sqrt_inv]; rfl
lemma fineR_next (A : Levels G) (N i) (hp : i<N) : fineR A N i ≤ fineR A N (i+1) := by
  rw [← ratioR_fineR A N (i+1) hp,← ratioR_fineR A N i hp.le]
  unfold ratioR
  gcongr
  · exact (div_pos (A.S.a_pos _) (A.S.a_pos _)).le
  · exact (A.S.a_pos _).le
  · exact A.S.a_pos _
  · exact (A.S.strictAnti (Nat.lt_succ_self i)).le

/-- One absolute exponent on all stages and ratios. -/
def targetPower : ℝ := 1/116
lemma targetPower_pos : 0<targetPower := by unfold targetPower; positivity
private def midR (S : Schedule) (N i) := ratioR S N i (1/58 : ℝ)
private lemma midR_real (A : Levels G) (N i) (hp : i≤N) : fineR A N i ≤ (midR A.S N i)^(28+1) := by
  unfold midR; rw [ratioR_pow,← ratioR_fineR A N i hp]; norm_num
private lemma targetRate (S : Schedule) (N i) : Real.sqrt (midR S N i) = ratioR S N i targetPower := by unfold midR targetPower; rw [ratioR_sqrt]; norm_num

structure Demand (G : Gauge) (j : ℕ) where
  A : Levels G
  i : ℕ
  N : ℕ
  M : ℕ
  sizes : i≤N
  mesh : N≤M
  height : A.clock.J i=j
namespace Demand
variable (x : Demand G j)
def up := x.height ▸ location x.A x.N x.i
def next := x.height ▸ location x.A x.M x.i
lemma adapt : HEq x.up (location x.A x.N x.i) ∧ HEq x.next (location x.A x.M x.i) := by
  rcases x with ⟨A,i,N,M,h,hp,rfl⟩
  exact ⟨HEq.rfl,HEq.rfl⟩
lemma probe : Probe Demand.up Demand.next A (i (G:=G) (j:=j)) N M := ⟨sizes,mesh,height,fun x=> x.adapt.1, fun x=> x.adapt.2⟩
end Demand

/-- Diagonal metric ingredient of the formal action (not actual activity
metric and not claiming inverse identities independent of supplied tables).
Width and constants independent even of levels meeting compatible cuts. -/
theorem colors (G : Gauge) (k : ℝ) (hk : 0<k) (hj : 4≤j) :
    ∃ σ C : ℝ, 0<σ ∧ 0<C ∧
       (∀ V : Train j,(pink k V).strip σ C ∧ (blue k V).strip σ C) ∧
       ∀ (A : Levels G) (N M i : ℕ), i≤N → N≤M → A.clock.J i=j →
        let B := C*ratioR A.S N i targetPower
        (minusRows (pink k (location A N i)) (pink k (location A M i))).strip σ B ∧
          (minusRows (blue k (location A N i)) (blue k (location A M i))).strip σ B := by
  obtain ⟨σ,C,hσ,hC,h⟩:=pulsePay k hk hj
  let f (x : Demand G j) := midR x.A.S x.N x.i
  obtain ⟨K,hK,H⟩:= bed_money (Demand.probe (G:=G)) hj k hk f
    (fun x=> ratioR_pos ..) (fun x=> ratioR_le_one _ _ _ _ x.sizes (by norm_num)) (fun x=>midR_real _ _ _ x.sizes) C σ hC hσ h
  have he : σ/4 ≤ σ := by linarith
  refine ⟨σ/4,max C K,by positivity,lt_max_of_lt_left hC,fun V=> ⟨strip_mono (h V).1 he (le_max_left ..),strip_mono (h V).2 he (le_max_left ..)⟩,fun A N M i hh ht hp=> ?_⟩
  subst j; obtain ⟨hA,hB⟩:= H ⟨A,i,N,M,hh,ht,rfl⟩
  have hs := mul_le_mul_of_nonneg_right (le_max_right C K) (ratioR_pos A.S N i targetPower).le
  have hy : K*Real.sqrt (midR A.S N i)≤max C K*ratioR A.S N i targetPower := by rw [targetRate]; exact hs
  exact ⟨strip_mono hA le_rfl hy,strip_mono hB le_rfl hy⟩

structure Adjacent (G : Gauge) (q : Gate j t) where
  A : Levels G
  i : ℕ
  N : ℕ
  M : ℕ
  step : i<N
  mesh : N ≤ M
  color0 : A.clock.J i=t
  color1 : A.clock.J (i+1)=j
  length : A.S.block i=q.L
namespace Adjacent
variable {q : Gate j t} (x : Adjacent G q)
def fine : Demand G j := ⟨x.A,x.i+1,x.N,x.M,x.step,x.mesh,x.color1⟩
lemma transfer : HEq (q.ride x.fine.up) (destination x.A x.N x.i) ∧ HEq (q.ride x.fine.next) (destination x.A x.M x.i) := by
  rcases x with ⟨A,i,N,M,h,e,hj,ht,hl⟩
  subst j t; apply And.intro
  · apply heq_of_eq; change q.ride (location A N (i+1))=stageHop A i (location A N (i+1)); unfold Gate.ride stageHop; simp only [hl]
  · apply heq_of_eq; change q.ride (location A M (i+1))=stageHop A i (location A M (i+1)); unfold Gate.ride stageHop; simp only [hl]

lemma book : Probe (fun x=> Demand.up (fine x)) (fun x=>Demand.next (fine x)) A (fun x=>i (G:=G) (q:=q) x+1) N M :=
    probe_more fine (Demand.probe)
lemma bracket : Probe (fun x=> (q.ride (fine x).up).land) (fun x=> (q.ride (fine x).next).land) A (i (G:=G) (q:=q)) N M := by
  have hx (x : Adjacent G q) : HEq (q.ride x.fine.up).land (location x.A x.N x.i) ∧
      HEq (q.ride x.fine.next).land (location x.A x.M x.i) := by
    obtain ⟨h,hg⟩:=x.transfer
    have hp:= x.color0; have hh:=x.color1
    -- substituting dependent variables may be tricky; recases before subst
    rcases x with ⟨A,i,N,M,h',he,ht,hj,hl⟩; subst j t; clear hp hh
    constructor <;> apply heq_of_eq
    · rw [eq_of_heq h]; exact (loc_land A N i h').symm
    rw [eq_of_heq hg]; exact (loc_land A M i (h'.trans_le he)).symm
  exact ⟨fun x=>x.step.le,mesh,color0,fun x=>(hx x).1,fun x=>(hx x).2⟩
end Adjacent

def RepeatPrices (k σ B : ℝ) (P : Flight j t) : Prop :=
    ∀ s : List Axis, s.length ≤ j-2 →
      (advanceC P.L (Flight.duo k P).A0 s).strip σ (B/(P.L.val:ℝ)^(1+s.length)) ∧
      (advanceC P.L (Flight.duo k P).T s).strip σ (B/(P.L.val:ℝ)^(2+s.length))

def Between (A : Levels G) (N M i : ℕ) (k σ B : ℝ) : Prop :=
    let L:= A.S.block i
    let s:= destination A N i
    let t:= destination A M i
    let T:= B*ratioR A.S N (i+1) targetPower
    ∀ a : List Axis, a.length ≤ A.clock.J (i+1)-2 →
      (minusRows (advanceC L (Flight.duo k s).A0 a) (advanceC L (Flight.duo k t).A0 a)).strip σ T ∧
      (minusRows (advanceC L (Flight.duo k s).T a) (advanceC L (Flight.duo k t).T a)).strip σ T

lemma transfer_buy (q : Gate j t) (ht : 4≤t) (k : ℝ) (hk : 0<k) (σ E : ℝ) (hσ : 0<σ) (hE : 0<E) (hw : ∀ P : Flight j t, RepeatPrices k σ E P) :
    ∃ C : ℝ, 0<C ∧ ∀ (A : Levels G) (N M i), i<N → N≤M → A.clock.J i=t → A.clock.J (i+1)=j → A.S.block i=q.L → Between A N M i k (σ/4) C := by
  classical
  let X (x:Adjacent G q):= midR x.A.S x.N (x.i+1)
  have hx (s:List Axis) (hs : s.length≤j-2) := Gate.cross_money q (Adjacent.book) ht (Adjacent.bracket) X
    (fun x=> ratioR_pos ..) (fun x=> ratioR_le_one _ _ _ _ x.step (by norm_num)) (fun x=>midR_real _ _ _ x.step) (fun x=> (fineR_next x.A x.N x.i x.step).trans (midR_real _ _ _ x.step))
    k hk s hs σ E hσ hE (fun V=> ⟨strip_mono ((hw (q.ride V) s hs).1) le_rfl (div_le_self hE.le (one_le_pow₀ (by exact_mod_cast q.L.property))), strip_mono ((hw (q.ride V) s hs).2) le_rfl (div_le_self hE.le (one_le_pow₀ (by exact_mod_cast q.L.property)))⟩)
  let β := {s : List Axis // s.length ≤ j-2}
  letI : Fintype β := (Secured.limited_lengths (j-2)).fintype
  choose C hC H using fun i : β=> hx i.val i.property
  let B:=1+∑ i,C i
  have hz : 0 < B := lt_of_lt_of_le one_pos (le_add_of_nonneg_right (Finset.sum_nonneg fun i _=> (hC i).le))
  refine ⟨B,hz,fun A N M i hp hm e1 e2 hL=> ?_⟩
  let y:Adjacent G q:=⟨A,i,N,M,hp,hm,e1,e2,hL⟩
  intro v hv
  subst j t
  let b:β:=⟨v,hv⟩
  have HE := H b y
  have hr : C b *Real.sqrt (X y) ≤ B * ratioR A.S N (i+1) targetPower := by
    change C b *Real.sqrt (midR A.S N (i+1)) ≤ _
    rw [targetRate]; gcongr
    · exact (ratioR_pos ..).le
    exact (Finset.single_le_sum (f:=C) (fun i _=> (hC i).le) (Finset.mem_univ b)).trans (by unfold B; linarith)
  rcases q with ⟨⟨L,h1,h2,h3,h4,h5,T⟩⟩; change A.S.block i=L at hL; subst L
  -- now HE transfers by definitional equality
  exact ⟨strip_mono HE.1 le_rfl hr,strip_mono HE.2 le_rfl hr⟩

/-- Pre-L widths and bounds, and post-block constant in the mesh defect in
that width (including requested difference words). -/
theorem transports (G : Gauge) (k : ℝ) (hk : 0<k) (hj : 4 ≤ j) (ht : 4≤t) :
    ∃ σ B : ℝ, 0<σ ∧ 0<B ∧ (∀ P : Flight j t,RepeatPrices k σ B P) ∧
      ∀ L : Side,∃ C : ℝ,0<C ∧
       ∀ (A : Levels G) (N M i : ℕ), i<N → N≤M → A.clock.J i=t → A.clock.J (i+1)=j → A.S.block i=L →
        Between A N M i k σ C := by
  obtain ⟨hA,hB⟩:=secure_both k hk hj ht
  obtain ⟨σ,B,hσ,hp,h⟩:=hA.honored hj 1
  obtain ⟨η,C,hη,hc,H⟩:=hB.honored hj 2
  let u:=min σ η; let E:=max B C
  have hu:0<u:=lt_min hσ hη
  have he:0<E:=lt_max_of_lt_left hp
  have hv (P:Flight j t): RepeatPrices k u E P:= fun s hs=>
    ⟨strip_mono (h P s hs) (min_le_left ..) (div_le_div_of_nonneg_right (le_max_left ..) (pow_nonneg (side_pos _).le _)),
      strip_mono (H P s hs) (min_le_right ..) (div_le_div_of_nonneg_right (le_max_right ..) (pow_nonneg (side_pos _).le _))⟩
  refine ⟨u/4,E,by positivity,he,fun P s hs=>⟨strip_mono (hv P s hs).1 (by linarith) le_rfl,strip_mono (hv P s hs).2 (by linarith) le_rfl⟩,fun L=>?_⟩
  by_cases hx : ∃ q : Gate j t,q.L=L
  · obtain ⟨q,rfl⟩:=hx; exact transfer_buy q ht k hk u E hu he hv
  exact ⟨1,one_pos,fun A N M i _ _ hh hg hy=> by subst j t; exact (hx ⟨Gate.mk (destination A N i),hy⟩).elim⟩
end YM.FormalBulk08.Flat
