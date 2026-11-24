import YM.WilsonCoeffUV.Flat.Mean

/-!
# All flat kernel prices for the W-primer
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV
open Filter Function Lattice RG Laurent Exterior Bloch Metric Matrix Precision Stationary
open Next.Free Tree Work.F08 FreeResolvent
open scoped Topology BigOperators ComplexConjugate
variable {G : Gauge} {K : KernelChoices}

-- gap on real actual off-tree slots
lemma vacuum_positive (k : ℝ) (hk : 0<k) {j:ℕ} (hj:4≤j) : ∃ a:ℝ, 0<a ∧ ∀ v:Train j,
    let H:=record (pulse k v)
    ∀ f,(H.acts f).transpose=H.acts f ∧ FreeResolvent.Gap (H.acts f) a := by
  have he := (heart_heats k hk hj (id : Train j → Train j)).1
  obtain ⟨v,A,hv,hA,h⟩ := he.funds
  refine ⟨v,hv,?_⟩
  intro i H f
  obtain ⟨h,hp⟩ := obey_band _ (he.stock.whole i) (h i) f
  exact ⟨h,⟨fun x=> (hp x).1⟩⟩

lemma canonical_gap (A:Levels G) {c f:Side} (m N : ℕ) (hc:f.val=c.val*(loose A m).L.val) :
    let S:StepData c f := ⟨loose A m,A.clock.kernel,hc⟩
    Bid.Larger (G:=G) S →
    let F:=treeMatrix G S (repeatF S) (freeForms A N (m+1)); F.transpose=F ∧ ∃ e>0, FreeResolvent.Gap F e := by
  intro S h F
  obtain ⟨e,he,H⟩ := vacuum_positive _ A.clock.kernel.penalty_pos (A.clock.adm (m+1))
  obtain ⟨hx,hb⟩ := H (location A N (m+1)) f
  have hp := tree_gap S (repeatF S) _ h he hb
  refine ⟨?_, _,treeFare_pos _ _ _ he,hp⟩
  unfold F treeMatrix freeForms; rw [transpose_submatrix,full_symmetric _ hx]

-- express schedule step estimates on common Patch S by attaching an equality. Use helper functions for dependent substitution (η cap)
structure Covered (A:Levels G) (m:ℕ) (σ C : ℝ) : Prop where
  actual : ∀ N ≥ m+1,
    (conditional A N m).strip σ C ∧ (feedA A N m).strip σ C ∧ (angle G (loose A m) (gaugedA G _ (predictionA A N m))).strip σ C
  gap : ∀ i, m+1 ≤ i → ∀ N N', i ≤ N → i ≤ N' →
    let v := Extension.UV.Linear.Dcost A.clock.kernel.penalty (A.clock.J i)*(A.S.a i/A.S.a (m+1))
    (minusRows (conditional A N m) (conditional A N' m)).strip σ (C*Real.sqrt v) ∧
      (minusRows (feedA A N m) (feedA A N' m)).strip σ (C*Real.sqrt v)

lemma advance_cap (k : ℝ) (hk : 0<k) {j t : ℕ} (hj : 4 ≤ j) (ht : 4 ≤ t) : ∃ σ C:ℝ, 0<σ ∧ 0<C ∧
    ∀ (P:Flight j t) (u : List Axis), u.length≤j-2 → (advanceC P.L (P.duo k).A0 u).strip σ (C/(P.L.val:ℝ)^(1+u.length)) :=
    (secure_both k hk hj ht).1.honored hj _
lemma advance_actual (k : ℝ) (hk : 0<k) {j t : ℕ} (hj : 4 ≤ j) (ht : 4 ≤ t) : ∃ σ C:ℝ, 0<σ ∧ 0<C ∧
    ∀ (A:Levels G) (m N : ℕ), A.clock.kernel.penalty=k → A.clock.J m=t → A.clock.J (m+1)=j →
    ∀ u : List Axis, u.length≤j-2 → (advanceC _ (predictionA A N m) u).strip σ (C/((loose A m).L.val:ℝ)^(1+u.length)) := by
  obtain ⟨σ,C,hσ,hC,h⟩ := advance_cap k hk hj ht
  refine ⟨σ,C,hσ,hC,?_⟩
  intro A m N he hm hn u hx
  subst k j t
  exact h (destination A N m) u hx

private lemma angleD (P:Patch) (G:Gauge) {B η:ℝ} (hp:0<B) (he:0<η) : ∃ F:ℝ,0 < F ∧
    ∀ Q:PoleRows P, Q.strip η B → (angle G P (gaugedA G P Q)).strip η F := by
  obtain ⟨a,ha,h⟩ := climbS_paid (G:=G) (P:=P) (η:=η)
  obtain ⟨b,hb,k⟩ := copyS_paid (G:=G) (P:=P) (η:=η)
  obtain ⟨d,hd,l⟩ := fixS_paid (G:=G) (P:=P) (η:=η)
  let M:=Fintype.card (Co P.L (PAC G 1))
  let N:=Fintype.card (PAC G 0)
  let F:ℝ:= M*(a*B)+ N*(b*(M*(d*B)))
  refine ⟨max F 1,lt_max_of_lt_right one_pos,fun Q hv=>?_⟩
  have hy : (gaugedA G P Q).strip η B := coloration_paid _ _ _ hp.le hv
  exact fun i j=> ((strip_minus (strip_compose he.le h hy) (strip_compose he.le k (strip_compose he.le l hy))) i j).mono le_rfl (le_max_left F _)

private lemma paid_one (G:Gauge) (K:KernelChoices) {j:ℕ} (P:Patch) (h:P.J=j) (hK:P.Branches K G)
    {t : ℕ} {δ σ η X C D:ℝ} (hx : 0<η) (hv : η ≤ σ) (hw: η≤δ) (hg : 0<X) (_hd:0<D) (hC:0<C)
    (hu : ∀ v:Train j, let H:=record (pulse K.penalty v);
                        (∀ (c f : Side) (hc:f.val=c.val*P.L.val), let S : StepData c f := ⟨P,K,hc⟩; IsUnit (treeMatrix G S (repeatF S) H).det) ∧
                        (gamma G P K H).strip σ D ∧ WickLine P G K H (gamma G P K H))
    (hf : ∀ (A:Levels G) (m : ℕ), A.clock.J m=j → A.clock.kernel.penalty=K.penalty →
            (∀ n,(freeForms A n m).strip η X) ∧
            ∀ i,m ≤ i → ∀ n n', i ≤ n → i ≤ n' →
                (minusRows (freeForms A n m) (freeForms A n' m)).strip η (X*Real.sqrt
                    (Extension.UV.Linear.Dcost K.penalty (A.clock.J i)*(A.S.a i/A.S.a m))))
    (hp : ∀ (A:Levels G) (m N : ℕ), A.clock.kernel.penalty = K.penalty → A.clock.J m=t → A.clock.J (m+1)=j →
                   (predictionA A N m).strip δ (C/((loose A m).L.val:ℝ))) :
    ∃ E:ℝ, 0<E ∧ ∀ (A:Levels G) (m:ℕ), loose A m=P → A.clock.kernel=K → A.clock.J m=t → Covered A m η E := by
  obtain ⟨c,hc,HC⟩ := probe_pay G P K.penalty hx.le
  obtain ⟨F,hF,q⟩ := angleD P G hC hx
  let n:ℝ := Fintype.card (Co P.L (PAC G 1))
  let z := n*(n*(D*padCost P η X)*D)
  refine ⟨max (max F (max D (n*(D*c)))) (max z (n*(z*c))),lt_max_of_lt_left (lt_max_of_lt_left hF),?_⟩
  intro A m he ha hj
  subst P K
  have hh : A.clock.J (m+1)=j := h
  subst t j
  let E := max (max F (max D (n*(D*c)))) (max z (n*(z*c)))
  have h₁ : n*(D*c)≤E := (le_max_right ..).trans ((le_max_right ..).trans (le_max_left ..))
  have hD : D≤E := (le_max_left ..).trans ((le_max_right ..).trans (le_max_left ..))
  have ht : F ≤ E := (le_max_left ..).trans (le_max_left ..)
  have hζ : z ≤ E := (le_max_left ..).trans (le_max_right ..)
  have h₂ : n*(z*c)≤E := (le_max_right ..).trans (le_max_right ..)
  have h (N) : (conditional A N m).strip η D := strip_mono (hu (location A N (m+1))).2.1 hv le_rfl
  constructor
  · intro N hN; refine ⟨strip_mono (h N) le_rfl hD,strip_mono (strip_compose hx.le (h N) HC) le_rfl h₁,?_⟩
    have H := hp A m N rfl rfl hh
    exact strip_mono (q _ (strip_mono H hw (div_le_self hC.le (by exact_mod_cast (loose A m).L.property)))) le_rfl ht
  intro i hi N N' hn hn' v
  have hJ := cond_laws A m N; have hV := cond_laws A m N'
  have ha' := hf A (m+1) hh rfl
  have hy : (minusRows (conditional A N m) (conditional A N' m)).strip η (z*Real.sqrt v) := by
    have H' := resolvent_paid hJ.2.2 hV.2.2 hJ.1 hV.1 hx.le (show 0 ≤ X * Real.sqrt v from by positivity) (h N) (h N')
      (ha'.2 i hi N' N hn' hn) ⟨_,_,hx,(ha'.1 N')⟩ ⟨_,_,hx,(ha'.1 N)⟩
    refine strip_mono H' le_rfl (le_of_eq ?_)
    unfold z n; rw [pad_linear]; ring
  refine ⟨strip_mono hy le_rfl (mul_le_mul_of_nonneg_right hζ (by positivity)),?_⟩
  exact strip_mono (degree_bill hJ.2.1 hV.2.1 HC hx hy) le_rfl (by
     apply le_trans (b:=n*(z*c)*Real.sqrt v) (le_of_eq (by unfold n; ring)); exact mul_le_mul_of_nonneg_right h₂ (by positivity))

/-- Overlap constants: σ chosen per neighbor pair J before patch/block, then
B=B(P,j,t,K) post-L, uniform in all A, levels and tops (with end cost at i). -/
theorem schedule_flat (K:KernelChoices) (G:Gauge) (j t : ℕ) (hj:4≤j) (ht:4≤t) :
    ∃ σ:ℝ, 0<σ ∧ ∀ P:Patch,P.J=j → P.Branches K G →
    ∃ B:ℝ,0<B ∧ ∀ (A:Levels G) (m:ℕ), loose A m=P → A.clock.kernel=K → A.clock.J m=t →
       Covered A m σ B := by
  let k:=K.penalty
  obtain ⟨σ,hσ,h⟩ := actually_gamma K G j hj
  obtain ⟨u,c,hu,hc,g⟩ := forms_tail k K.penalty_pos j hj
  obtain ⟨δ,D,hd,hD,hB⟩ := advance_actual (G:=G) k K.penalty_pos hj ht
  set η := min σ (min u δ)
  have hη := lt_min hσ (lt_min hu hd)
  have he : η≤u := (min_le_right ..).trans (min_le_left ..); have hh : η≤δ := (min_le_right ..).trans (min_le_right ..)
  refine ⟨η,hη,?_⟩
  intro P hP hK
  obtain ⟨E,hE,H⟩ := h P hP hK
  apply paid_one G K P hP hK hη (min_le_left ..) hh hc hE hD H (fun A m h h' => ?_) fun A m N h ha he=> ?_
  · have hy := g A m h h'
    exact ⟨fun n=>strip_mono (hy.1 n) he le_rfl, fun i hv n n' => fun hn hn'=> strip_mono (hy.2 i hv n n' hn hn') he le_rfl⟩
  have hv := hB A m N h ha he [] (Nat.zero_le _)
  simpa only [advanceC, List.length_nil,Nat.add_zero,pow_one] using hv
end YM.WilsonCoeffUV
