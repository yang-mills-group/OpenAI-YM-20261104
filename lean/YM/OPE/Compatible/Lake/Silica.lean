import YM.OPE.Compatible.Lake.Fare
/-! Guard norms of output route. Procure Φ after selecting f. Uniform params. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Lake
open Function Filter MeasureTheory Spec Lattice RG Word Cov Allot MergeProof Next.Extract Dash Extra.Histories
open Next.Rank Next.Rank.Price Extraction
open ContinuousLinearMap
open scoped Topology Classical BigOperators
variable {d k N D:ℕ}{G:Gauge}{C:Family G}{T:C.Makes}{E: Fin (d+1)→Type} [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedSpace ℂ (E i)]
local notation "F"=> C.label d
local notation "L"=> C.labels.level d
variable {Q:ℕ→ C.label d ≃L[ℂ] C.label d}{φ:Filter (ℕ×ℕ)}[φ.NeBot]{H:Extraction.Order}(M:Conic T φ Q)
variable (h:φ ≤ H.fuse)
variable {W : Table C.book}{J:ℕ→ W.Field d ≃L[ℂ] Dock E}
-- both min & main
structure Coach (C:Family G) (W:Table C.book)(k D:ℕ) (E: Fin (d+1)→Type)[∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℂ (E i)]
   (Q:ℕ→ C.label d ≃L[ℂ] C.label d) (J:ℕ→ W.Field d≃L[ℂ] Dock E) :Prop where
    rides : Road C k D (fun i=> (J (i+1)).symm.trans (J i))
    head i : k ≤ i → ∀ v:C.label d, ‖J i (W.project d v)‖ ≤ β C i^D * chargeTerm d v (Q i)
    lift i : k ≤ i → ∀ x:Dock E, ∃ v:C.label d,J i (W.project d v)=x ∧ chargeTerm d v (Q i) ≤ β C i ^ D * ‖x‖
namespace Coach
variable (Z: Coach C W k D E Q J)
variable (κ: Services C H W) (hk:C.ref d ≤ k)
include h hk Z M
-- inward.logν weak
lemma pennant (x:F) (hm:k ≤  N): ∃ v:C.label d, W.project d v=W.project d x ∧ chargeTerm d v (Q N) ≤ (β C N^D)^2*(((d+1:ℕ):ℝ)* (OPE.Columns.juice C.path.levels k)*(L).coeffSize x):=by
    let q i:= J i (W.project d x)
    obtain ⟨v,he,hv⟩:= Z.lift N hm (q N); refine ⟨v,(J N).injective he,hv.trans ?_⟩
    have h1 : ‖q k‖≤ _ := (Z.head k le_rfl x).trans (mul_le_mul_of_nonneg_left (up_bound T M h hk x) (pow_nonneg (β_pos C _).le _))
    have ht:= Z.rides.flight hm q (fun i _=> by dsimp only [q]; simp)
    let t:= β C N^D; let r:= β C k^D; have hh :0<r:=pow_pos (β_pos ..) _;have ht':0<t:=pow_pos (β_pos ..) _
    let s:ℝ:= ((d+1:ℕ):ℝ)
    let f:= s*(OPE.Columns.juice C.path.levels k)*(L).coeffSize x; change t*‖q N‖ ≤ t^2*f
    have he': ‖q N‖ * r ≤ s * ‖q k‖*t:= (mul_le_mul_of_nonneg_right (board (q N)) hh.le).trans (ht.trans (mul_le_mul_of_nonneg_right (boardTicket (q k)) ht'.le))
    have hy: ‖q N‖ ≤ t*f := le_of_mul_le_mul_right (by unfold f; linarith only [he',mul_le_mul_of_nonneg_left h1 (show 0 ≤ s*t from mul_nonneg (by unfold s; positivity) ht'.le)]) hh
    exact (mul_le_mul_of_nonneg_left hy ht'.le).trans_eq (by ring)
-- price out use SectorCost
variable {P:DiffPlan W}{e:ℕ} (pi:P.Inclusions W) (u:W.Field d→L[ℂ]ℂ) (hV:∀ j:ℕ,j < e→∀ h:j ≤ d,∀ y:W.Field j,u (P.rise h y)=0) (he:e ≤ d)
include hV pi he κ
lemma ensign (hm:k ≤  N) (x:C.label d):
   ‖u (W.project d x)‖*C.S.a N ^ (d-e) ≤ ((2*((d+1:ℕ):ℝ)* ‖u.comp (LinearMap.toContinuousLinearMap (W.project d))‖) *outward C d k *C.S.a k^(d-e))*(β C N ^ D)^2 * chargeTerm d x (Q N):=by
     let v i:= u.comp (J i).symm.toContinuousLinearMap
     have hz (m:ℕ) : v (m+1)=(v m).comp (((J (m+1)).symm.trans (J m)).toContinuousLinearMap):=by unfold v; ext1; simp
     obtain ⟨c,hc,hC,hD⟩:= spotted M h pi u κ hV he
     have hW (i:ℕ) (h:k ≤ i) : ‖v i‖ ≤ c i*β C i^D:=by
        have hp : 0 ≤ β C i:= (β_pos C i).le
        refine opNorm_le_bound _ (mul_nonneg (hc i) (pow_nonneg hp _)) (fun p=>?_)
        obtain ⟨w,hw,hh⟩:= Z.lift i h p; change ‖u ((J i).symm p)‖ ≤ _; rw [show _=W.project d w from (J i).symm_apply_eq.mpr hw.symm]; apply (hD i (hk.trans h) w).trans; linarith only [mul_le_mul_of_nonneg_left hh (hc i)]
     have ht: RateLE atTop C.S.scale v (d-e:ℕ):=by
        apply RateLE.of_norm_le (f:=fun i=> c i*β C i^D) ?_ ((eventually_ge_atTop k).mono hW); simpa only [mul_zero,add_zero] using hC.mul (((plateau κ.simpleGate).power D).pays C.S.divergent)
     let y:= u.comp (LinearMap.toContinuousLinearMap (W.project d));let α:=outward C d k; have ha:=outward_nn C d k; have ha':0≤α:= zero_le_one.trans ha
     let r:=β C k^D; let t:= β C N^D; have hr:0<r:= pow_pos (β_pos ..) _; have hT:0<t:=pow_pos (β_pos ..) _
     have hv0: ‖v k‖ ≤ ‖y‖ *α*r:=by
        apply opNorm_le_bound _ (by positivity); intro p
        obtain ⟨w,hp,hL⟩:= Z.lift k le_rfl p; change ‖u ((J k).symm p)‖ ≤ _; rw [show _=W.project d w from (J k).symm_apply_eq.mpr hp.symm]
        apply (y.le_opNorm w).trans; have hh : ‖w‖ ≤ α*(r*‖p‖):=(Size.norm_le _ _).trans ((down_bound T M h hk _).trans (mul_le_mul_of_nonneg_left hL ha')); linarith only [mul_le_mul_of_nonneg_left hh (norm_nonneg y)]
     let f:= J N (W.project d x); change _ ≤ (2*_ * ‖y‖ *α* _) *t^2*_
     have hB: shelf (v N) e * C.S.a N^(d-e)*r ≤ _ := Z.rides.highBill (fun i _=>hz i) he ht hm
     let A:= C.S.a N^(d-e); let B:= C.S.a k^(d-e); let n:ℝ:= ((d+1:ℕ):ℝ); have hβ:0<B:=pow_pos (C.S.a_pos _) _; have hα:0<A:=pow_pos (C.S.a_pos _) _
     have hh: ‖v N‖ *A ≤ 2*n*‖y‖*α*B*t:=by
        have hγ : 0 ≤ courtyard (v k) e:= Finset.sum_nonneg fun _ _=> norm_nonneg _
        have heq : shelf (v k) e ≤ n*‖v k‖:= calc
           _ ≤ income (v k):=by rw [field_merger (v k) e]; linarith
           _ ≤ _:= boardRowTicket _
        have hc : ‖v N‖ ≤ 2*shelf (v N) e:=by apply (boardRow _).trans; rw [field_merger _ e]; have hi:=Z.rides.rests (fun i _=>hz i) he ht hm; linarith only [hi]
        apply le_of_mul_le_mul_right _ hr
        change shelf (v N) e*A*r ≤ shelf (v k) e*B*t at hB; linarith only [mul_le_mul_of_nonneg_right hc (mul_nonneg hα.le hr.le), hB, mul_le_mul_of_nonneg_right heq (mul_nonneg hβ.le hT.le), mul_le_mul_of_nonneg_left hv0 (mul_nonneg (mul_nonneg (show 0 ≤ n by unfold n; positivity) hβ.le) hT.le)]
     have heq: v N f=u (W.project d x):=by simp [v,f]
     rw [← heq]; refine (mul_le_mul_of_nonneg_right ((v N).le_opNorm f) hα.le).trans ?_
     have ht' : 0 ≤ 2*n*‖y‖*α*B*t:=by
        have hn:0≤ n:=by dsimp [n]; positivity
        positivity
     linarith only [mul_le_mul_of_nonneg_right hh (norm_nonneg f), mul_le_mul_of_nonneg_left (Z.head N hm x) ht']
end Coach
end YM.OPE.Lake
