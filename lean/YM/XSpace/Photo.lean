import YM.XSpace.Financing
/-! # Portrait & kernel limits in the safe geometry, through readings. -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Photo
open Function Set Filter Structure1 Cirrus Normalize PowerSeries Retirement MeasureTheory Maxwell Future Stall Metric
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge} {d n:ℕ} (W:Initialize G)(V:Store G)(d:ℕ)(p:Tags G d n)(c:Shade.Cut)
section
variable {Y:Sample n→ Point G d n}(K:Set (Points n))
def Positive (Y: Cirrus.Sample n→ Point G d n) := ∀ p:Tags G d n,∀ x∈K,Likely (Gate x) (fun i=>Y i p)
def mature (Y:Cirrus.Sample n→Point G d n)(H: Positive d K Y) (x:Points n):Point G d n:=by
  by_cases h:x∈K; swap; · exact 0
  let f (p:Tags G d n) := (H p x h).choose; refine MultilinearMap.mk' f (fun p i a b=>?_) (fun p i a b=>?_)
  · refine tendsto_nhds_unique (f:=fun i=>Y i _) ((H _ x h).choose_spec) ?_; simp_rw [MultilinearMap.map_update_add]; exact (H _ _ h).choose_spec.add (H _ _ h).choose_spec
  refine tendsto_nhds_unique (f:=fun i=>Y i _) ((H _ x h).choose_spec) ?_; simp_rw [MultilinearMap.map_update_smul]; exact (H _ _ h).choose_spec.const_smul _
lemma maturation (H:Positive d K Y): Senses K (fun i=> Y i p) (fun x=>mature d K Y H x p):=by intro x hx; simp only [mature,hx, ↓reduceDIte]; exact (H p x hx).choose_spec
lemma sees_test (g:Test n) (P:Points n→ℂ){Y:Cirrus.Sample n→ℂ} (h:IsOpen K)(S:Senses K Y P)(hs:Centered Y)(hx:tsupport g⊆ K): Tendsto (fun m=> Deposit m Y g) Front (𝓝 (g.applyTo P)):=by
  obtain ⟨b,hb,B⟩:= TestBudget.bound_fin g; apply Metric.tendsto_nhds.mpr; intro e he; refine (graduate Y P h S.priced hx g.hasCompactSupport S hs (e/b/2) (by positivity)).mono fun i hi=>?_ ; specialize hi g (Subset.refl _) b B; rw [dist_eq_norm]; refine hi.trans_lt (lt_of_eq_of_lt ?_ (half_lt_self he)); field_simp
end

def Beyond (a:ℝ) (n:ℕ): Set (Points n):={x| ∀ i j:Fin n,i≠j→ 5*a< ‖x i-x j‖}
abbrev Good (c:Shade.Cut)(n:ℕ):= Beyond c.rOut n
lemma beyond_op (a:ℝ)(n:ℕ): IsOpen (Beyond a n):=by unfold Beyond; simp only [setOf_forall]; apply isOpen_iInter_of_finite; intro i; apply isOpen_iInter_of_finite; intro j; apply isOpen_iInter_of_finite; intro h; apply isOpen_lt continuous_const; fun_prop
lemma beyond_mono {s t:ℝ}(h:s≤t): Beyond t n⊆Beyond s n:=fun x hx i j hv=> lt_of_le_of_lt (mul_le_mul_of_nonneg_left h (by norm_num)) (hx i j hv)
lemma beyond_conf : Good c n⊆conf n:=by intro x hx i j h; by_contra h'; have hh:= hx i j h'; rw [h,sub_self,norm_zero] at hh; linarith [c.rOut_pos]
lemma beyond_ok {x:Points n}(h:x∈ Good c n): Cleared c x.ofLp Finset.univ:= fun i _ j _ ht=> (h i j ht).le

-- picking common geometries. Finite ANY tests across arities.
lemma wishes {K:Set (Points n)}(H:IsCompact K)(hp:K⊆conf n):∀ᶠ r:ℝ in 𝓝[>] 0,K⊆ Beyond r n:=by
  by_cases hx:K=∅; · simp only [hx,empty_subset,eventually_true]
  have he(i j:Fin n):∀ᶠ r:ℝ in 𝓝[>] 0,∀ x∈K,i≠j→ 5*r<‖(x i)-(x j)‖:=by
    by_cases h:i=j; · simp [h]
    let f(x:Points n):= ‖(x i)-(x j)‖; obtain ⟨x,hx,Y⟩:= H.exists_isMinOn (f:=f) (nonempty_iff_ne_empty.mpr hx) (continuousOn_of_forall_continuousAt (fun z _=> by unfold f; fun_prop)); -- check
    have ht:f x>0:= norm_pos_iff.mpr (sub_ne_zero.mpr ((show Injective _ from hp hx).ne h)); filter_upwards [eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds (show 0<f x/5 by positivity))] with i hi z hz hn; apply lt_of_lt_of_le _ (Y hz); linarith
  filter_upwards [eventually_all.mpr fun i=> eventually_all.mpr (he i)] with x hx; exact fun z hz i j=> hx i j z hz

def Granted (V:Store G)(d:ℕ)(c:Shade.Cut):Prop:=∀ i:Fin (V.survey d).n, tsupport ((V.survey d).scope i).t ⊆ Good c ((V.survey d).scope i).n
lemma small_cut {K:Set (Points n)}(H:IsCompact K)(h:K⊆conf n):∃ c:Shade.Cut,K⊆ Good c n ∧ Granted V d c:=by
  obtain ⟨r,hr,hh,hu⟩:=(eventually_all.mpr (fun i=> let t:= ((V.survey d).scope i).t; wishes (K:=tsupport t) t.hasCompactSupport t.tsupport_subset)|>.and ((wishes H h).and self_mem_nhdsWithin)).exists
  exact ⟨⟨r/2,r, (by change r>0 at hu; positivity),half_lt_self hu⟩,hh,hr⟩
lemma structures : Positive d (Good c n) (fallRecords W d c):=fun p x hx=> knows_fall W d p c x (beyond_ok c hx) (beyond_conf c hx)
def orderBasic (x:Points n): Point G d n:= mature d (Good c n) _ (structures W d c) x
lemma basic_test (g:Test n)(hs:tsupport g⊆ Good c n): Tendsto (fun m:Mesh=> batchShift W m (harvest W c d m.spacing).val n g p) Front (𝓝 (g.applyTo (fun x=> orderBasic W d c x p))):= (sees_test (Good c n) g (fun x=> orderBasic W d c x p) (beyond_op ..) (maturation d p (Good c n) (structures W d c)) (fun _ _ _=>rfl) hs).congr fun _=>deposit_shift W p _ _ g (fun m=> (harvest W c d m.spacing).val) rfl
end YM.XSpace.Photo
