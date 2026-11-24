import YM.WilsonBridge.ExpInk
/-!
# Removing the auxiliary antifield variables and reading exact tree-chart jets

No correlation hypotheses. Integrands after A-only projection computed on the
complete cotree chart using the actual `Orb` series. The rank and coupling
series are still distinct!
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBridge.Based.Position
open MS MS.Book MS.Koszul MS.Swirl MS.Puff MS.Cylinder MS.Orbit
open MS.Book.Convolve Program Puff.Mom Puff.Engine Puff.SplitP Puff.Actors Puff.Dynamics Orbit.LogReal Orbit.Cog
open PertExtension GaussianScore Orb Function Finset Lattice MeasureTheory WilsonBridge.Polynomial Native Bare Focus
open PertExtension.Series Radial PertExtension.Series.Tested Cylinder.Taylor Precision Filter
open scoped BigOperators ContDiff Classical Topology
variable {G:Gauge}{n:Side}
local notation "V" => Position.Letter G n
local notation "γ" => Position.glow G n
local notation "WΦ"=> actionW G n
local notation "Q"=> FreeBV.interaction WΦ (haarW G n)
local notation "v" => real_cov (G:=G) (n:=n)
local notation "Tζ" => LinearMap.toContinuousLinearMap (insertCo G n) -- precheck?
def bareH (G:Gauge)(n:Side) : T (Raw (Letter G n) ℂ) := FreeBV.relative (rankLevel 2 (actionW G n))

@[simp] lemma Haar_null : logHaar (0:E G n)=0:= by unfold logHaar; simp [Maurer.lac,LocalH.spin_zero]
private lemma vac0 : rankLevel 0 (haarW G n) 0=0:= by change mask 0 _=0; rw [rank_zero_hat (haarW G n),master.haar_normalized]; funext l; cases l <;> rfl
local notation "L" => rankLevel 0 (haarW G n)
local notation "P"=> Position.Parity G n
lemma clean_log : Happy useN L:= vac0
lemma clean_in : Happy useN (bareH G n):= by change _ - useN.refineV (rankLevel 2 WΦ 0) 0 = _; rw [lone_use]; exact sub_self _
lemma begins : (bareH G n)∈ (PermV P).guard := by
  let S:=rankLevel 2 WΦ; have he:S∈ (PermV P).guard := FreeBV.even_level master.evenW
  exact (PermV P).guard.sub_mem he (refineπ useN (S 0) (Center P|>.zero_mem |> (fun _=>he 0 (Set.mem_univ _)))) -- adjust
lemma grant : Γ (bareH G n) P:= by
  let S:=rankLevel 2 WΦ; have he:Γ S P:= FreeBV.basis_level master.smoothW
  exact (allIndex (FeeP P) ℕ).sub_mem he (refineπ useN _ (he 0 (Set.mem_univ _)))
lemma split_Q : Q=bareH G n + L:= by
    unfold FreeBV.interaction FreeBV.action bareH FreeBV.relative; simp only [Pi.add_apply,vac0, add_zero]; abel -- maybe unfolding order
lemma fee_power {f:T (Raw V ℂ)} (h:Γ f P) (j:ℕ): Γ ((PermV P).power f j) P:= by
    induction j with| zero=> exact refineπ useN _ feeUnit| succ i ih=> exact ΤΓ_pair h ih
lemma fee_Q_offset {i:ℕ}(hi:i≠0) : bareH G n i=rankLevel 2 WΦ i := by
    unfold bareH FreeBV.relative; rw [Pi.sub_apply, SplitP.refineV, if_neg (show i≠ useN.origin from hi),sub_zero]

variable (x:Dir G n)
local notation "ξ" => value (fun i=> (v i x:ℂ))
local notation "ℓ" => chord (fun i=> (v i x:ℂ))
lemma tree_ink {F:E G n → ℝ}(h:germ F) : pull ℓ (ink (γ).e0 F)= ink (fun _:Unit=>x) (F ∘ Tζ):= by
    rw [ink_ctrl_one (fun _:Unit=>x) Tζ h]
    let W (j:V):= v j x; let M : Matrix Unit V ℝ := fun _=>W
    change pull (M.map ((↑):ℝ→ℂ)) _ = _
    apply pull_ink _ _ _ _ h; rintro ⟨⟩; change insertCo G n x=∑ i:Letters _ _, W i • (γ).e0 i
    rw [Fintype.sum_sum_type]; simp_rw [Fintype.sum_sum_type]; change _=((∑ i:Gluon G n, W (a i) • priv i)+(∑ _: Ghost G n,(0:ℝ) • (0:E G n)))+((∑ _:Gluon G n,(0:ℝ) • (0:E G n))+(∑ _:Ghost G n,(0:ℝ) • (0:E G n)))
    simp only [smul_zero,Finset.sum_const_zero,add_zero]; exact (Native.frame _).symm
lemma tree_read (F:E G n → ℝ)(h:germ F) (i:ℕ): ξ (mask i (ink (γ).e0 F)) = (Radial.jet (F ∘ Tζ) i x:ℂ):= by
    rw [at_rank _ i (rankMod (ink (γ).e0 F) i),along_mask,if_pos rfl, along_read, ray, tree_ink x h]; exact local_jet (F ∘ Tζ) (ContDiffAt.comp _ (by rw [map_zero]; exact h) ((Tζ).contDiff.contDiffAt)) (fun _:Unit=>x) _ -- rankMod args
lemma tree_ghost : pull ℓ (Bonded.hung (Position.Bracket G n) (Focus.launch (Position.glow G n) (colorTerm G (BasedSite n)) generator))=0:= by
    let T:= Position.Bracket G n
    unfold Bonded.hung; rw [map_sum]; refine Finset.sum_eq_zero (fun i _=>?_)
    rw [map_smul, pull_prod _ (tied x), pull_letter];
    have he : ∀ j:Unit, ℓ j (T.dual i)=0:= by intro j; rcases i with i|i <;> rfl
    rw [Fintype.sum_unique]; rw [he _]; simp
lemma value_action (i:ℕ): ξ (bareH G n i)=(layers fiscal i x:ℂ):= by
    obtain rfl|h:=eq_zero_or_pos i
    · rw [show bareH G n 0=0 from clean_in,map_zero]; simp
    have he:exponent G n ∘ Tζ= (-1:ℝ) • fiscal := funext fun x=> ((neg_eq_iff_eq_neg.mp (expense_tree x))).trans (by simp)
    rw [fee_Q_offset h.ne',at_rank _ (i+2) (show rank (↑(i+2:ℕ):ℤ) (rankLevel 2 WΦ i) from (by push_cast; exact rankMod _ _)), rankLevel,along_mask, if_pos (by omega),along_read ]
    unfold actionW Sourced ray; rw [map_add, tree_ghost x, add_zero, tree_ink x (expGerm G n),he, ink_smul _ fiscal_smooth.contDiffAt, Pi.smul_apply ]; rw [Radial.layers,if_neg h.ne']; push_cast; simp only [neg_smul,one_smul, add_zero, mul_neg]; rw [local_jet fiscal fiscal_smooth.contDiffAt]
local infixl:70 " ★ " => Actors.core (PermV P)
lemma value_product {F H : T (Raw V ℂ)} (hF:Γ F P) (hH:Γ H P)(i:ℕ):
    ξ ((F ★ H) i)=∑ j∈ antidiagonal i, ξ (F j.1)*ξ (H j.2):= by
    change ξ (∑ j∈ antidiagonal i, product P (F j.1) (H j.2))=_; rw [map_sum]; exact Finset.sum_congr rfl fun j _=>value_pair _ (tied x) (hF j.1 (Set.mem_univ _)) (hH j.2 (Set.mem_univ _))
lemma value_weight (i:ℕ): ξ ((exp0 P (bareH G n)) i)=(expsum (layers fiscal) i i x:ℂ):= by
   let W(m:ℕ):= (PermV P).power (bareH G n) m
   have he k j: ξ (W k j)=((Zone.TaylorPow (layers fiscal) k j x:ℝ):ℂ):=by
       induction k generalizing j with
       | zero=> change ξ (useN.refineV (coin 1) j)=_; unfold SplitP.refineV; split; rename_i hj; change j=0 at hj; subst j; simp [at_zero,Zone.TaylorPow]; rename_i hj; rw [map_zero]; simp [Zone.TaylorPow, show j≠0 from hj]
       | succ k ih=>
          change ξ ((bareH G n ★ W k) j)= _; rw [value_product x grant (fee_power grant _), Zone.TaylorPow, Zone.mul]; push_cast; refine Eq.trans ?_ (Finset.Nat.sum_antidiagonal_swap (f:=fun t=> ((Zone.TaylorPow (layers fiscal) k t.1 x:ℝ):ℂ)*(layers fiscal t.2 x:ℂ)) (n:=j)); refine Finset.sum_congr rfl fun t ht=> ?_; rw [value_action, show ξ ((PermV P).power _ k t.2)=_ from ih t.2]; exact mul_comm ..
   change ξ ((∑ j∈Finset.range (i+1),(PermV P).wages (bareH G n) j) i) = _; rw [ Finset.sum_apply,map_sum,expsum,Complex.ofReal_sum ]; refine Finset.sum_congr rfl fun j _=>?_ ; change ξ (Actors.phase j • (W j i))= _; rw [map_smul,he,smul_eq_mul]; unfold Actors.phase; push_cast; rfl

-- Tree map of insertions. No curvature normalization on Jacobian log.
variable (O : Wilson.Config G n→ℝ)
abbrev treeChart : Dir G n→ ℝ := (charted O) ∘ (insertCo G n).toContinuousLinearMap
lemma chart_link : treeChart O= (Orb.restrictedO O) ∘ PertExtension.Chart.expLinks G _:= by
    funext i; apply congr_arg O; change array (genJet i)=liftLinks _; unfold array; apply congr_arg liftLinks; funext j; unfold genJet splitLink Function.comp; split_ifs<;> first| rfl| (solve|simp_all [PertExtension.Chart.expLinks])
private lemma smooth_chart (h:germ (charted O)): germ (treeChart O):=ContDiffAt.comp _ (by rw [map_zero]; exact h) (Tζ).contDiff.contDiffAt

lemma cuts_cost (F:Dir G n) : logHaar (insertCo G n F) = ∑ i:Cotree n, Maurer.lac (F i):= by
    let g i:= Maurer.lac (insertCo G n F i); unfold logHaar; rw [ show ∑ i:Cotree n, Maurer.lac (F i)=∑ i:Cotree n, g i.val from ?_]; swap; · unfold g; simp_rw [co_at]
    change ∑ i:OEdge n, g i=_
    rw [ ← Fintype.sum_subtype_add_sum_subtype Branch g, show ∑ i:Trees n,g i.val=0 from ?_, zero_add ]; apply Finset.sum_eq_zero; intro i _; unfold g; rw [co_off F i,Maurer.lac,LocalH.spin_zero,Real.log_one]

private lemma fee_Q {J:Precision.ChartRatio G}(h:Precision.LocalRatio J): ∀ᶠ i:G.Color in 𝓝 0, PertExtension.Chart.fee J i= J.scale * Real.exp ( Maurer.lac i):= by
    filter_upwards [Maurer.lives G, Maurer.real_ratio h] with i hi hq
    unfold Maurer.lac PertExtension.Chart.fee; rw [hq, max_eq_left (mul_nonneg h.scale.le hi.le), Real.exp_log hi]
def cJac (G:Gauge)(n:Side):ℝ:= (tray G).scale ^ Fintype.card (Cotree n)
lemma cJac_pos : 0<cJac G n:=pow_pos (traySpec G).scale _
lemma orig_density : PertExtension.Chart.jacobian (tray G) (U:=Cotree n) =ᶠ[𝓝 0] fun F => cJac G n*Real.exp (logHaar (insertCo G n F)) := by
    filter_upwards [Filter.eventually_all.mpr (fun i:Cotree n=> (continuous_apply i|>.tendsto (0:Dir G n)).eventually (fee_Q (traySpec G)))] with F h
    rw [cuts_cost,Real.exp_sum]; unfold PertExtension.Chart.jacobian; simp_rw [h,Finset.prod_mul_distrib]; simp [cJac]
private lemma charge_jet (h:germ (charted O)) (i:ℕ) : -- use normalized account germ
    Radial.jet ((fun x=> Real.exp (logHaar x)*(charted O x)) ∘ Tζ) i x= (cJac G n)⁻¹*jet (accountingWith (tray G) (restrictedO O)) i x:= by
    let K:= accountingWith (tray G) (restrictedO O)
    let F(A:E G n):= Real.exp (logHaar A)*charted O A
    have hv : F∘ Tζ =ᶠ[𝓝 0] ((cJac G n)⁻¹) • K := by
        filter_upwards [orig_density (G:=G) (n:=n)] with i h
        change Real.exp _ * treeChart O i= (cJac G n)⁻¹* (PertExtension.Chart.jacobian _ _ * _)
        rw [chart_link,h]; unfold Function.comp; field_simp [cJac_pos.ne']; exact mul_comm .. 
    have hk : germ K:= by
        change germ (PertExtension.Chart.jacobian (U:=Cotree n) (tray G) * (restrictedO O ∘ PertExtension.Chart.expLinks _ _)); rw [← chart_link]; exact (PertExtension.Chart.Ratio.jacobian_smooth (traySpec G)).mul (smooth_chart O h)
    unfold jet; change _ * iteratedFDeriv ℝ i (F ∘ Tζ) 0 _= _; rw [(hv.iteratedFDeriv ℝ i).eq_of_nhds, iteratedFDeriv_const_smul_apply (hk.of_le le_top) ]; unfold K; simp only [_root_.smul_apply, smul_eq_mul]; ring
lemma factors : exp0 P Q= (exp0 P (bareH G n)) ★ rankLevel 0 (ink (γ).e0 (Real.exp ∘ logHaar)):= by
    rw [split_Q,← ranked_exp (γ).never haarSmooth Haar_null]; exact cheer_a («P»:=useN) ( «M»:=actor P ) begins (FreeBV.even_level master.evenH) clean_in clean_log
-- density for inserted, includes also insertion Q=1 (not dropping normalization)
local notation "tO"=> rankLevel 0 (Position.insertion O)
def numeratorRows (O:Wilson.Config G n→ℝ): T (Raw V ℂ):= (exp0 (Position.Parity G n) (FreeBV.interaction (actionW G n) (haarW G n))) ★ rankLevel 0 (Position.insertion O)
-- notation p due to hygiene
lemma multiplied (F H:Raw V ℂ): rankLevel 0 (product P F H) = rankLevel 0 F ★ rankLevel 0 H:= Eq.symm (funext fun i=> pairLevel i (h:=0) (g:=0) (hF:=fun _ hx=>by omega) (hH:=fun _ hx=>by omega))
lemma totalRevenue (h:germ (charted O))(i:ℕ): ξ (numeratorRows O i)= (( (cJac G n)⁻¹*integrandSeries fiscal (accountingWith (tray G) (restrictedO O)) i x:ℝ) : ℂ) := by
    let a := exp0 P (bareH G n)
    let f := (Real.exp ∘ logHaar) * (charted O)
    have he : germ (Real.exp ∘ (logHaar (G:=G) (n:=n))):= Real.contDiff_exp.contDiffAt.comp _ haarSmooth
    have hf:germ f:= he.mul h
    rw [numeratorRows,factors,(PermV P).star_a,← multiplied, ← show ink (γ).e0 f= product P (ink (γ).e0 (Real.exp∘logHaar)) (Position.insertion O) from ink_mul (γ).e0 (γ).never he h, value_product x (expΓ (p:=P) grant) (FreeBV.basis_level (ink_s _ (γ).never hf)) ]; unfold integrandSeries Zone.mul; push_cast; rw [Finset.mul_sum ]; refine Eq.trans ?_ (Finset.Nat.sum_antidiagonal_swap (f:=fun t=> ((cJac G n:ℝ):ℂ)⁻¹*((jet (accountingWith (tray G) (restrictedO O)) t.1 x:ℂ)*(expsum (layers fiscal) t.2 t.2 x:ℂ))) (n:=i)); refine Finset.sum_congr rfl fun j hj=> ?_; rw [value_weight,rankLevel, add_zero, tree_read x f hf, show jet (f ∘ Tζ) j.2 x= _ from charge_jet x O h j.2 ]; push_cast; rcases j; simp only [Prod.swap]; ring

end YM.WilsonBridge.Based.Position
