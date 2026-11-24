import YM.Trace.Physicalv2.Germ
import YM.Planned.ATOM_REGULAR_ESTIMATE.Pin
import YM.Next.FLUCTUATIONS.Charts
import YM.Next.WARD_BIN.Lies
import YM.Work.G05.Taylor

/-! A local part of error extraction: gain coupling/threshold powers on the
actual health set by killing every left-link Taylor tensor THROUGH an indicated
ordinary order. No smoothness of the masks is to be inferred from this. First
bring the field up to gauge and restrict directions to the true local stencil.
Need genuine smooth *unmasked* bounds (analytic price for loop packets below),
not just a formal identity on small momentum tests. Constants in the local
Taylor estimate only worsen by powers of the halo radius; side and probe
geometries of course still have to meet these health conditions. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Trace.Physical.LogAccuracy
open WardBin.Lies Metric Set Function Lattice Wilson RG Source MeasureTheory Filter
open scoped Matrix.Norms.Frobenius Topology ContDiff BigOperators Classical
variable {G:Gauge}{n:Side}{F : Config G n→ℂ}{m r:ℕ}
local notation "D" => Directions G n
abbrev small_horizon (t:Site n→G.El) (A:D) : D := fun i=> G.adjoint (t i.1) (A i)
lemma incremental (t:Site n→G.El) (A:D) (V:Config G n) (k:ℝ) : gauge t (increment V (k • A)) = increment (gauge t V) (k • small_horizon t A) := by
   ext i
   unfold increment Lattice.gauge small_horizon; simp only [Pi.smul_apply,← LinearMap.map_smul, ProjectorNext.Equivariance.exp_adjoint]; group
lemma dashed (t:Site n→G.El) (h: GaugeInvariant F) (l:List D) (V:Config G n) : leftDerivs F l V = leftDerivs F (l.map (small_horizon t)) (gauge t V) := by
    induction l generalizing V with
    | nil=> exact (h ..).symm
    | cons l i ih=> simp only [leftDerivs,List.map_cons]; congr; funext k; rw [ih,incremental]
def slim (X:Support n) (A:D):D:=fun i=> if i.1∈X then A i else 0
lemma slim_agrees (X:Support n) (A:D):Agrees X A (slim X A) := fun i hi _=> (if_pos (show i.1∈X from hi)).symm
lemma directed_agrees (X:Support n) (h:LocalOn X F) (l:List D){V U:Config G n}(he:Agrees X V U) : leftDerivs F l V = leftDerivs F (l.map (slim X)) U:=by
    induction l generalizing V U with
    | nil=> exact h _ _ he
    | cons l i ih=>
      simp only [leftDerivs,List.map_cons]; apply congr_arg (fun z=> deriv (z:ℝ→ℂ) 0); funext k; apply ih
      intro a ha hb; unfold increment; rw [Pi.smul_apply,Pi.smul_apply,slim_agrees X l a ha hb,he a ha hb]

def Flat (F:Config G n→ℂ)(r:ℕ):Prop:= ∀ k<r,iteratedFDeriv ℝ k (F∘increment 1) 0=0

theorem tapered_jet (r:ℕ)(h:Flat F r) (hd: Push.Local.Chart r F 1) (l:List D)(he:l.length<r): leftDerivs F l 1 = 0:=by
    let k:=l.length; let J : Fin k→D:=l.get
    rw [← show List.ofFn J=l from List.ofFn_get l]
    have h': WardBin.Lies.Germ k F 1:= hd.of_le (Nat.cast_le.mpr he.le)
    rw [Germ.ordered J h']
    let f:=journey (1:Config G n) k J
    have H (j:ℕ)(U:Panels k → Config G n)(z:Panels k→ Slab G n j)(hU:∀ i,ContDiff ℝ ω fun t=>G.mat (U t i))(hz:ContDiff ℝ ω z) (i:Edge (Site n)): ContDiff ℝ ω (fun t=>G.mat (chug j (U t) (z t) i)):= by
      induction j generalizing U i with
      | zero=> exact hU _
      | succ j ih=> refine ih (fun t=>increment (U t) (z t 0)) (fun t=>Fin.tail (z t)) (fun i=>?_) (contDiff_pi.mpr (fun i=>contDiff_pi.mp hz _)) _; change ContDiff ℝ ω (fun t=>G.mat (G.lieExp ((z t) 0 i)*(U t i))); simp_rw [G.mat_mul]; exact (G.exp_jet.comp (contDiff_pi.mp (contDiff_pi.mp hz _) _)).mul (hU _)
    obtain ⟨Z,hz,hAt,hEq⟩:= Push.Local.lift_germ f 0 (fun i=> (H k _ (photon k J) (fun _=>contDiff_const) (photon k J).contDiff i).contDiffAt)
    have hf : f (0:Panels k) = chug k 1 0:= by unfold f journey; congr; funext i; simp
    rw [hf,chug_zero] at hEq
    have empty (i)(hi:i≤r-1) :iteratedFDeriv ℝ i (F∘increment 1) (0:D)=iteratedFDeriv ℝ i (0:D→ℂ) 0:=by rw [h i (by omega),iteratedFDeriv_zero];rfl
    have hjet := Work.G05.jets_comp (d:=r-1) (f:=Z) (f':=Z) (x:=0) (hz.of_le le_top) (hz.of_le le_top) (g:=F∘increment 1) (by rw [hAt]; exact hd.of_le (Nat.cast_le.mpr (Nat.sub_le _ _))) (g':=(0:D→ℂ)) contDiff_const.contDiffAt rfl (fun _ _=>rfl) (by rw [hAt];exact empty) k (by omega)
    have eq : F∘journey 1 k J=ᶠ[𝓝 0](F∘increment 1)∘ Z:=hEq.fun_comp F
    rw [(eq.iteratedFDeriv (𝕜:=ℝ) k).eq_of_nhds,hjet, show (0:D→ℂ) ∘ Z=(0:Panels k→ℂ) from rfl,iteratedFDeriv_zero]; exact rfl

lemma scalar_mvt {e:ℕ}{V:ℝ→ℂ}{C:ℝ} (he:e>0)(hc:C≥0)(h0:iteratedDeriv (e-1) V 0 = 0)(hs:∀ u∈Icc (0:ℝ) 1,DifferentiableAt ℝ (iteratedDeriv (e-1) V) u)(hf:∀ u∈Icc (0:ℝ) 1, ‖iteratedDeriv e V u‖ ≤ C) : ∀ u∈Icc (0:ℝ) 1,‖iteratedDeriv (e-1) V u‖ ≤ C := by
    intro u hu
    have bound (x:ℝ)(hx:x∈ Icc (0:ℝ) 1): ‖deriv (iteratedDeriv (e-1) V) x‖ ≤ C:=by rw [←iteratedDeriv_succ (n:=e-1),show e-1+1=e by omega]; exact hf x hx
    have H := Convex.norm_image_sub_le_of_norm_deriv_le hs bound (convex_Icc _ _) (s:=Icc (0:ℝ) 1) (y:=u) (x:=0) (Set.left_mem_Icc.mpr zero_le_one) hu
    rw [h0,sub_zero,sub_zero,Real.norm_of_nonneg (Set.mem_Icc.mp hu).1] at H
    exact H.trans (mul_le_of_le_one_right hc (Set.mem_Icc.mp hu).2)

def OnLinks(F:Config G n→ℂ)(m:ℕ)(C δ:ℝ):Prop:= ∀{v:D}, ‖v‖≤ δ → let V:=increment (1:Config G n) v;Push.Local.Chart m F V ∧ ∀ l:List D,l.length≤m→ (∀ i∈l,‖i‖≤1) → ‖leftDerivs F l V‖≤C

-- scalar line with repeatedly prepended parameter A followed by a fixed list
private lemma scale_paid {C δ τ:ℝ}(hC: C≥0)(hτ:τ>0)(hg:OnLinks F m C δ) {t:ℝ}(ht:t∈ Icc (0:ℝ) 1){A:D}(hA:‖A‖≤τ)(hδ:τ≤δ)(l:List D)(hm:l.length≤m)(hl:∀ i∈l,‖i‖≤ τ): ‖leftDerivs F l (increment 1 (t • A))‖≤ τ^l.length * C:=by
     obtain ⟨hV,hg'⟩:=hg (v:=t • A) ((norm_smul_of_nonneg (Set.mem_Icc.mp ht).1 _).trans_le ((mul_le_mul (Set.mem_Icc.mp ht).2 hA (norm_nonneg _) zero_le_one).trans (by simpa using hδ)))
     let p:=l.map (fun i=>τ⁻¹ • i)
     have hL:l = p.map (fun i=>τ • i):=(show l.map (fun i=>τ • (τ⁻¹ • i))=l from by simp_rw [smul_smul,mul_inv_cancel₀ hτ.ne',one_smul];simp).symm.trans (List.map_map ..).symm
     have hh:p.length=l.length:=List.length_map _
     conv_lhs => rw [hL,Push.Local.left_homogeneous (k:=m) _ hV (hh.trans_le hm)]
     rw [hh,norm_smul_of_nonneg (pow_nonneg hτ.le _)]
     refine mul_le_mul_of_nonneg_left (hg' p (hh.trans_le hm) ?_) (by positivity)
     intro i hi; obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hi
     rw [norm_smul_of_nonneg (inv_nonneg.mpr hτ.le)]; exact (mul_le_mul_of_nonneg_left (hl j hj) (inv_nonneg.mpr hτ.le)).trans_eq (inv_mul_cancel₀ hτ.ne')


private lemma radial_wage {C τ:ℝ}(hC:C≥0)(hpos:0<τ)(hle:τ≤1)(hr:r≤m)(hF:Flat F r)(hg:OnLinks F m C τ) {u:ℝ}(hu:u∈ Icc (0:ℝ) 1){A:D}(hA:‖A‖≤τ)(l:List D)(hm:l.length≤m)(hl:∀ i∈l, ‖i‖≤τ) :
    ‖leftDerivs F l (increment 1 (u • A))‖≤τ^r*C:=by
     by_cases he:r≤l.length
     · exact (scale_paid hC hpos hg hu hA le_rfl _ hm hl).trans (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hpos.le hle he) hC)
     let T : ℝ→ℂ:=fun u=>leftDerivs F l (increment 1 (u • A))
     have hEq k x : iteratedDeriv k T x = _ := (Next.Foundations.leftDerivs_diag (1:Config G n) A (leftDerivs F l) k x).symm.trans (congr_fun (Work.G07.left_append F _ _).symm (increment 1 (x • A)))
     have hV {x:ℝ}(hx:x∈Icc (0:ℝ) 1): Push.Local.Chart m F (increment (1:Config G n) (x • A)) := (hg (v:=x • A) (by rw [norm_smul_of_nonneg hx.1]; simpa using mul_le_mul hx.2 hA (norm_nonneg _) (zero_le_one' ℝ))).1
     have hH:∀ i≤r-l.length,∀ x∈Icc (0:ℝ) 1, ‖iteratedDeriv i T x‖≤τ^r*C:=by
          intro i hi
          induction hi using Nat.decreasingInduction with
          | self=>
            intro x hx; rw [hEq]
            let p:=List.replicate (r-l.length) A ++ l
            have hh:p.length=r:=by simp only [p,List.length_append,List.length_replicate]; omega
            convert! (scale_paid hC hpos hg hx hA le_rfl p (hh.trans_le hr) (fun i hi=>?_)) using 2
            · rw [hh]
            rcases List.mem_append.mp hi with h|h
            · exact (List.mem_replicate.mp h).2 ▸ hA
            exact hl i h
          | of_succ j hj ih=>
            apply scalar_mvt (show j+1>0 by omega) (C:=τ^r*C) (mul_nonneg (pow_nonneg hpos.le _) hC) ?_ ?_ ih
            · rw [show j+1-1=j from rfl,hEq,zero_smul,Work.G07.at_zero_increment, tapered_jet r hF ?_ _ (by simp only [List.length_append,List.length_replicate];omega)]
              exact Work.G07.at_zero_increment (1:Config G n) ▸ ((hg (v:=(0:D)) (by rw [norm_zero]; positivity)).1.of_le (Nat.cast_le.mpr hr))
            intro x hx
            have hL: Push.Local.Chart (j+1) (leftDerivs F l) (increment (1:Config G n) (x • A)):= Next.Foundations.leftDerivs_chart l (j+1) (show Push.Local.Chart (l.length+(j+1)) F _ from (hV hx).of_le (Nat.cast_le.mpr (by omega)))
            have hT : ContDiffAt ℝ (↑(j+1:ℕ)) T x := Push.Local.chart_comp (k:=j+1) (W:=fun x:ℝ=>increment 1 (x • A)) hL (fun i=> ((G.exp_jet.comp ((contDiff_id.smul contDiff_const))).mul (g:=fun _=>G.mat 1) contDiff_const).contDiffAt)
            -- locate scalar version
            have hd₁ : DifferentiableAt ℝ (iteratedFDeriv ℝ j T) x:= hT.differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self j)
            exact (ContinuousMultilinearMap.apply ℝ _ ℂ (fun (_:Fin j)=>1)).differentiableAt.comp _ hd₁
     exact (by simpa using hH 0 (Nat.zero_le _) u hu)

private def bouquet (Q τ:ℝ)(s:ℕ) := 4*Q*τ*(1+s)
private lemma bush (U:Config G n){s:ℕ}{τ δ Q:ℝ}(hQ:Q>0)(hτ:τ≥0)(hδ : ∀ j : G.El,G.chord j≤δ → G.lieExp (G.plog (G.mat j))=j ∧ ‖G.plog (G.mat j)‖ ≤ Q*G.chord j)(o:Site n)(h:∀ i:Edge (Site n), separation o i.1 ≤ s → G.chord (U i) ≤ 4*(τ*(1+separation o i.1)))(hsmall:4*(τ*(1+s))≤δ): ∃ A:D, Agrees (halo s {o}) U (increment 1 A) ∧ ‖A‖≤ bouquet Q τ s := by
    let f:D:=fun i=> if separation o i.1 ≤s then G.plog (G.mat (U i)) else 0
    refine ⟨f, fun i hi hx=>?_,(pi_norm_le_iff_of_nonneg (by unfold bouquet; positivity)).mpr fun i=> ?_⟩
    · obtain ⟨o',ho,he⟩:=halo_spec.mp (show i.1∈halo s {o} from hi); obtain rfl:=Finset.mem_singleton.mp ho
      apply Eq.symm; change G.lieExp (f i)*(1:G.El)=_; unfold f; rw [if_pos he,mul_one]
      exact (hδ _ ((h i he).trans (le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add_right (by exact_mod_cast he : (separation o' i.1:ℝ)≤(s:ℝ)) _) hτ) (by norm_num)) hsmall))).1
    unfold f; split
    next hv=>
      have hH:G.chord (U i) ≤ 4*(τ*(1+s)):= by
          apply (h i hv).trans
          gcongr
      have hp := (hδ (U i) (hH.trans hsmall)).2
      exact hp.trans ((mul_le_mul_of_nonneg_left hH hQ.le).trans_eq (by unfold bouquet;ring))
    rw [norm_zero]; unfold bouquet; positivity

def τradius (Q τ:ℝ)(s power:ℕ):= max (bouquet Q τ s) (τ*(1+s)^power)
lemma τpos {Q τ:ℝ}(h:τ>0)(s power:ℕ) : τradius Q τ s power > 0 := lt_of_lt_of_le (by positivity) (le_max_right ..)
private lemma trim (o:Site n)(s:ℕ)(Q:ℝ)(B:BudgetPoint)(v:D)(h:B.dirBound o v)(X:Support n)(hx:X ⊆ halo s {o})(t:Site n→G.El) : ‖slim X (small_horizon t v)‖ ≤ τradius Q B.threshold s B.power := by
   apply (pi_norm_le_iff_of_nonneg ((τpos (Q:=Q) B.threshold_pos _ _).le)).mpr -- positivity error
   intro i; unfold slim; split_ifs with hv
   · obtain ⟨o',he,hH⟩:=halo_spec.mp (hx hv); obtain rfl := Finset.mem_singleton.mp he
     dsimp only [small_horizon]; rw [G.norm_adjoint]
     refine (h i).trans (le_trans ?_ (le_max_right ..))
     gcongr; exact B.threshold_pos.le; rw [separation_comm]; exact_mod_cast hH
   simp only [norm_zero]; exact (τpos B.threshold_pos _ _).le

lemma local_bound (G:Gauge) : ∃ Q δ:ℝ,0<Q ∧ 0<δ ∧ ∀ {n:Side}{X Y:Support n}{F:Config G n→ℂ} {C:ℝ}{m s r:ℕ}(B:BudgetPoint)(o:Site n), 4*(B.threshold*(1+(s:ℝ))) ≤ δ → let R:=τradius Q B.threshold s B.power; R ≤ 1 → r≤m → B.order ≤ m → 2*(s+1)<n.val → X ⊆ halo s {o} → halo (s+1) {o} ⊆ Y → LocalOn X F → GaugeInvariant F → Flat F r → OnLinks F m C R → B.supBounds o Y F (R^r*C):=by
    obtain ⟨Q,δ,hQ,hq,hδ⟩:= Next.Fluctuations.log_chart_cost G
    refine ⟨Q,δ,hQ,hq,?_⟩
    intro n X Y F C m s r B o hPrice R hle horder hB hSize hX hY hL hG h0 hM
    have hp : 0 < R:=τpos B.threshold_pos _ _
    have hV:= (hM (v:=(0:Directions G n)) (by rw [norm_zero]; exact hp.le)).2 [] (Nat.zero_le _) (by simp); have hC := (norm_nonneg _).trans hV
    refine ⟨by positivity,fun U hh l hl he=>?_⟩
    obtain ⟨t,ht⟩:= Planned.AtomRegular.Foliage.Cube.anchored o hh B.threshold_pos.le hY hSize
    obtain ⟨A,H,hr⟩:= bush (gauge t U) hQ B.threshold_pos.le hδ o ht hPrice
    rw [dashed _ hG _ _,directed_agrees _ hL _ (agrees_mono H hX)]
    refine (show ‖leftDerivs F _ (increment 1 A)‖≤_ by
       simpa only [one_smul] using! radial_wage hC hp hle horder h0 hM (Set.right_mem_Icc.mpr zero_le_one) (u:=1) (A:=A) (hr.trans (le_max_left ..)) (l.map (small_horizon t)|>.map (slim X)) (by simpa using hl.trans hB) (by simp only [List.forall_mem_map]; exact fun i hi=> trim o s Q B i (he i hi) X hX t))
end YM.Trace.Physical.LogAccuracy
