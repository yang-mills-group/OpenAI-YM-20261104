import YM.SchemeConversionRG11.FirstW.Ore.Height
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function MeasureTheory Filter Set Metric Topology Lattice Pert Align Laurent Position Deck
open scoped BigOperators Classical ContDiff
variable {G:Gauge}{T:Itinerary}{F:Labels.Frames G}{c:ℕ→Side}{A B:ℕ→Field4 G}{K W:Set E4}
variable {R : ℝ}
lemma Melody.gate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℕ → Cover→ E}{b:ℤ} (h:Lives T R f) (hp:Melody T ((Metric.closedBall 0 R)\{0}: Set E4) b f): Melody T {x:E4|x≠0} b f := by
 obtain ⟨g,hp⟩:=hp
 refine ⟨fun x=> if ‖x‖≤R then g x else 0,fun σ hs v hv p H=>?_⟩
 change Tendsto _ _ (𝓝 (if ‖v‖≤R then _ else _)); split_ifs with he
 · exact hp σ hs v ⟨mem_closedBall_zero_iff.mpr he,hv⟩ p H
 apply tendsto_const_nhds.congr'
 filter_upwards [(Tendsto.norm H).eventually (lt_mem_nhds (lt_of_not_ge he)), hs.eventually h] with i hi hh
 symm; unfold ped; rw [show f (σ i) (p i)=0 from by by_contra he; exact (hh _ he).not_gt hi, smul_zero]
lemma playRoof (A:ℕ→Field4 G)(h:MarkGrid T c)(Q:Wash)(a b:Who G 6)(ha:fee a=2)(hb:fee b=2){u m:ℤ}
    (H:Credit T Q.rOut u m (fun j x=>oneMinus T j A a b x)) (e:-3 ≤ m) (K':Deaf T ((Metric.closedBall 0 Q.rOut)\{0}:Set E4) (m-u+7) A) :
    Helen (fun i=> T.gap i ^(4+(m-u)) * wheelS G T i Q (pit T a i) (pit T b i) (A i)) := by
 -- Debit f ≤ h^u step^m. scaled by h^(m-u) gives locally integrable singular ≤ m real. Lands exponent for wheel = m-u.
 let R:= Q.rOut; have hr:0<R:=Q.rOut_pos; let S:= ((Metric.closedBall (0:E4) R)\{0})
 let f := fun j x=> soft Q (Moss T j x)*oneMinus T j A a b x; let B:= ped T (m-u) f
 have hf: Lives T R f:=Eventually.of_forall (fun i x hx=> by by_contra h; exact hx (by simp only [f,soft_life Q _ (lt_of_not_ge h).le,zero_mul]))
 have hh: Melody T {x:E4| x≠0} (m-u) f:=by
    apply Melody.gate hf; have hx:S ⊆ {x:E4|x≠0}:=fun v hv=>hv.2
    have ht : Melody T S (m-u) (fun j x=> oneMinus T j A a b x) := by
       unfold oneMinus; apply Melody.sum; intro i _; apply Melody.sum; intro j _
       rw [show m-u=(-3)+(-3)+(m-u+7)-1 by omega]; exact toRoof _ _ ((lit_point _ _ ha).onSet hx) ((lit_point _ _ hb).onSet hx) K'
    simpa only [zero_add] using! ((cloud T Q S).linked ht (ContinuousLinearMap.mul ℝ ℝ))
 obtain ⟨g,Hg⟩:=hh
 have hV : Credit T R u m f := by simpa only [zero_add] using! Credit.pays (soft_credit T Q R) H (ContinuousLinearMap.mul ℝ ℝ)
 have hd:= hV.time (m-u); have he:B=fun i x=> (T.gap i^(m-u)) • f i x := rfl; rw [sub_add_cancel, ←he] at hd; obtain ⟨C,hC,hq⟩:=hd
 have hl : Lives T R B:=Eventually.mono hf (fun i hi x hx=> hi x (fun h=>hx (by simp [B,h])))
 have ht: NearCost T B:= by
    let r:ℤ:=m+3
    refine ⟨C*(R+1)^r,by positivity,?_⟩
    filter_upwards [hq,hl,T.cutoff.eventually (ge_mem_nhds (show (0:ℝ)<1 by norm_num))] with i hi hl hG v
    by_cases hz:B i v=0; · rw [hz,norm_zero,mul_zero]; positivity
    have hJ:= hl v hz; have hy:= limb hJ; have hp:=T.positive i; have hk:=zero_lt_one.trans_le (unit_stepY v); have hF:0< Foot T i v:=mul_pos hp hk
    calc
      _ ≤ Foot T i v ^3 * (C*T.gap i^m * stepY v^m):=mul_le_mul_of_nonneg_left (hi _ hJ) (by positivity)
      _ = C * Foot T i v ^ r:= by unfold r; rw [zpow_add₀ hF.ne']; unfold Foot; rw [zpow_ofNat,mul_zpow]; ring
      _ ≤ _ := by refine mul_le_mul_of_nonneg_left ?_ hC.le; exact zpow_le_zpow_left₀ (by unfold r; omega) hF.le (hy.trans (by linarith))
 have hp (x:E4)(hx:x≠0)(p:ℕ → Cover)(h : Harbor T p x): Tendsto (fun i=>B i (p i)) atTop (𝓝 (g x)):= Hg id tendsto_id x hx p h
 have hb := (mount hl h ht hp).2; refine ⟨_,hb.congr' ?_⟩; filter_upwards [pressV T A Q a b] with i hi
 rw [hi]; unfold B ped f; simp only [expenditure, smul_eq_mul,← Finset.mul_sum,zpow_add₀ (T.positive i).ne', zpow_ofNat]; ring
lemma oneM_credits (a b:Who G 6)(ha:fee a=2)(hb:fee b=2){r:ℝ} {u v:ℤ}(p:ℕ→Field4 G)(hp:Scrip T R u v p)(he:r<R): Credit T r u (v-7) (fun j x=> oneMinus T j p a b x) := by
 have hA:=wheel_live T a R; have hB:=wheel_live T b R;rw [ha] at hA;rw [hb] at hB
 unfold oneMinus; apply Credit.owed;intro i _; apply Credit.owed; intro j _; rw [show v-7=((-3)+(-3)+v-1) by omega]
 unfold pit; have H:= roof_cap (fresh i) (fresh j) hA hB hp he; simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_one,zero_add] using! H
end YM.RG11.FirstW
