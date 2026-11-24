import YM.RG12.Kintsugi.Aspect
import YM.RG12.Kintsugi.Course
/-! # Ward slot-price stability. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 400000
noncomputable section
namespace YM.RG12.Kintsugi
open Function Filter Finset Set Analysis Spec Org Climb Table Next.UVStress UVNext.FreeStress Work.A01 Maxwell
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{L:Register G}{S:Table L}(H:S.RealSpin){C:Family G}(T:MaxwellData C)
local notation "B!"=>Bel C.book
local notation "F!"=>C.book.grid
set_option quotPrecheck false
local notation "V!"=>(B!).Field 4
local notation "h!"=>T.hT.spin
instance capline : FiniteDimensional ℂ ((V!) →L[ℂ] ℂ):= LinearMap.toContinuousLinearMap.finiteDimensional
private lemma silk_axis {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E](r:ℂ)(x:Axis→Axis→E→L[ℂ] ℂ):‖r • x‖= ‖r‖*‖x‖:= norm_smul r x
local instance: ProperSpace (Auspect (Bel C.book)):= FiniteDimensional.proper ℂ (Auspect (Bel C.book))
-- opnorm compress on ANY meters J approaching scaled canonical in free (no profiles)
lemma measured (hG:G.Simple) {c:ℝ}(hc:c≠0) (J:ℕ→(B!).Stress) (he:Tendsto J atTop (𝓝 (c • canonicalStress F!))):
   ∃ y:ℝ,0≤y ∧ ∀ᶠ k in atTop,∀ v:linespace (h!),‖v‖ ≤ y * ‖scope T (J k) v‖ :=by
   -- If not, unit envelope with this representation type and evals going to zero.
   let V:=Auspect (B!);let L:=linespace (h!)
   suffices ht:∃ y:ℝ,0≤y ∧ ∀ᶠ k in atTop,∀ (v:linespace (h!)), ‖v.val‖=1 → 1 ≤ y * ‖scope T (J k) v‖ by
      obtain ⟨y,hy,H⟩:=ht; refine ⟨y,hy,H.mono fun k hk v=>?_⟩
      by_cases he:v.val=0
      · change ‖v.val‖ ≤ _; rw [he, show ‖(0:Auspect (B!))‖=0 from @norm_zero (Auspect (B!)) _]; positivity
      let t:= ‖v.val‖;have hp:0<t:= (norm_pos_iff (a := (v.val:Auspect (B!)))).mpr he
      have hu (r:ℝ)(x:V) : r • x=(r:ℂ) • x:= by
         ext1 i; ext1 j; apply ContinuousLinearMap.ext; intro u; exact (Complex.coe_smul _ (x i j u)).symm
      have heq (r:ℂ)(x:V) : ‖r • x‖= ‖r‖*‖x‖:= silk_axis (E:=(V!)) r x
      specialize hk (t⁻¹ • v) (show ‖t⁻¹ • v.val‖=1 from by rw [hu,heq,Complex.norm_real,Real.norm_of_nonneg (inv_nonneg.mpr hp.le), ← show t=_ from rfl,inv_mul_cancel₀ hp.ne'])
      rw [show scope T (J k) (t⁻¹ • v)=t⁻¹ • scope T (J k) v from (scope T (J k)).map_smul ..,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hp.le),inv_mul_eq_div,mul_div_assoc' ,le_div_iff₀ hp,one_mul] at hk
      exact hk
   by_contra! e
   have hs (n:ℕ):∃ k:ℕ, n≤k ∧ ∃ v: linespace (h!), ‖v.val‖=1 ∧ ((sizeHint n):ℝ)*‖scope T (J k) v‖<1:=
      let E:=((e (sizeHint n) (by unfold sizeHint; positivity)).and_eventually (eventually_ge_atTop n)).exists
      (show _ by obtain ⟨k,⟨v,hz,hE⟩,hX⟩:=E;exact ⟨k,hX,v,hz,hE⟩)
   choose k hk v hv hV using hs
   let w (n:ℕ):V:= (v n).val
   have hx n : w n ∈ Metric.sphere 0 1:=by rw [Metric.mem_sphere,dist_zero_right (a:= w n)];exact hv _
   obtain ⟨x,hx,q,hq,hY⟩:=(isCompact_sphere (0:V) (1:ℝ)).tendsto_subseq hx
   let Z:=w ∘ q
   have hy(i j:Axis):Tendsto (fun k=> Z k i j) atTop (𝓝 (x i j)):= tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hY i) j
   have hA {z:ℕ→(V!)}{p}(H:Tendsto z atTop (𝓝 p))(i j:Axis): Tendsto (fun k=> Z k i j (z k)) atTop (𝓝 (x i j p)):=Dash.arcing (hy i j) H
   have hz(n:ℕ):Peal (h!) (Z n):=(v (q n)).property
   have hpe : Peal (h!) x := by
      constructor
      · intro i j; apply tendsto_nhds_unique_of_eventuallyEq (hy i j) (hy j i) (Eventually.of_forall (fun k=> (hz k).sym i j))
      · intro i j u; apply tendsto_nhds_unique_of_eventuallyEq (hA (tendsto_const_nhds (x:=_)) i j) ((hA tendsto_const_nhds i j).star) (Eventually.of_forall (fun k=> (hz k).were i j u))
      · intro s i j u
        apply tendsto_nhds_unique_of_eventuallyEq (hA (tendsto_const_nhds (x:=_)) i j) ((hA tendsto_const_nhds _ _).const_smul (eps s i*eps s j))
        exact Eventually.of_forall (fun k=>(hz k).bars s i j u)
      intro u; exact tendsto_nhds_unique_of_eventuallyEq (tendsto_finsetSum _ (fun i _=> hA (tendsto_const_nhds (x:=u)) i i)) tendsto_const_nhds (Eventually.of_forall fun k=>(hz k).track u)
   have hθ:Tendsto (k ∘ q) atTop atTop:= (tendsto_atTop_mono (f:=id) hk tendsto_id).comp hq.tendsto_atTop
   have h (i j a b:Axis):(x i j) (canonicalStress (F!) a b)=0:=by
      have h₁:= hA (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (he.comp hθ) a) b) i j
      have h₂:Tendsto (fun n=> (Z n i j) (J (k (q n)) a b)) atTop (𝓝 0):=by
         apply squeeze_zero_norm (a:= fun n=>costHint (q n)) _ (cost_clears.comp hq.tendsto_atTop)
         intro n;let r:=q n;let v':=v r; let Y:=scope T (J (k r)) v'
         have hp0(r): 0<sizeHint r:=by unfold sizeHint; positivity
         have hu:‖Y‖< costHint r:= (show ‖Y‖<1 / sizeHint r from (lt_div_iff₀ (hp0 r)).2 ((mul_comm ..).trans_lt (hV _))) |> (by simpa using ·)
         change ‖Y i j a b‖≤_
         exact (norm_le_pi_norm (Y i j a) _).trans ((norm_le_pi_norm (Y i j) _).trans ((norm_le_pi_norm (Y i) _).trans ((norm_le_pi_norm Y _).trans hu.le)))
      have hh := tendsto_nhds_unique h₁ h₂
      change (x i j) (c • _) = 0 at hh
      rw [show ∀ v, x i j (c • v)= c • x i j v from fun v=> ((x i j).restrictScalars ℝ).map_smul ..] at hh
      exact (smul_eq_zero.mp hh).resolve_left hc
   rw [arcs T hG hpe h,Metric.mem_sphere,dist_self] at hx; exact zero_ne_one hx

variable {S':Table C.book}{f:Extraction.Order}(U:Final C f S')(X:Scaling S')
local notation "H'"=>U.room.kernel.spin
local notation "J'"=>reCenter S' U.sector.energy
abbrev shears (A:Auspect S')(k:ℕ): Auspect (B!):=fun i j=> (A i j).comp ((X.U k 4).toLinearMap.toContinuousLinearMap)
lemma shears_pack (k:ℕ)(h:Coherent T.hT.spin U.room.kernel.spin 4 (X.U k 4)){A:Auspect S'}(hA:Peal (H') A): Peal (h!) (shears X A k) := by
   constructor
   · intro i j; unfold shears;rw [hA.sym]
   · intro i j v; change A i j (X.U k 4 ((B!).conj _ _ v)) =_; rw [h.stars,hA.were];rfl
   · intro s i j v; change A i j (X.U k 4 ((B!).mirror _ _ s⁻¹ v)) = _; rw [h.signed,hA.bars];rfl
   intro v; exact hA.track _
lemma sectors_on (hG:G.Simple) (hJ:T.T.J=torch F! 1) {k:Extraction.Sequence}
    (hP:Tendsto (fun i=> labelScale X (k i) (J')) atTop (𝓝 (T.T.κ⁻¹ • T.T.J)))
    (ho:∀ᶠ j in atTop, Coherent (h!) (H') 4 (X.U j 4)) {A:Auspect S'}(h:Peal (H') A):
    ∃ d≥0,∀ᶠ i in atTop, ∀ a b, ‖shears X A (k i) a b‖ ≤ d*(X.r (k i))^4:=by
   rw [hJ,torch,one_smul] at hP
   obtain ⟨d,hd,hD⟩:= measured T hG (inv_ne_zero T.T.hκ) _ hP
   let Z (i j a b):ℂ:= A i j ((J') a b)
   refine ⟨d*‖Z‖,mul_nonneg hd (norm_nonneg _),?_⟩
   filter_upwards [hD,k.cofinal.eventually ho] with i hI hK a b
   let t:=k i;let v:linespace (h!):= ⟨shears X A (k i),shears_pack T U X (k i) hK h⟩;let r:= (X.r (k i))^4
   have hq:scope T (labelScale X (k i) (J')) v=r • Z := by
      funext p q c e
      change A p q (X.U (k i) 4 ((X.U _ _).symm (r • _)))=_
      rw [LinearEquiv.apply_symm_apply]
      exact ((A p q).restrictScalars ℝ).map_smul ..
   have hp:= hI v; rw [hq,norm_smul,Real.norm_of_nonneg (pow_nonneg (X.positive _).le _)] at hp
   exact ((norm_le_pi_norm (shears X A (k i) a) b).trans ((norm_le_pi_norm (shears X A (k i)) a).trans hp)).trans_eq (by ring)
end YM.RG12.Kintsugi
