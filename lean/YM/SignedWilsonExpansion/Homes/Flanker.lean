import YM.SignedWilsonExpansion.Homes.Quotes

/-! Coordinates of a full-tail lift projected into any leading frame. Use full-cap
positive Gram with true reflected partner (conjugate included). -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.SignedWilsonExpansion.Homes
open Function Filter Set MeasureTheory Extraction Climb Spec Table Next.UVStress OPE.Levy Trace.Pilot PhysMS PhysMS.Frame
open MergeProof.East Next.Rank Ward Next.Rank.East OPE
open YM.Push.FiniteDetection.Free
open scoped Topology BigOperators Classical ContDiff
variable {n:ℕ} {ι : Type*}
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book}

variable (d:ℕ) (P:Panel S) (J:tower S)
local notation "B" => (Bel C.book).Field d
def facN (P:Panel S)(J:tower S)(d:ℕ) : (Bel C.book).Field d →ₗ[ℂ] (Bel C.book).Field d:= (J d).symm.toLinearMap.comp (P d)
@[simp] theorem fac_value (v:B) : J d (facN P J d v) = P d v := LinearEquiv.apply_symm_apply ..

lemma fac_reflect {F:Final C f S} {H:(Bel C.book).Hierarchy}
   (hg:Spin.realH F.room.kernel.spin (Maxwell.Free.spin_free C.labels) (J d)) (hP:StraightAt F.room.kernel.spin H.spin P d) (v:B):
   facN P J d (reflect (C:=C) d v) = reflect (C:=C) d (facN P J d v) := by
   apply (J d).injective; rw [ flip_coupled F d (fun _=>J) 1 hg, fac_value,fac_value ]; unfold Levy.reflect; rw [hP.reflects, hP.bars]

lemma mate {F:Final C f S} (r:ℝ) (v w:B):
   measured F none J (d:=fun _:Fin 2=>d) ![facN P J d v, facN P J d w] r = Coast P r (d:=fun _:Fin 2=>d) ![v,w] := by
   funext t; apply DFunLike.congr_arg (S.classMoment S _ _); ext1 i; fin_cases i <;> exact fac_value ..

lemma twin_scale (c:ℂ) {F:Final C f S} (r:ℝ) (u v:B) (x:Points 2):
   measured F none J (d:=fun _:Fin 2=>d) ![ c • u,c • v ] r x = c^2 * measured F none J (d:=fun _:Fin 2=>d) ![u,v] r x := by
   unfold measured
   rw [show (fun i => J _ (![ c • u,c • v ] i)) = fun i => c • (J d (![u,v] (i:Fin 2))) from funext fun i => (J d).congr_arg (show (![ c • u,c • v ] i)= c • (![u,v] i) by fin_cases i <;> rfl)|>.trans (map_smul ..)]
   rw [MultilinearMap.map_smul_univ]; simp

section budget
variable {L:Filter ι} {r:ι→ℝ} {D:ι→ℕ}{F:Final C f S}{H:(Bel C.book).Hierarchy}{P:ι→Panel S}{J:ℝ→tower S} (hJ:Leading F J)(hr:Tendsto r L trail)(hd:Tendsto D L atTop) (hs: ∀ᶠ i in L, HouseT F.room.kernel H (r i) (D i) (P i))
include hJ hr hd hs

lemma bounded_costT (v:B) : ∃ ε:ℝ, ∀ᶠ i in L, ‖facN (P i) (J (r i)) d v‖ ≤ ε := by
   apply bound_of_ceiling; intro U hu p
   let L' := (U:Filter ι)
   let z(i):=facN (P i) (J (r i)) d
   let A(i):=(‖z i v‖)⁻¹
   have hp:= p.eventually_gt_atTop 0
   let X(i):= (A i:ℂ) • (z i v)
   have he : ∀ᶠ i in L',X i∈ Metric.sphere (0:B) 1 := by
      filter_upwards [hp] with i hi
      unfold X; rw [Metric.mem_sphere,dist_zero_right,norm_smul,Complex.norm_real,Real.norm_of_nonneg]; exact inv_mul_cancel₀ (show 0<‖z i v‖ from hi).ne'
      exact inv_nonneg.mpr hi.le
   obtain ⟨y,hy,T⟩:= appointment (U:=U) (isCompact_sphere ..) he
   have hN:y≠0:=by rintro rfl; simp at hy
   let v':= reflect (C:=C) d v; let Y(i):=(A i:ℂ) • (z i v'); let y':= reflect (C:=C) d y
   have Q:Tendsto Y L' (𝓝 y'):= by
       apply Tendsto.congr' _ (Levy.reflect_limit (C:=C) d T)
       filter_upwards [(hr.mono_left hu).eventually (hJ.equivariant d),(hd.mono_left hu).eventually_ge_atTop d,hs.filter_mono hu] with i hi hf H'
       unfold Function.comp X Y z v'
       rw [fac_reflect (F:=F) (H:=H) d _ _ hi (H'.ticket (⟨d,Nat.lt_succ_of_le hf⟩: Fin (D i+1))|>.1), Levy.reflect, LinearMap.map_smulₛₗ, Complex.conj_ofReal,map_smul]
   have hT: Tendsto (fun i=> (A i:ℂ)) L' (𝓝 0):= by simpa only [Complex.ofReal_zero] using! (Complex.continuous_ofReal.tendsto _).comp (tendsto_inv_atTop_zero.comp p)
   let W:= WickGoal (C:=C) (d:=fun _:Fin 2=>d) ![ y,y' ]
   have weak(t:Test 2) : t.applyTo W=0 := by
      have hc := chargeV hJ (hr.mono_left hu) (d:=fun _:Fin 2=>d) (U:=fun i=>![ X i,Y i]) (v:=![y,y']) (fun j=>by fin_cases j; exact T; exact Q) t
      have hx: Tendsto (fun i=> (A i:ℂ)^2 * t.applyTo (Coast (P i) (r i) (d:=fun _:Fin 2=>d) ![v,v'])) L' (𝓝 0) := by
         simpa only [zero_pow (by omega : 2≠0), zero_mul] using
           (hT.pow 2).mul ((lateX hd hs _ (show MaxwellSlots C (fun _:Fin 2=>d) from ![v,v']) t).mono_left hu)
      apply tendsto_nhds_unique hc (hx.congr ?_); intro i
      change (A i:ℂ)^2 * t.applyTo (Coast _ _ (d:=fun _:Fin 2=>d) _)=t.applyTo (measured F none _ (d:=fun _:Fin 2=>d) _ _)
      have hv: measured F none (J (r i)) (d:=fun _:Fin 2=>d) ![ X i,Y i ] (r i)=fun x=> (A i:ℂ)^2 * Coast (P i) (r i) (d:=fun _:Fin 2=>d) ![v,v'] x:= by
         dsimp only [X,Y,z]
         exact funext fun x=> (twin_scale (F:=F) (J:=J (r i)) d _ _ _ _ x).trans (congr_arg ((_ : ℂ) * ·) (congrFun (mate d (P i) _ (F:=F) (r i) v v') x))
      rw [hv]
      unfold Test.applyTo; simp_rw [mul_left_comm (t _)]; rw [integral_const_mul]
   have hx : free2 d (C:=C) y y' = 0 := Test.weak_null (WickC _) |>.1 weak detectors_in
   exact (ne_of_gt (free_positive d y hN)).symm (congr_arg Complex.re hx.symm)
end budget
end YM.SignedWilsonExpansion.Homes
