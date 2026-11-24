import YM.SignedWilsonExpansion.Homes.Egg

/-! Partners, mix two or more radii. Do not assume a sign from a one-home
measurement. Outer reference frame used to price these **bounded-ratio** homes. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.SignedWilsonExpansion.Homes
open Function Filter Set MeasureTheory Extraction Climb Spec Table Next.UVStress OPE.Levy Trace.Pilot PhysMS PhysMS.Frame
open MergeProof.East Next.Rank Ward Next.Rank.East Pert.Scale Maxwell Extra.FD
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book} {n:ℕ} {d:Caps n} {ι:Type*} {L:Filter ι}

abbrev serving {T:Type*} {A:Type*} [TopologicalSpace A] (U:Ultrafilter T) (v:T→A):= ∃ x, Tendsto v (U:Filter _) (𝓝 x)
lemma columnY {X Y:Type*}[NormedAddCommGroup X][NormedAddCommGroup Y][NormedSpace ℂ X][NormedSpace ℂ Y][FiniteDimensional ℂ X]
    {U:Ultrafilter ι}{G:ι→X→ₗ[ℂ] Y}(h:∀ x,serving U (fun i=>G i x)){v:ι→X}(hp:serving U v): serving U (fun i=> G i (v i)) := by
   let B:=Module.finBasis ℂ X
   obtain ⟨x,T⟩:=hp
   choose y H using fun j=> h (B j)
   refine ⟨∑ j,B.coord j x • y j,?_⟩
   have e(i): G i (v i)=∑j,B.coord j (v i) • G i (B j):= by
      simp_rw [← map_smul (G i), ← map_sum (G i)]; exact congrArg (G i) (B.sum_repr _).symm
   simp_rw [e]
   exact tendsto_finsetSum _ fun i _=> ((((B.coord i).continuous_of_finiteDimensional.tendsto _).comp T).smul (H i))
lemma chargedG {X:Type*}[NormedAddCommGroup X][ProperSpace X]{U:Ultrafilter ι}{v:ι→X}: serving U v ↔ ∃ε:ℝ,∀ᶠ i in (U:Filter ι), ‖v i‖ ≤ ε := by
   constructor; rintro ⟨x,p⟩; exact ⟨_,p.norm.eventually (ge_mem_nhds (lt_add_one _))⟩
   rintro ⟨ε,hε⟩
   obtain ⟨x,-,p⟩:= appointment (U:=U) (v:=v) (hZ:=isCompact_closedBall (0:X) ε) (by simpa only [Metric.mem_closedBall,dist_zero_right] using hε)
   exact ⟨x,p⟩
lemma ceilings {X:Type*}[NormedAddCommGroup X]{v:ι→X} (h:∀U:Ultrafilter ι,(U:Filter ι)≤L→ serving U v) : ∃ ε:ℝ,∀ᶠi in L, ‖v i‖ ≤ ε :=
   bound_of_ceiling _ (fun U hu H=>by obtain ⟨x,p⟩:= h U hu; obtain ⟨i,hi,hh⟩:= ((p.norm.eventually (ge_mem_nhds (lt_add_one _))).and (H.eventually_gt_atTop _)).exists; exact hi.not_gt hh)
lemma double_trail {r:ι→ℝ} (hr:Tendsto r L trail): Tendsto (fun i=>2*r i) L trail := by refine tendsto_nhdsWithin_iff.mpr ⟨?_,(hr.eventually self_mem_nhdsWithin).mono fun _ hi=> mul_pos two_pos hi⟩; simpa only [mul_zero] using (hr.mono_right nhdsWithin_le_nhds).const_mul (2:ℝ)
lemma comparableT {r ρ:ι→ℝ} (h:Tendsto r L trail)(hr:pivotT L r ρ): ∀ᶠ i in L, ρ i/(2*r i)∈ Icc (2:ℝ)⁻¹ 1:= by
   filter_upwards [hr,h.eventually self_mem_nhdsWithin] with i hi hp
   have ht:= mul_pos (by norm_num:0<(2:ℝ)) (show 0<r i from hp)
   exact ⟨(le_div_iff₀ ht).2 (by linarith [hi.1]), (div_le_one ht).2 hi.2⟩

section home
-- named condition allows using Panel Eq only later
lemma rentOuter {r ρ:ι→ℝ}{F:Final C f S}{J:ℝ→tower S}(H':Leading F J) {H:(Bel C.book).Hierarchy}{D:ι→ℕ}{P:ι→Panel S} (h:Tendsto r L trail)(hr:pivotT L r ρ)(hd:Tendsto D L atTop) (hs: ∀ᶠ i in L, HouseT F.room.kernel H (ρ i) (D i) (P i))
   (d:ℕ)(U:Ultrafilter ι)(hu:(U:Filter ι)≤ L) (v:ι→(Bel C.book).Field d) (hv:serving U v) :
   serving U (fun i=> facN (P i) (J (2*r i)) d (gear C.labels d (r i/ρ i) (v i))) := by
   let t(i):= ρ i/(2*r i)
   let s (i):=r i/ρ i
   let X(i):= gear C.labels d (s i) (v i)
   let y(i):= facN (P i) (J (ρ i)) d (X i)
   obtain ⟨p,hP⟩:= compare_pivot h hr
   obtain ⟨z,-,T⟩:= appointment (U:=U) (v:=s) isCompact_Icc ((hP.filter_mono hu).mono fun i hi=> hi.1)
   have hT:= comparableT h hr
   obtain ⟨z',-,τ⟩:= appointment (U:=U) (v:=t) isCompact_Icc (hT.filter_mono hu)
   obtain ⟨v0,hv0⟩:=hv
   obtain ⟨B,hB⟩:= chargedG (U:=U) (v:=y)|>.mp (columnY (U:=U) (G:=fun i=> facN (P i) (J (ρ i)) d) (fun x=> by
       obtain ⟨ε,hε⟩:= bounded_costT d H' p hd hs x; exact chargedG.mpr ⟨ε,hε.filter_mono hu⟩) (show serving U X from ⟨_,gearHome d T hv0⟩))
   obtain ⟨Ψ,ψ,c⟩:= PhysMS.Frame.comparison F d J H'
   let o(i) := if h:0<t i then cocycle d J (2*r i) (t i) h (y i) else 0
   have hσ: 0<(2:ℝ)⁻¹:=by norm_num
   obtain ⟨Y,T⟩:= (chargedG (v:=o) (U:=U)).2 (show ∃ε:ℝ,∀ᶠ i in (U:Filter ι), ‖o i‖ ≤ ε from ⟨Ψ*B,by
      filter_upwards [hB,hT.filter_mono hu, ((double_trail h).mono_left hu).eventually (c _ hσ)] with i he hx hk
      unfold o; rw [dif_pos (hσ.trans_le hx.1)]; exact ((hk _ hx).1 (y i)).trans (mul_le_mul_of_nonneg_left he (zero_le_one.trans ψ))⟩)
   refine ⟨_,(gearHome _ τ T).congr' ?_⟩
   filter_upwards [hT.filter_mono hu,(h.mono_left hu).eventually self_mem_nhdsWithin] with i hi hp
   let v:=hσ.trans_le (show (2:ℝ)⁻¹ ≤ t i from hi.1)
   unfold o; rw [dif_pos v]
   apply (J (2*r i) d).injective
   rw [cocycle_value, show t i*(2*r i)=ρ i from div_mul_cancel₀ _ (mul_pos two_pos (show 0<r i from hp)).ne', fac_value,fac_value ]
def shelter (r:ℝ) (ρ:Fin n→ℝ) (P:Fin n→Panel S)(v:MaxwellSlots C d)(x:Points n):ℂ:=
   S.classMoment S d (r • x) (fun i=> P i (d i) (gear C.labels (d i) (r/ρ i) (v i)))
lemma mixed {F:Final C f S}{J:ℝ→tower S}(H':Leading F J) {H:(Bel C.book).Hierarchy}{r:ι→ℝ}
   {ρ:ι→Fin n→ ℝ} {D:ι→Fin n→ ℕ}{P:ι→Fin n→Panel S} (h:Tendsto r L trail)(hr:∀ j,pivotT L r (fun i=>ρ i j))(hd:∀ j,Tendsto (fun i=>D i j) L atTop) (hs: ∀ᶠ i in L, ∀ j, HouseT F.room.kernel H (ρ i j) (D i j) (P i j))
    {x:ι→Points n}{K:Set (Points n)}(hK:IsCompact K)(hk:K⊆conf n)(X:∀ᶠ i in L, x i∈ K)(d:Caps n){w:ι→MaxwellSlots C d}{v:MaxwellSlots C d} (hv:∀ j,Tendsto (fun i=>w i j) L (𝓝 (v j))):
   ∃ ε:ℝ,∀ᶠ i in L, ‖shelter (r i) (ρ i) (P i) (w i) (x i)‖ ≤ ε := by
   refine ceilings fun U hu=>?_
   let z(i)(j:Fin n):= facN (P i j) (J (2*r i)) (d j) (gear C.labels (d j) (r i/ρ i j) (w i j))
   choose y T using fun j:Fin n=> rentOuter H' h (hr j) (hd j) (hs.mono fun _ hi=>hi j) (d j) U hu (fun i=>w i j) ⟨v j,(hv j).mono_left hu⟩
   obtain ⟨q,H,p⟩:= appointment (U:=U) hK (X.filter_mono hu)
   have θ:= Work.A05.smul_conf (inv_pos.mpr two_pos) (hk H)
   obtain ⟨V,hV,hI,hv⟩:= exists_compact_subset (conf_open _) θ
   let w' i:= (2:ℝ)⁻¹ • x i
   have W:= landArea (x:=w') (mem_interior_iff_mem_nhds.mp hI) ((coordU _ _).mpr (higher H' ((double_trail h).mono_left hu) 0 (d:=d) (U:=z) (v:=y) T hV hv)) ((tendsto_const_nhds (x:=(2:ℝ)⁻¹)).smul p) ((WickGoal_tied y θ).continuousAt)
   refine ⟨_,W.congr ?_⟩
   intro i
   unfold measured shelter
   simp_rw [z,w',fac_value]; rw [smul_smul,mul_comm 2, mul_assoc, mul_inv_cancel₀ two_pos.ne',mul_one]; rfl
end home
end YM.SignedWilsonExpansion.Homes
