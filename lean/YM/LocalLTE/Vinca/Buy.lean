import YM.LocalLTE.Dilation.Silhouette
import YM.LocalLTE.Estate.Call
import YM.LocalLTE.Georges.Mile
/-! All tilts exposed. Pay a release for expanding before. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Mallow
variable {G:Gauge} {p O:ℕ→ℝ} {a:Levels G} {W:Bid.Worth}
open YM.LocalLTE.Dilation
lemma thinner (h: Doors.Budget a p W) (hx:∀ i,1 ≤ O i ∧ O i ≤ p i):Doors.Budget a O W:=by
   refine ⟨h.stage,h.sectionBudget,h.sequences,h.room,h.bank,fun H he m d ht=>?_⟩
   have hp:=h.fits H he m d ht; have hx' :0≤ Motion.orbitCost ((Labels.frames G).level d):= zero_le_one.trans (Motion.orbitCost_one_le _)
   refine ⟨(hx _).1,hp.epsilon,hp.tiny,le_trans ?_ hp.funds⟩
   apply mul_le_mul_of_nonneg_right _ hx'; apply add_le_add (hx _).2 le_rfl
abbrev tabP (L:ℕ)(s:ℝ):ℝ:=4*LocalLTE.Dilation.sill s L
lemma tabP_one (l s) (h:0 ≤ s):1≤tabP l s:=one_le_mul_of_one_le_of_one_le (by norm_num) (Real.one_le_exp (mul_nonneg (add_nonneg h zero_le_two) (by positivity)))
-- pre-order. r first. annuities needed
lemma chooseBig (t:Orders)(h:Draft t)(l:ℕ) {C:ℕ→ℝ} (hp:∀ i,1≤ C i) : ∃ Y:ℕ→ℝ, (∀ j, C j≤ Y j) ∧ ∀ j i, StepStages j i → tabP l (t.supportExp i)*C j+1 ≤Y j:=by
   let U(j:ℕ):=∑ i∈Finset.range (j+1),tabP l (t.supportExp i) * C j
   have hu i j:0≤ tabP l (t.supportExp i)*C j:=mul_nonneg (zero_le_one.trans (tabP_one _ _ (h.positive i).le)) (zero_le_one.trans (hp _))
   refine ⟨fun j=>C j+U j+1,fun j=>?_,fun j i ht=>?_⟩
   · exact (le_add_of_nonneg_right (Finset.sum_nonneg fun i _=>hu i j)).trans (le_add_of_nonneg_right zero_le_one)
   exact add_le_add_left ((Finset.single_le_sum (fun i _=>hu i j) (Finset.mem_range.mpr (Nat.lt_add_one_iff.mpr ht.1))).trans (le_add_of_nonneg_left (zero_le_one.trans (hp j)))) _ -- le_add direction? test.
lemma stageDress {p:ℝ}(hp:1 ≤ p)(L A':ℝ)(ht:1≤ A')(_hx:1≤ L):∃ k:ℕ,∀ n:Side,k ≤ n.val→ p*Doors.rate n * L ≤ 1 ∧ p*Doors.rate n*(1+L)*A' ≤ Bid.barunit n:=by
   obtain ⟨u,h⟩:= Doors.pre_tilt (p*(1+L)) A'
   refine ⟨u,fun n hn=>?_⟩
   obtain ⟨hh,hv⟩:= h _ hn
   have he1:0 ≤ Doors.rate n:= (Doors.rate_pos _).le; have hz : 0 ≤ p:=zero_le_one.trans hp; have ha:0≤ A':=zero_le_one.trans ht
   constructor; · nlinarith [mul_nonneg he1 hz]
   nlinarith [mul_nonneg he1 ha]
-- call hhex line at any eligible.ad.
structure Elevates (a:Levels G)(p:ℕ→ℝ)(W:Bid.Worth)(l:ℕ):Prop where
    tilt (H:History G)(m):H.levels=a→∀ d, d≤ a.clock.J m→ let j:= a.clock.J (m+1); Buys H ((Labels.frames G).level d) W m (4*sill (a.params m).supportExponent l * p j) (4*sill (a.params m).supportExponent l*Doors.rate (a.S.block m))
variable {s:Sheet G}
lemma affordsExtra (s:Sheet G) (l:ℕ) {p O:ℕ → ℝ} (hp:∀ i, 1≤O i)(hh:∀ j i, StepStages j i → tabP l (s.profile i|>.supportExponent)*(O j)+1 ≤ p j) : ∃ L:ℕ→ℕ,∀ (M:ℕ→ℕ),L ≤ M→∀ (D:Rolls (ThroughLaunch.raise s M)),∀ (Θ:Protection D)(Y:Delays Θ)(b:Bar Y)(K:Wait b) (a : Levels G), Paid K a →∀ W,Doors.Budget a p W→ Elevates a O W l:=by
   choose C hC using fun i j d:ℕ=> stageDress (tabP_one l _ (s.profile i|>.price_pos.le)) (s.profile j|>.columns) (Motion.orbitCost ((Labels.frames G).level d)) (Motion.orbitCost_one_le _) (s.profile j|>.columns_ge)
   let u j i:= (Finset.range (i+1)).sup (C i j)
   refine ⟨fromMax u,fun l' hl D Θ X b Wk a h M hw=> ⟨fun H m hℓ d hd=>?_⟩⟩
   intro j; let k:= a.clock.J m; have ht : a.params m= s.profile k:= params_eq h m; have h': StepStages j k:= step_paid a m
   have hz: u j k ≤ (D.L j).val:= (le_fromMax u h').trans ((hl _).trans (D.large _).need)
   have hBT: a.S.block m=D.L j:= Push.PriceCompiler.block_eq h _; have hB:= hC k j d (a.S.block m) ((Finset.le_sup (f:=C k j) (Finset.mem_range.mpr (Nat.lt_add_one_iff.mpr hd))).trans (hBT.symm ▸ hz))
   have he:= hw.fits H hℓ m d hd
   have hT:= (Doors.rate_pos (a.S.block m)).le; let S:= tabP l (s.profile k|>.supportExponent); have ha:1 ≤ S:= tabP_one _ _ (s.profile k|>.price_pos.le) -- order
   constructor
   · rw [ht]; exact one_le_mul_of_one_le_of_one_le ha (hp _)
   · rw [ht]; exact mul_nonneg (zero_le_one.trans ha) hT
   · rw [ht,hℓ,show H.S=a.S from congr_arg Levels.S hℓ]; rw [show a.params (m+1)=s.profile j from params_eq h (m+1)]; exact hB.2
   refine le_trans ?_ he.funds; have hM:0 ≤ Motion.orbitCost ((Labels.frames G).level d):=zero_le_one.trans (Motion.orbitCost_one_le ..); apply mul_le_mul_of_nonneg_right _ hM
   rw [ht,hℓ, show a.params (m+1)=s.profile j from params_eq h (m+1)]
   exact (add_le_add le_rfl hB.1).trans ((hh j k h').trans (le_add_of_nonneg_right (mul_nonneg hT (zero_le_one.trans ((s.profile _).columns_ge)))))
end YM.PhysicalNext.Repeat.Legato
