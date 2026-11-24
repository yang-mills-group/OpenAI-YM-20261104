import YM.Contacts.Procession.Reserve
/-! # Reset for formal Mark with arbitrarily shifted Power. PreWarp coupling = x, new argument `X * rotate w`, full rank perturb marker. Terms indexed by V.Proper m, $q_g V(g) logU^r g^{-r}$. Preserve including prefactors and carry claimed checked-budget explicitly.Mirror not needed at this stage. Some adaptation below of `Milling/Reset.lean` estimates/checks, but not same ticker. -/
namespace YM.Contacts.Milling.Resetter
open Filter Function Set Finset Lattice RG Wilson Bid Exterior Precision Tree Matrix
open Bloch Stationary Garf Pulse Spine Larch Origin PertExtension.Series MeasureTheory
open Pulse.Form Spark House Radial Forge Next.Free Laurent MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Extension.UV.Linear
open Convoy Kale Ion Steam FreeResolvent Lumen
open PowerSeries
open scoped Topology BigOperators Classical Matrix NNReal ContDiff
noncomputable section
variable {α β Υ :Type}{s:ℝ≥0}{n k r j e:ℕ}{m:Side}{G:Gauge}
open Procession Procession.Welcome Procession.Xenon Procession.Sun
lemma rotates_inverse {w:Pow}(h:Uniform w): rotate w*(rotate w*w)=1:= by rw [← rotate_share h]; ring -- rw occurrence danger
lemma rotated_power {w:Pow}(h:Uniform w)(t:ℕ): (w*((rotate w*w)^t))* (rotate w)^(t+2)=1:=calc
  _=(w*(rotate w)^2)*(rotate w*(rotate w*w))^t:= by rw [pow_add]; ring
  _=1:= by rw [rotate_share h,rotates_inverse h]; simp
abbrev rockW (w:Pow)(w':ℕ) := w*(rotate w*w)^w'
lemma rockUniform (w:Pow)(w':ℕ)(h:Uniform w): Uniform (rockW w w'):= h.mul (((rotate_zero w).mul h).power _ w')
section reassemble
variable (w:Pow)(t:ℕ) {U:House α} (F:House α)
def chargeMark (l:ℕ) (n:ℕ):= pin (rockW w t * (rotate w)^l) n
def tickerMark (i j:ℕ) := chargeMark w t i (j-i)
def presageMark (F:House α)(j:ℕ): Pulse.Rack α := fun r=> F j r-∑ i∈Finset.range j,tickerMark w t i j • (if _h:i<j then presageMark F i r else 0) -- include w syntax?
termination_by j
def lowerHouseMark (F:House α): House α:= flipBack (presageMark w t (dazzle F))
lemma presage_eqMark (j r:ℕ) : presageMark w t F j r= F j r - ∑ i∈Finset.range j,tickerMark w t i j • presageMark w t F i r := by
  rw [presageMark]; congr! 1; exact sum_congr rfl fun i hi=> by rw [dif_pos (Finset.mem_range.mp hi)]
lemma presage_botMark (r:ℕ): presageMark w t F 0 r= F 0 r:= by rw [presage_eqMark]; simp
lemma presage_outMark {r j:ℕ}(h:j+r < 2) : presageMark w t (dazzle F) j r=0:= by
   induction j using Nat.strongRecOn with| _ n ih=>
   rw [presage_eqMark, dazzle, if_neg (by omega),sum_eq_zero,sub_zero]; intro i hi; have he:= Finset.mem_range.mp hi; rw [ih i he (by omega),smul_zero]
lemma near_houseMark {r j:ℕ} (hp:Uniform w) : dazzle (lowerHouseMark w t F) j r=presageMark w t (dazzle F) j r:= by
   unfold dazzle lowerHouseMark; split
   next h=> rw [flipBack,if_pos (by omega),show j+r-2+2-r=j from by omega]; rfl
   next hz=> exact (presage_outMark w t F (by omega)).symm
lemma portMark (h:Uniform w)(n): tickerMark w t n n=1:= by rw [tickerMark,Nat.sub_self]; exact (rockUniform w t h).mul ((rotate_zero w).power (rotate w) n)
lemma charterMark (h:Uniform w)(i j:ℕ): pin (rockW w t*(PowerSeries.X*(rotate w))^j) i=if j ≤ i then tickerMark w t j i else 0:= by
   rw [show rockW w t*((PowerSeries.X*(rotate w))^j)= rockW w t*(rotate w)^j * PowerSeries.X^j from (by ring)]; unfold pin; rw [coeff_mul_X_pow']; split <;> rfl
lemma rehouseMark (h:Uniform w)(i r:ℕ): dazzle F i r= ∑ j∈Finset.range (i+1), pin (rockW w t*(PowerSeries.X*(rotate w))^j) i • dazzle (lowerHouseMark w t F) j r:= by
   simp_rw [charterMark w t h i,near_houseMark w t F h]; rw [sum_range_succ,if_pos (by omega),portMark w t h,one_smul,presage_eqMark w t (dazzle F) i]
   rw [show (∑ x∈Finset.range i,(if x ≤ i then tickerMark w t x i else 0) • presageMark w t (dazzle F) x r) = _ from sum_congr rfl (show ∀ j∈Finset.range i,(if j ≤ i then _ else 0) • _ = tickerMark w t j i • presageMark w t (dazzle F) j r from fun x hx=>by rw [if_pos (Finset.mem_range.mp hx).le])]; abel
-- e-form explicitly resets only earlier powers
lemma translatedMark {e r:ℕ}(hr:r≤e+2)(h:Uniform w): lowerHouseMark w t F e r=F e r-∑ i∈Finset.range (e+2-r), tickerMark w t i (e+2-r) • dazzle (lowerHouseMark w t F) i r:= by
    rw [lowerHouseMark, flipBack, if_pos hr,presage_eqMark,dazzle, show e+2-r+r=e+2 from by omega, if_pos (by omega), Nat.add_sub_cancel] -- unfolds wrong
    apply congr_arg; exact sum_congr rfl fun i hi=> congr_arg (tickerMark w t i _ • ·) (near_houseMark w t F h).symm
lemma presage_formMark (h:Shaped F)(u:Uniform w) : Shaped (lowerHouseMark w t F):= by
    have hx j r : Poem (dazzle (lowerHouseMark w t F) j r):= by
       induction j using Nat.strongRecOn with| _ j ih=>
         rw [near_houseMark w t F u,presage_eqMark]; rw [sub_eq_add_neg (dazzle F j r)]; apply Poem.add; · unfold dazzle; split; exact h.poem _ _; apply Poem.empty
         apply Poem.minus; exact Poem.sum _ fun k hk=>(Poem.scale (by rw [← near_houseMark w t F u]; apply ih k (Finset.mem_range.mp hk)) _)
    constructor
    · intro i j; unfold lowerHouseMark flipBack; split; rw [←near_houseMark w t F u]; apply hx; apply Poem.empty
    intro i r hi; unfold lowerHouseMark flipBack; split; swap; rfl
    next he=> rcases hi with ⟨hh,hp⟩|hh; swap; omega; subst i; rw [presage_eqMark, dazzle, show 0+2-r+r=2 from by omega,if_pos le_rfl,h.thin _ _ (Or.inl ⟨rfl,hp⟩),sum_eq_zero]; exact sub_zero _; intro j hj; rw [presage_outMark w t F (by simp only [Finset.mem_range] at hj; omega), smul_zero]
lemma recapturedMark [Fintype α](u:Uniform w)(i r:ℕ)(x:House.Dir α): grate (lowerHouseMark w t F) i r x= grate F i r x -∑ j∈Finset.range i,tickerMark w t j i * grate (lowerHouseMark w t F) j r x:= by
   simp_rw [← glitter,near_houseMark w t F u]; rw [presage_eqMark w t (dazzle F) i,parcel_sub]; apply congr_arg; simp only [design,verse_sum, map_sum]; exact sum_congr rfl fun _ _=> Convoy.design_scale ..
end reassemble
section guards
local notation "Ζ" => Swatch G m
local notation "R" => Link G m
variable {V P:Link G m→ℝ}
lemma truncatedMark (h:GuardsL V k) (j:ℕ) (hj:j≤k): GuardsL (prepare j V) j:= by
   let W:=prepare j V; have he:Rays j (W-V):= dream j h.analytic; have ha: AnalyticAt ℝ W 0:=prepared ..; have hl (L : R →L[ℝ] R) (hl:∀ x,V (L x)=V x)(x:R): W (L x)=W x:= by unfold W prepare; exact sum_congr rfl fun i _=> (woven h.analytic L x i).symm.trans (congr_arg (fun f:R→ℝ=> jet f i x) (funext hl))
   refine ⟨continuous_iff_continuousAt.mpr (fun x=> (prepared ..).continuousAt),ha,fun u=> hl _ (h.color u),?_⟩
   let L : Ζ→R:=moveField; let P: Ζ→L[ℝ] R:= ContinuousLinearMap.snd ℝ _ _
   have hh: Rays j ((W-V)∘moveField-(W-V)∘ P):= (merkin (ha.sub h.analytic) he _ moveField_analytic moveField_zero).sub (merkin (ha.sub h.analytic) he _ (P.analyticAt _) (map_zero _))
   convert (hh.add (h.grade.weaker hj)) using 1; ext x; change W (moveField x)-W x.2 = W (moveField x)-V (moveField x) - (W x.2-V x.2) + (V (moveField x)-V x.2); abel
lemma preservesTotalMark {P:Υ→ Link G m→ℝ} (s:Finset Υ)(h:∀ i∈s,GuardsL (P i) k): GuardsL (∑ i∈s,P i) k:= by
   let Y:= fun x=>∑ i∈s,P i x; change GuardsL _ _; rw [show (∑ i∈s,P i)=Y from funext fun i=> Finset.sum_apply ..]; refine ⟨continuous_finsetSum _ fun i hi=> (h i hi).cont, ContDiffAt.analyticAt (ContDiffAt.sum fun i hi=>(h i hi).analytic.contDiffAt),fun u x=> sum_congr rfl fun i hi=>(h i hi).color .., fun v=>?_⟩; unfold Y; simp_rw [← Finset.sum_sub_distrib]; exact Asymptotics.IsBigO.sum fun i hi=> (h i hi).grade v
lemma shiningMark (h:GuardsL V k)(b:ℝ): GuardsL (b • V) k:= by
   have he : (b • V)=(fun x=> b* V x):= rfl; rw [he]; refine ⟨continuous_const.mul h.cont,analyticAt_const.mul h.analytic,fun u x=> congr_arg (b*·) (h.color u x),?_⟩; intro v; simp_rw [← mul_sub]; exact (h.grade v).const_mul_left _
variable {F: House (Lines G m 1)}
lemma sealsMark (w: Pow)(t:ℕ)(ht:Uniform w)(h:sealedL F k) : sealedL (lowerHouseMark w t F) k:= by
   let V:= lowerHouseMark w t F; intro i hi; change GuardsL (wind V k i) (k-i); induction i using Nat.strongRecOn with| _ i ih=>
   let U (j:ℕ):= prepare (k-i) (wind V k j); let T:= Finset.range (k-i); let W j : Link G m→ℝ:= tickerMark w t j i • U j; let M:=∑ j∈Finset.range i,W j; suffices he:wind V k i=wind F k i-M by
      rw [he]; refine (color_walk (h i hi) (preservesTotalMark (P:=W) _ ?_)).2; intro j hj; have hj:=Finset.mem_range.mp hj; exact shiningMark (truncatedMark (ih j hj (by omega)) _ (by omega)) _
   funext x; change (∑ r∈T,grate _ i r x)= _; unfold V M; simp_rw [recapturedMark w t F ht i,Finset.sum_sub_distrib]; rw [sum_comm (s:=T), Pi.sub_apply, Finset.sum_apply]; apply congr_arg; refine sum_congr rfl fun j hj=>?_ ; have hj:= Finset.mem_range.mp hj; change (∑ r∈T, _)= _ * ∑ r∈T,jet _ _ _ ; rw [← mul_sum]; congr 1; refine sum_congr rfl fun r hr=> ?_; rw [wind_jet]; rw [if_pos (by unfold T at hr; simp only [Finset.mem_range] at hr; omega)]
end guards
end
end YM.Contacts.Milling.Resetter
