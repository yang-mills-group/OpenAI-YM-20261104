import YM.RG17.Feather
import YM.RG17.Ledger
import YM.RG17.Sparse
/-!
# Pricing measurements in a log window. Can situate anywhere on real r tail now.

Two clocks: age=log(r^-1), actual `s_m`, SampleLog later uses former.
All on the same History. Fixed exponent commitments after choosing r map,
not varying. This doesn't supply momentum/circle convergence or that *one*
such n will afford every requested p-th report.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Set Filter OPE SharpGram.Allow RG PhysicalNext.Repeat.Legato
open scoped Topology BigOperators Classical
variable {G:Gauge}(C:Family G)(h:G.Simple) (b:ℕ)
set_option quotPrecheck false
local notation "Λ"=> Lambda C
local notation "H"=> C.path.levels.clock.hatBeta
local notation "a" => C.S.a
local notation "s" => C.S.scale
local notation "ρ" => OPE.run
def starter : ℕ→ℝ:=fun k=> a k * Λ k ^ b
lemma affordable (i):1 ≤ Λ i:=by unfold Lambda; have hh:= Real.log_nonneg (C.path.levels.fits.delayed i).le; linarith
lemma padding {B : ℕ}: RateIs atTop s (starter C B) (-1):=by
   have ha : RateIs atTop s a (-1):= ⟨Eventually.of_forall (fun _=> C.S.a_pos _),(MergeProof.Ribbons.Note.note_a C.S).pitch⟩
   have hx: RateIs atTop s Λ 0:=by
      let F(t:ℕ):=2*(H t)
      have hh : RateLE atTop s F 0:=by simpa only [zero_add] using (RateLE.const 2 C.S.divergent).mul (armour C)
      refine RateIs.of_sandwich (RateIs.const C.S.divergent (by norm_num : (0:ℝ)<1)) hh (Eventually.of_forall (affordable C)) ?_ C.S.divergent
      apply Eventually.of_forall; intro i; have hp:= C.path.levels.fits.delayed i; have ht:= Real.log_le_sub_one_of_pos (lt_trans zero_lt_one hp); unfold Lambda F; linarith
   have hv:=ha.mul (hx.power B); rw [mul_zero,add_zero] at hv; exact hv
lemma lives (i):0 < starter C b i:=mul_pos (C.S.a_pos _) (pow_pos (zero_lt_one.trans_le (affordable C _)) _)
lemma aperture_exists (r:ℝ)(hr:0<r): ∃ k, starter C b k ≤ r:= (((padding (B:=b) C).tends (by norm_num) C.S.divergent).eventually (ge_mem_nhds hr)).exists
-- choose FIRST finer reporting as manuscript suggests. even without anti.
def locale (r:ℝ):ℕ:= if hr:0<r then Nat.find (aperture_exists C b r hr) else 0
lemma reached {r:ℝ}(hr:0<r): starter C b (locale C b r) ≤ r:=by rw [locale,dif_pos hr]; exact Nat.find_spec (aperture_exists C b r hr)
lemma beforeRank {r:ℝ}{k:ℕ}(hr:0<r)(hk:k<locale C b r): r < starter C b k:=by rw [locale,dif_pos hr] at hk; exact lt_of_not_ge (Nat.find_min (aperture_exists C b r hr) hk)
lemma reachesRank : Tendsto (locale C b) home atTop := by
    refine tendsto_atTop.mpr fun i=> ?_
    filter_upwards [(eventually_all_finset (Finset.range i)).mpr (fun k _=> (nhdsWithin_le_nhds (gt_mem_nhds (lives C b k)) : ∀ᶠ r:ℝ in home,r < starter C b k)),positiveLength] with r hr hh
    exact le_of_not_gt fun hf=>(not_lt_of_ge (reached C b hh)) (hr _ (Finset.mem_range.mpr hf))

variable (hx:Flick C.path.levels) (p:ℝ→ℕ)
structure Sized (p:ℝ→ℕ) : Prop where
    rank : Tendsto p home atTop
    region : ∀ᶠ r in home, a (p r)*Λ (p r)^b ≤ r ∧ r ≤ a (p r)* Λ (p r)^(b+1)
include hx h
lemma ranks : Sized C b (locale C b):= by
    refine ⟨reachesRank C b,?_⟩
    filter_upwards [(reachesRank C b).eventually (eventually_gt_atTop 0),positiveLength] with r hr ht
    refine ⟨reached C b ht,?_⟩
    obtain ⟨i,hi⟩:= Nat.exists_eq_succ_of_ne_zero (show locale C b r ≠ 0 from Nat.ne_of_gt hr)
    rw [hi]
    have hp : i < locale C b r:= by omega
    refine (beforeRank C b ht hp).le.trans ?_
    let P:= Λ i; let Q:= Λ (i+1); let l:ℝ:= (C.S.block i).val
    have h' : P ≤ Q:= by
       have hg:= WilsonStartup.Timing.hat_mono C.path.levels (Gauge.slopeConstant_pos h).le (Nat.le_succ i)
       exact add_le_add_right (Real.log_le_log (zero_lt_one.trans (C.path.levels.fits.delayed i)) hg) _
    have hk: l ≤ Q:= (hx.grade i).trans ((le_add_of_nonneg_left zero_le_two).trans h')
    have hl:0<l:= by unfold l; positivity
    change a i*P^b ≤ a (i+1)*Q^(b+1)
    rw [show a i=a (i+1)*l from Eq.symm (by dsimp [l]; rw [C.S.a_step]; field_simp)] -- index rewrite issues
    rw [pow_succ',mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul hk (pow_le_pow_left₀ (zero_le_one.trans (affordable C i)) h' b) (pow_nonneg (zero_le_one.trans (affordable C _)) _) (hl.trans_le hk|>.le)) (C.S.a_pos _).le
omit hx h
lemma Sized.reach (hp:Sized C b p) : Reach C p := by
   have hy : RateIs home (s ∘ p) id (-1) := RateIs.of_sandwich ((padding (B:=b) C).comp hp.rank)
      (((padding (B:=b+1) C).comp hp.rank).pays (C.S.divergent.comp hp.rank)) (hp.region.mono fun _ h=> h.1) (hp.region.mono fun _ h=> h.2) (C.S.divergent.comp hp.rank)
   refine ⟨hp.rank,?_⟩
   have hh:= hy.rate.neg.inv₀ (by norm_num); norm_num at hh
   refine hh.congr (fun r=> ?_); rw [run,div_neg]
lemma existence : Flick C.path.levels → G.Simple → ∃ p, Sized C b p ∧ Reach C p:=fun h' h=> ⟨_,ranks C h b h',(ranks C h b h').reach ..⟩
end YM.RG17
