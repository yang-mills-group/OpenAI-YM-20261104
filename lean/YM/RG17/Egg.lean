import YM.RG17.Cymbal
/-!
# At actual apertures. Paying the WHOLE grid. This lives in S,
W in L at all frames at each r. Uses Reader protocol through V Cut.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Filter Set Spec MeasureTheory OPE OPE.Orbits OPE.Log Table Extraction Word
open SharpGram PhysicalNext PhysicalNext.Repeat.Legato Lattice RG Wilson
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{S:Table C.book}{f: Extraction.Order}(F:Spec.Final C f S)(W:Services C f S) {n:ℕ} {K J:Type}[Fintype K][Fintype J]
set_option quotPrecheck false
local notation "S'"=> sole (0:E4)
local notation "T"=>OPE.run
variable (z:Exterior C.book) {t:ℕ}
private lemma clearings : ∃ δ>0,ClearOf 0 (bearing z) δ:=by
   obtain ⟨M,η,hM,hη,hv⟩:= roomCosts (K:={z.point}) (isCompact_singleton) (singleton_subset_iff.mpr z.clear)
   have he(j k)(h:j≠k):= (hv 1 one_pos z.point (mem_singleton z.point)).spaced j k h
   refine ⟨η,hη,⟨fun j=>?_,fun i j hi=>?_⟩⟩
   · simpa [posed,bearing,horizonPin,Points.head] using (he 0 j.succ (Ne.symm (Fin.succ_ne_zero _))) -- norm_sub
   simpa [posed,bearing] using (he i.succ j.succ (Fin.succ_injective _|>.ne hi))
include F
private lemma plantAxes : S.classTokens ∘ z.letter=S.classTokens ∘ names (fields S z):=by
    funext i; change _=(⟨_,S.project _ (S.representative _ _)⟩:S.Tag); rw [S.rep]; rfl
private lemma uponStand (c:C.label t) : glance F none (viewing F (beside S' (bearing z)) (beside (sole (⟨t,c⟩:C.book.Token)) z.letter)) = S.spectra t (S.project t c) z :=by
    have ht:= bearing_clear z
    rw [← Prescription.one_test t z c F.room.kernel,glance_sees F none _ _ ht]; unfold Prescription.reading; simp only [spectator, sub_zero, if_pos ht]; rfl
lemma fault17 (y:S.Field t): upon S t 0 (bearing z) (fields S z) y=S.spectra t y z:=by
    obtain ⟨w,rfl⟩:= S.onto t y
    let v:Labels S (fun _ : Unit=>t):=sole (S.project t w); let x:= beside S' (bearing z); have ht:=bearing_clear z
    rw [← uponStand F z w]; change whole (spectator F none) _ v _ _ = _; rw [← read_algebra F none ht]; congr 1
    symm; refine mingle F ?_ ht; rw [beside_commutes,beside_commutes,plantAxes F]; refine congr_arg (fun z=>beside z (S.classTokens ∘ names (fields S _))) ?_
    funext i; change _=(⟨_,S.project _ (S.representative _ _)⟩: S.Tag); rw [S.rep]; rfl
variable (R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
-- consumes ANY paid-at selector
include W R
lemma fines (Y m j:ℝ→ℕ){α:ℝ}(ha:0<α)(hh:α<1)(hY:Height C.S home T Y α)(hj:Height C.S home T j 1){ρ:ℝ}{β:Filter (ℕ×ℕ)}(hζ:β≤f.fuse){d:K→ℕ} (v:ℝ→Labels S d)(b:ℝ→K→ Cover){X A:ℝ→ℝ} (P:ℝ→ C.label t) (hD:∀ᶠ i in home,Dress (C:=C) β S (Y i) (m i) (j i) (X i) (A i) (names (v i)) (b i) t (P i)) (hp:RateLE home T X ρ) (hG:∀ᶠ i in home,Screen (C.S.gridPoint (j i) ∘ b i))(p:GradePrice R d v 0) (hX:∃ M η:ℝ, 0≤M ∧0<η ∧ ∀ᶠ i in home,WithinRoom i M η (C.S.gridPoint (j i) ∘ b i) 0): RateLE home T (fun i=>R.packet t (C.S.gridPoint (j i) ∘ b i) (v i) 0-S.project t (P i)) (max (-(t+1:ℝ)) ρ):=by
    obtain ⟨M,η,hM,hη,hB⟩:= hX; apply noise17; intro z
    let B (i:ℝ):= C.S.gridPoint (j i) ∘ b i; have hr:Tendsto id home home:=tendsto_id
    obtain ⟨h₁,h₂⟩:= room_regime (X:=B) (O:=fun _=>0) hr hM hη hB
    have he: ∀ᶠ i in home, Injective (beside (B i) (bearing z)):=by
        apply epoch_space ageLarge h₂ _ (a:=1) one_pos
        unfold enveloped OPE.away at h₁; simpa only [sub_zero] using! h₁
    have hx: RateLE home T (fun i=> whole S (B i) (v i) (bearing z) (fields S z)- S.spectra t (S.project t (P i)) z) ρ:=by
        apply (travels17 F W Y m j ha hh hY hj hζ (fun i=>names (v i)) b P hD hp z hG he).transfer
        filter_upwards [he] with i hi
        have hy:= mingle F (show S.classTokens ∘ beside (names (v i)) z.letter=S.classTokens ∘ beside (names (v i)) (names (fields S z)) from by rw [beside_commutes,beside_commutes,plantAxes F z]) hi
        change ‖whole (spectator F none) _ _ _ _- _‖ ≤ _; rw [← uponStand,← read_algebra F none hi,← hy, ← map_sub]; exact glance_bound ..
    obtain ⟨δ,hδ,hL⟩:= clearings z
    let u(i:ℝ):= S.spectra t (R.packet t (B i) (v i) 0) z; have hU:RateLE home T (fun i=>whole S (B i) (v i) (bearing z) (fields S z)-u i) (-(t+1:ℝ)):=by
        have h':= formulaOn R W hM hη (fields S z) t p (show home≤home from le_rfl) B (fun _=>0) (fun _=>bearing z) (fun _=>none) hB hδ (Eventually.of_forall (fun _=>hL)); simp only [Pi.zero_apply,Finset.sum_const_zero,add_zero] at h'; apply h'.congr
        filter_upwards with i
        change _-_= _-u i; congr 1; rw [← packet_read F R _ _ _ _ _ none t (bearing_clear z)]; exact fault17 F z _
    apply (((hx.mono (le_max_right ..)).add (hU.neg.mono (le_max_left ..)) ageLarge)).congr (Eventually.of_forall fun i=>?_)
    rw [map_sub]; change _ - _ + -(_-u i) = u i-_; abel
end YM.RG17
