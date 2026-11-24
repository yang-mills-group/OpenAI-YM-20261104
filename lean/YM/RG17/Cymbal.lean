import YM.RG17.Fleece
import YM.OPE.Log.Stylist
/-!
# PaidAt -> algebra stat in *all* axes fields (but grid points spend them before extending). Same notation C.Makes & Final.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Filter Set Spec MeasureTheory OPE OPE.Orbits OPE.Log Table Extraction Word
open SharpGram PhysicalNext PhysicalNext.Repeat.Legato Lattice RG Wilson
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{S:Table C.book}{f: Extraction.Order}(F:Spec.Final C f S)(W:Services C f S) {n:ℕ} {K J:Type}[Fintype K][Fintype J]
set_option quotPrecheck false
local notation "T"=>OPE.run
local notation "S'"=> (sole (0:E4))
include W
private lemma route17  (Y m j:ℝ→ℕ) {α:ℝ}(ha:0<α)(hh:α<1)(hY: Height C.S home OPE.run Y α)(hj:Height C.S home OPE.run j 1) {ρ:ℝ} {β:Filter (ℕ×ℕ)}(hζ:β≤ f.fuse) (v:ℝ→ K → C.book.Token)(b:ℝ→K→ Cover)    {p:ℕ} {X A:ℝ→ℝ} (P:ℝ→ C.label p) (hD:∀ᶠ i in home,Dress (C:=C) β S (Y i) (m i) (j i) (X i) (A i) (v i) (b i) p (P i)) (hp:RateLE home T X ρ)(z:Exterior C.book) (hG:∀ᶠ i in home,Screen (C.S.gridPoint (j i) ∘ b i))(hΓ:∀ᶠ i in home,Injective (beside (C.S.gridPoint (j i) ∘ b i) (bearing z))){s u l k: ℝ→ℕ}{μ:ℝ}(hm:0<μ)(h:μ<α)(hs:Height C.S home T s (μ/4))(hu:Height C.S home T u (μ/2))(hl:Height C.S home T l (3*μ/4))(hk:Height C.S home T k μ) : RateLE home T (fun i=> viewing F (beside (C.S.gridPoint (j i) ∘ b i) (bearing z)) (beside (v i) z.letter) - viewing F (beside S' (bearing z)) (beside (sole (⟨p,P i⟩:C.book.Token)) z.letter)) (ρ+(sigma z.letter+μ*Fintype.card (Fin z.n))*μ):=by
    obtain ⟨κ,hκ,hκ₀⟩:= admitted F z.letter ageLarge hk hm
    obtain ⟨hw,he⟩:= bearing_lifetime ageLarge z
    have hS:0< μ/4:=by linarith
    have hK:0<3*μ/4:=by linarith
    apply (hp.mul (hκ.pays ageLarge)).of_norm_le; filter_upwards [hall_range ageLarge hs hl hu hk hY (by linarith) (by linarith) (by linarith) (by linarith) 1 (Fintype.card (Fin z.n)),hκ₀,hG,hD,hΓ,he.short hS ageLarge (Moment_gap ageLarge hs hS), hw.short hK ageLarge (Moment_gap ageLarge hl hK), hs.earlier (by linarith) ageLarge hj] with i hP ht hG H he₁ hr hZ hS
    obtain ⟨B',Q,hk1,h𝓛,hτ,⟨v₀,hv,K,hK,hQ⟩,-⟩:= H.wins
    have h:= stylus_admits F W.schedule hK hS.le hG hZ hr he₁ hP (h𝓛.trans hζ) hτ hQ ht; rw [mingle F (show S.classTokens ∘ beside v₀ z.letter=S.classTokens ∘ beside (v i) z.letter from by rw [beside_commutes,beside_commutes,hv]) he₁] at h; exact h -- simplify next
lemma travels17 (Y m j:ℝ→ℕ) {α:ℝ}(ha:0<α)(hh:α<1)(hY: Height C.S home OPE.run Y α)(hj:Height C.S home OPE.run j 1) {ρ:ℝ} {β:Filter (ℕ×ℕ)}(hζ:β≤ f.fuse) (v:ℝ→ K → C.book.Token)(b:ℝ→K→ Cover)    {p:ℕ} {X A:ℝ→ℝ} (P:ℝ→ C.label p) (hD:∀ᶠ i in home,Dress (C:=C) β S (Y i) (m i) (j i) (X i) (A i) (v i) (b i) p (P i)) (hp:RateLE home T X ρ)(z:Exterior C.book) (hG:∀ᶠ i in home,Screen (C.S.gridPoint (j i) ∘ b i))(hΓ:∀ᶠ i in home,Injective (beside (C.S.gridPoint (j i) ∘ b i) (bearing z))) : RateLE home T (fun i=> viewing F (beside (C.S.gridPoint (j i) ∘ b i) (bearing z)) (beside (v i) z.letter) - viewing F (beside S' (bearing z)) (beside (sole (⟨p,P i⟩:C.book.Token)) z.letter)) ρ:=by
    intro r hr
    obtain ⟨u,hu,hU,h⟩ : ∃ u:ℝ,0<u ∧ u<α∧ρ+(sigma z.letter+u*Fintype.card (Fin z.n))*u<r:=by
       let x(u:ℝ):= ρ+(sigma z.letter+u*Fintype.card (Fin z.n))*u; have hv:x 0<r:=by simpa [x] using hr
       have ht : ∀ᶠ u in home,x u < r:= ((show Continuous x from by unfold x; fun_prop).continuousAt.tendsto.eventually (gt_mem_nhds hv)).filter_mono nhdsWithin_le_nhds
       exact ((positiveLength).and (((show ∀ᶠ u in 𝓝 (0:ℝ),u<α from gt_mem_nhds ha).filter_mono nhdsWithin_le_nhds).and ht)).exists
    obtain ⟨s,hs⟩:= found ageLarge C.path.levels.fits.mesh (show 0≤u/4 by positivity)
    obtain ⟨u',hu'⟩:= found ageLarge C.path.levels.fits.mesh (show 0≤u/2 by positivity)
    obtain ⟨l,hl⟩:= found ageLarge C.path.levels.fits.mesh (show 0≤3*u/4 by positivity)
    obtain ⟨k,hk⟩:= found ageLarge C.path.levels.fits.mesh hu.le
    exact route17 F W Y m j ha hh hY hj hζ v b P hD hp z hG hΓ hu hU hs hu' hl hk r h
omit W
variable {p:ℕ}
/-- Variance purchase from observing. NO external roots on this pricing other than S. -/
lemma noise17 (y:ℝ→ S.Field p) {c:ℝ}(hV:∀ z:Exterior C.book,RateLE home T (fun i=> S.spectra p (y i) z) c): RateLE home T y c:=by
    let A:=Module.finBasis ℂ (S.Field p); have hV'(j:Fin _) : RateLE home T (fun i=>A.coord j (y i)) c:=by
        obtain ⟨b,hb⟩:= reachReads p (A.coord j); simp_rw [←hb,computes]; exact RateLE.sum ageLarge (fun j _=> ((RateLE.const (b j) ageLarge).mul (hV j)).mono (by ring_nf; rfl))
    exact (RateLE.sum (S:=Finset.univ) ageLarge (fun j _=> ((hV' j).smul (RateLE.const (A j) ageLarge)).mono (add_zero c|>.le))).congr (Eventually.of_forall (fun i=> A.sum_repr _))
end YM.RG17
