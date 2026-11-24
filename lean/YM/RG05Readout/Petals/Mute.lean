import YM.RG05Readout.Petals.Melody
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Petals
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Halls Shadow Flatten
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}
    {b k l:ℕ}{Q:ℝ}(h:C.Makes){D: Address.Rail C}{B:ℕ→ℕ→ℝ}
set_option quotPrecheck false
local notation "t!"=> (1,false)
local notation "L"=> C.path.levels
local notation "χ"=> C.path.levels.clock.J
local notation "λ₀"=> C.S.toDepth
local notation "Α"=> C.S.a
local notation "R0"=> C.path.rep N p
open Pulse Extraction Extraction.Lease
open Push.RelayDifference
variable {D:Address.Rail C}

local notation "L!"=> Lattice.wrap
variable {f: Extraction.Order}

/-! A transcription at common origin: affordable → vetted literal against calibrated matrices, absorb a finite bank then same at ALL higher SBP orders on-demand. For low-weight planes repaint them further. -/
open Bay Kernel Dash
local notation "i!"=> Cutoffs
local notation "F"=> f.fuse
local notation "Σ!"=> Palette C d
variable (u: ∀ (_i:Cutoffs), Emblems C d)(M:Cutoffs→Palette C d)
-- script supplies from basis inputs on actual Backbone while holding arbitrary localized Root.Late
variable (D₀:Poem C n)
local notation "F!"=> fieldC C m N p d
local notation "ζ"=> D₀.opening
local notation "U!"=> u (N,p)
noncomputable def subtitle (p N m:ℕ)(w:Palette C d):= preamble D₀ N p (fieldC C m N p d (Many.point (u (N,p)) w m N) D₀.opening)
local notation "V₁"=> subtitle u D₀ p N m
lemma voice_plus (a q: Palette C d) (z:Site (C.side N p)) (f:Body) : entrance C _ N p (a-q) z f= entrance C _ N p a z f-entrance C _ N p q z f:=by
    unfold entrance; rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _=> sub_smul ..
lemma curtain (w w':Palette C d) (f:Body) : fieldC C m N p d (w-w') f=fieldC C m N p d w f-fieldC C m N p d w' f:=by
    unfold fieldC; rw [← smul_sub, ← Finset.sum_sub_distrib]; simp_rw [voice_plus, Records.rot_sub]
lemma column_times (q:Goods G (C.side N p))(c:ℂ) : preamble D₀ N p (c • q)=c*preamble D₀ N p q:=by
    unfold preamble; rw [mul_left_comm c]; congr 1; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; unfold Bay.column moment; rw [mul_left_comm c]; simp only [Pi.smul_apply, smul_eq_mul,mul_assoc]; rw [integral_const_mul]
local notation "Lx"=> Palette C d
lemma sings (hm:m ≤ N): IsLinearMap ℂ (subtitle u D₀ p N m):=by
    let U₁:= subtitle u D₀ p N m; have he(w w':Lx):U₁ (w-w')=U₁ w-U₁ w':=by
       unfold U₁ subtitle; rw [weave_fine hm,map_sub,curtain,onward_minus]; rotate_left
       · exact minting (fun _=>finer (u (N,p)) hm w) ζ
       · exact minting (fun _=>finer (u (N,p)) hm w') ζ
       rw [weave_fine hm,weave_fine hm]
    refine ⟨fun x y=> ?_,fun c x=>?_⟩; · have h:=he (x+y) y; rw [add_sub_cancel_right] at h; change U₁ _ = _ + _; exact eq_add_of_sub_eq h.symm
    unfold subtitle; rw [weave_fine hm,map_smul,Harvest.field_translate,column_times,weave_fine hm];rfl
-- If all BASIS detector charges converge, then numerical estimation passes also for inputs depending on cutoff
noncomputable abbrev Pages (C:Family G)(d:ℕ):= Fin (Module.finrank ℂ (Palette C d))
noncomputable abbrev playlist : Module.Basis (Pages C d) ℂ (Palette C d):= Module.finBasis ..
variable {T S:YM.Table C.book}{L0:ℕ→YM.Table C.book}{P:DiffPlan T}{R:Dash.Bin S} (H:Next.Extract.Base C f S L0 R T P)
variable {x:Palette C d}{φ:Filter Cutoffs}(hp:φ≤ f.fuse)
variable {Z:Palette C d→ₗ[ℂ] C.label d}
include H hp
lemma echo_all (hB:Tendsto M φ (𝓝 x))(hz:∀ i: Pages C d, Script u (fun _=> playlist i) m φ T H.kernel (Z (playlist i))): Script u M m φ T H.kernel (Z x):=by
    intro j Q'; let b:C.label d→L[ℂ]ℂ:= Q'.sight.core T (Poem.sanctioned H.kernel.smooth); let g:= b.toLinearMap.comp Z; let B':= (playlist (C:=C) (d:=d)); let D':= Pages C d
    let a (i:D')(p:Cutoffs)(v:Lx):= B'.repr v i * (subtitle u Q' p.2 p.1 m (B' i))
    let Lz(p:Cutoffs):= subtitle u Q' p.2 p.1 m (M p)
    have hV(i:D') : Tendsto (fun p=> a i p (M p)) φ (𝓝 (B'.repr x i*g (B' i))):=by
       have hp := hz i j Q'; rw [Poem.intact (h:=H.kernel.laws.toSymmetric)] at hp; exact ((B'.coord i).continuous_of_finiteDimensional.continuousAt.tendsto.comp hB).mul hp
    have ht:=tendsto_finsetSum Finset.univ (fun i _=>hV i); have he(p:Lx): g p=∑ i:D', B'.repr p i*g (B' i):=by
                                        conv_lhs=> rw [← B'.sum_repr p,map_sum]
                                        exact Finset.sum_congr rfl (fun i _=>map_smul ..)
    have hh:= (show (∑ i:D',B'.repr x i*g (B' i))= g x from (he x).symm); rw [hh] at ht; rw [Poem.intact (h:=H.kernel.laws.toSymmetric)]; refine ht.congr' ?_; filter_upwards [(cutoff_grows f).mono_left hp|>.eventually_ge_atTop m] with j hj
    let W₀:=subtitle u Q' j.2 j.1 m; let W:= (sings (p:=j.2) u Q' hj).mk' W₀; change (∑ i:D', B'.repr (M j) i * W (B' i))= W (M j); conv_rhs=> rw [← B'.sum_repr (M j),map_sum]
    exact Finset.sum_congr rfl (fun i _=> (W.map_smul _ _).symm) -- issue
omit hp H
lemma stand_fast {W: Palette C d→ₗ[ℂ] C.label d}{A:Dash.Bin T}
    (hK:∀ i:Pages C d,(A d).trueP (W (playlist i))= W (playlist i))(v:Palette C d): (A d).trueP (W v)=W v:= by
    let B':= playlist (C:=C) (d:=d); rw [←B'.sum_repr v]; simp only [map_sum, map_smul]; exact Finset.sum_congr rfl fun i _=> congr_arg _ (hK i)
-- converse via charged SNAP. `Script` from any better stencil.
variable {I:Type}[Fintype I]{D₁:I→Poem C n}{c:ℝ}(hP:Proctor C f R n d I D₁ c)
   (w:i!→Palette C d) (w₀:C.label d)
include H hp hP
lemma sounding (hV:∀ i:I,Tendsto (fun x:i!=> preamble (D₁ i) x.1 x.2 (fieldC C m x.1 x.2 d (w x) (D₁ i).opening)) φ (𝓝 ((D₁ i).sight.core T (Poem.sanctioned H.kernel.smooth) w₀)))
   (hW: (R d).trueP w₀=w₀) (v:Rowe C d)(hx:exactP C f (code m k w) R v)
   (hc:∀ i:I,Tendsto (fun x: Cutoffs=> targetB (code m k w) (D₁ i).sight x.1 x.2-preamble (D₁ i) x.1 x.2 (fieldC C m x.1 x.2 d (w x) (D₁ i).opening)) φ (𝓝 0)) : Tendsto v φ (𝓝 w₀):=by
     let y(x:i!):= (R d).step x w₀
     have hz:Tendsto y φ (𝓝 w₀):=by
         have h':= arcing (W:= (R d).step) ((H.carries d).P.mono_left hp) (tendsto_const_nhds (x:=w₀)); rw [hW] at h'; exact h'
     let V(i:I):= snapshots (D₁ i).sight d; have ht(i:I): Tendsto (fun x:Cutoffs=> V i x (v x-y x)) φ (𝓝 0):=by
         let u:= (D₁ i).sight; let S':ℂ:= u.core S H.arrives.born w₀; have hH:S'=u.core T (Poem.sanctioned H.kernel.smooth) w₀:=Dash.faithful H.clean.sharp _ _
         have hx':= hV i; rw [←hH] at hx'
         have ht:= (((hc i).add hx').sub ((on_profile H.family v ((D₁ i).sight) hx.2 H.center).mono_left hp)).sub (arcing (W:=V i) ((u.ready H.arrives.born H.arrives.census.integral d).mono_left hp) hz); rw [zero_add,sub_zero,show S'-_ = 0 from sub_self S'] at ht; apply ht.congr (fun x=> by rw [map_sub]; unfold V; abel)
     let F₁(x):= v x-y x; have hL:= tendsto_finsetSum Finset.univ (fun i (_:i∈@Finset.univ I _)=> (ht i).norm); simp only [norm_zero,Finset.sum_const_zero] at hL; have he:= (hL.div_const c); rw [zero_div] at he
     have h:Tendsto F₁ φ (𝓝 0):= tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall (fun x=> norm_nonneg (F₁ x))) (Eventually.mono (Eventually.filter_mono hp hP.detector) (fun x hx'=> (le_div_iff₀ hP.pos).2 (le_trans (le_of_eq (mul_comm ..)) (hx' (F₁ x) (by unfold F₁ y; rw [map_sub,hx.1,(R d).projection]))))) he)
     have hv:= h.add hz; rw [zero_add] at hv; exact hv.congr (fun x=> sub_add_cancel ..)
-- header order proof may need lean
end YM.RG05Readout.Petals
