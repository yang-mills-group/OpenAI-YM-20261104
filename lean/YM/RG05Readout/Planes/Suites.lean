import YM.RG05Readout.Planes.Checkpoint
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Planes
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Halls Shadow Flatten
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}
    {b k l:ℕ}{Q:ℝ}(h:C.Makes){D: Address.Rail C}{B:ℕ→ℕ→ℝ}
set_option quotPrecheck false
open Pulse Extraction Extraction.Lease
open Push.RelayDifference
variable {D:Address.Rail C}

variable {f: Extraction.Order}

/-! A transcription at common origin: affordable → vetted literal against calibrated matrices, absorb a finite bank then same at ALL higher SBP orders on-demand. For low-weight planes repaint them further. -/
open Bay Chalice

/-!
# Cone receipts.Boolean Ward.
 Weighted REAL ancestry maps. Projection kernel not discarded here. This proves linear inverse attenuation for surviving low-engineering weights and propagation bound for the rest, not lower/separated aperture budget by assumption. Using m≫ as required from Husk.C. -/
local notation "Z!"=> C.path.levels
local notation "χ"=> Address.clear C
local notation "S"=> Palette C d
local notation "J"=> Mark C d
local notation "ξ"=> C.S.block
local notation "L"=> C.S.block i
local notation "p!"=> BudgetPoint
variable {e:ℕ}{s t α A E:ℝ}
local notation "ΠΩ"=> Address.clear C d e
local notation "T"=> LinearMap.id (R:=ℂ) (M:=S) - Address.clear C d e
local notation "Ω"=> amplify d C L
/-!
# Actual limiting dictionary including transitions on same extraction. E units threshold within. Holds in kernel identified by all Poem tests.This is same linear mapping in ANY extraction.H.Phase fields ported by common T.F. -/
open Function Filter MeasureTheory Extraction Next.Extract
open Petals Dash
variable {b₀:ℕ→ℕ} (Y:∀ d:ℕ,Cutoffs→ Emblems C d)
variable {T₀ S₀:YM.Table C.book}{L0:ℕ→YM.Table C.book}{W:DiffPlan T₀}{R:Dash.Bin S₀}(H:Next.Extract.Base C f S₀ L0 R T₀ W) {g:Extraction.Order}
variable {G':∀ d:ℕ,ℕ→Palette C d→ₗ[ℂ] C.label d}(hp:Chalice.Anchored D B h b₀ Y)(ht:Tune (dims:=b₀) H Y g G')
variable {q:Extraction.Order} {θ:∀ d:ℕ,Emblems C d}(hΘ:Tempo Y b₀ q θ)(hF:q.fuse ≤ (f.refine g).fuse)

include hΘ
local notation "Q"=> finer (θ d)
local notation "P'"=> feeling Y d
-- through whole matrix limits. both directions
lemma Tempo.across (he:b₀ d ≤ m)(hm:m ≤ i): Tendsto (feeling Y d m i hm) q.fuse (𝓝 ((finer (θ d) hm).toLinearMap.toContinuousLinearMap,(finer (θ d) hm).symm.toLinearMap.toContinuousLinearMap)):=by
   induction i,hm using Nat.le_induction with
   | base=> unfold feeling; dsimp only; simp_rw [base_value]; exact tendsto_const_nhds
   | succ i hi ih=>
      let X:= θ d i; let Z:= finer (θ d) hi; let h:= P' m (i+1) (hi.trans i.le_succ); let W:= finer (θ d) (hi.trans i.le_succ)
      have hV:= hΘ.til d i (he.trans hi)
      apply Tendsto.prodMk_nhds
      · apply Dash.fit_plane (fun u=> (finer (Y d u) (hi.trans i.le_succ)).toLinearMap) W.toLinearMap
        intro x; have hv:= arcing (V:=S) hV.fst_nhds (arcing (W:=fun u=> (P' m i hi u).fst) ih.fst_nhds (tendsto_const_nhds (x:=x))); rw [show W= _ from finer_next hi]; apply hv.congr
        intro j; rw [Address.finer_next hi]; dsimp only [feeling]; rw [finer_next (le_refl i),base_value]; rfl
      apply Dash.fit_plane (fun u=>(finer (Y d u) (hi.trans i.le_succ)).symm.toLinearMap) W.symm.toLinearMap; intro x
      have hv:= arcing (W:=fun u=> (P' m i hi u).snd) ih.snd_nhds (arcing hV.snd_nhds (tendsto_const_nhds (x:=x))); rw [show W= _ from finer_next hi]; apply hv.congr; intro j; rw [Address.finer_next hi]; dsimp only [feeling]; rw [finer_next (le_refl i),base_value];rfl
-- at same cash.Frame.J.W
noncomputable abbrev lightest (C:Family G)(d m i:ℕ):ℂ:= ((C.S.a i:ℂ)/(C.S.a m:ℂ))^d
local notation "G!"=> lightest C d m i
variable (w:Palette C d)
omit hΘ in
lemma summit {i m N p:ℕ} (u:Emblems C d) (v:Palette C d) (ht:m≤ i)(hv:i ≤ N)(g:Body):
    fieldC C i N p d (Many.point u v i N) g= fieldC C m N p d (Many.point u (lightest C d m i • (finer u ht).symm v) m N) g := by
   let c:= lightest C d m i; rw [weave_fine hv,weave_fine (ht.trans hv),sumwalk u ht hv,map_smul,LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, Harvest.field_translate]; unfold Pulse.fieldC; rw [smul_smul]; congr 1; unfold Pulse.gate lightest; simp_rw [div_pow]; have hm: ↑(C.S.a m)≠(0:ℂ):=Complex.ofReal_ne_zero.mpr (C.S.a_pos _).ne';field_simp
variable (u:Palette C d)(v:Palette C d)
include ht H hF
-- use all script, no V if finite Y.Ar.
lemma tune_level (ht':m≤ i)(hm:b₀ d ≤ m)(v:S) : (T₀.project d (G' d i v)) = T₀.project d (G' d m (lightest C d m i • (Q ht').symm v)):=by
    obtain ⟨D⟩:=Contacts.Foci.available H.kernel.translations d
    obtain ⟨j,hj⟩:=(Bay.selected T₀ H.kernel D).exists; obtain ⟨Z,hZ⟩:= hj
    apply hZ; funext k
    let B:= fun u':Cutoffs=> v; let K:= Y d; let x(u':Cutoffs):= (lightest C d m i) • ((finer (Y d u') ht').symm v)
    let φ:=q.fuse; let Qz:= Z k
    have hu:= arcing ((Tempo.across Y hΘ hm ht').snd_nhds) (tendsto_const_nhds (x:=v)); let p:=lightest C d m i • (Q ht').symm v; have htX: Tendsto x φ (𝓝 p):= hu.const_smul _
    have ht'₁:= echo_all K B H (φ:=q.fuse) (Z:=G' d i) (m:=i) (le_trans hF (Tails.refine f g).fused) (x:=v) tendsto_const_nhds (fun s j Z=> (ht.pending d _ (hm.trans ht') s _ Z).mono_left hF) j Qz
    have ht₂:= echo_all K x H (m:=m) (φ:=q.fuse) (Z:=G' d m) (le_trans hF (Tails.refine f g).fused) htX (fun s j Z=> (ht.pending d _ hm s _ Z).mono_left hF) j Qz
    apply tendsto_nhds_unique_of_eventuallyEq ht'₁ ht₂
    filter_upwards [(cutoff_grows q).eventually_ge_atTop i] with u hu using congr_arg _ (summit (Y d u) v ht' hu Qz.opening) -- adjust args
end YM.RG05Readout.Planes
