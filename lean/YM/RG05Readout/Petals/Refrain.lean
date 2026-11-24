import YM.RG05Readout.Petals.Mute
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

/-!
# Common ordered lifts

Includes all vectors in primary Palette and all physical analyses in this
kernel on ANY finer filter.Limited request d moves the cutoff threshold tail,
not the Family, not the fit of existing columns.M component computed on
same f order. `Reserve` for all gauges basis.Price.Grammar.Cov.
-/
variable {T S:YM.Table C.book}{L0:ℕ→YM.Table C.book}{E':DiffPlan T}{R:Dash.Bin S} (H:Next.Extract.Base C f S L0 R T E')(hF:∀ d, UVExt.Slots.StrongBin C R f d)
variable {w:Worth}{ζ:ℕ→ℕ}(Y:OPE.Package C w ζ D)(Ys:Storage C D)(hG:G.Simple)
open Next.Extract
local notation "x!"=> Fin
local notation "φ₀"=> f.fuse
variable {dims:ℕ→ℕ}(X:∀ d:ℕ,Cutoffs→Address.Emblems C d)(hx:∀ d:ℕ,UniformM f (X d) (dims d) D B h)
-- root selection α phases on common Period.Real matrices along this order.Later choose their limits down further.
local notation "A!"=> ∀ d:ℕ,ℕ→Palette C d→ₗ[ℂ] C.label d
structure Tune (g: Extraction.Order) (Z:∀ d:ℕ,ℕ→Palette C d→ₗ[ℂ] C.label d) :Prop where
   pending : ∀ (d m:ℕ), dims d ≤ m → ∀ i:Pages C d, Script (X d) (fun _=>playlist i) m (f.refine g).fuse T H.kernel (Z d m (playlist i))
   fixed (d m:ℕ):dims d ≤ m →∀ v,(R d).trueP (Z d m v)=Z d m v
include H
lemma forums (d:ℕ) : ∃ (j:ℕ) (p:ℕ) (Z: Fin p→Poem C j) (c:ℝ), Proctor C f R j d _ Z c:=by
    obtain ⟨D⟩:=Contacts.Foci.available H.kernel.translations d
    obtain ⟨j,hp⟩:= (Bay.selected T H.kernel D).exists; obtain ⟨Z,hZ⟩:=hp
    let t:= Fintype.equivFin D.index
    have he:Injective (LinearMap.pi (fun i=>Poem.passField (Z (t.symm i)) T H.kernel.smooth d)):=by
        intro x y ht; apply hZ; funext i; have hx:= congr_fun ht (t i); change Poem.passField (Z (t.symm _)) T H.kernel.smooth d x= Poem.passField (Z (t.symm _)) T H.kernel.smooth d y at hx; rw [t.symm_apply_apply] at hx; exact hx
    exact ⟨j,_,Z ∘ t.symm, proctor H (Z ∘ t.symm) he⟩
local notation "S!"=> Σ d:ℕ, Σ m:{m:ℕ//dims d ≤ m}, Pages C d
include h hx hG hF Ys Y
set_option maxHeartbeats 450000 in
lemma summon : ∃ g : Extraction.Order, ∃ Z : (∀ d:ℕ,ℕ→ Palette C d→ₗ[ℂ] C.label d), Tune (dims:=dims) H X g Z:=by
    choose j p Qt c hP using forums H -- wrong linter
    let k(d):= Finset.univ.sup (fun i:Fin (p d)=>craving (Qt d i) d); have hK(d)(i:Fin (p d)): craving (Qt d i) d ≤ k d:= Finset.le_sup (f:=fun i:Fin (p d)=>craving (Qt d i) d) (Finset.mem_univ _)
    let W(i:S!)(_j:Cutoffs): Palette C i.1:= playlist i.snd.snd
    have hp(v:S!):∃ a:Rowe C v.fst, exactP C f (code v.snd.fst.val (k v.fst) (fastU (X v.fst) (W v) v.snd.fst.val)) R a:=by
       rcases v with ⟨d,m,i⟩; let b:= fun _ :Cutoffs=> playlist i; have he: UniformM f (X d) (dims d) D B h:=hx d; have hq(m':Cutoffs):size (b m') ≤ size (playlist i):=le_rfl; let P:=fastU (X d) b m.val
       have ht:= Eventually.of_forall (f:=f.fuse) hq; exact favored h (X d) b he m.property _ ht Y Ys hG H (hF d) (hP d) le_rfl (by simpa only [Nat.sub_self,pow_zero,inv_one, one_smul] using onboard h (X d) b he m.property _ ht) (hK d)
    choose a ha using hp; let I:= (S!); let J:= fun i:S!=> C.label i.fst
    let A i (q:ℕ):= ∃ D:ℝ,0 ≤ D ∧ ∀ᶠ k:ℕ in atTop, ‖a i (f.mesh k,q)‖≤ D
    have ht(i:S!): ∃ b:ℝ,0≤ b∧ f.late fun n p=>‖a i (n,p)‖≤b:=by
       obtain ⟨k,hk⟩:=(ha i).2.2.1; exact ⟨|k|,abs_nonneg _,hk.mono fun _ hh=>hh.mono fun _ ht=> ht.trans (le_abs_self _)⟩
    have hZ: Reserve f A («X»:=J) (fun i n p=>a i (n,p)):=Reserve.of_norm (fun i=> (ht i).choose_spec.2.mono fun k hk=> ⟨_,(ht i).choose_spec.1,hk⟩) (fun _ _ h=>h) (fun i=>ht i)
    obtain ⟨g,z,y,hY⟩:= hZ.gather
    let A': A! := fun d m=> if hm:dims d ≤ m then playlist.constr ℂ (fun i:Pages C d=>y (⟨d,⟨m,hm⟩,i⟩:S!)) else 0
    have hv(d m:ℕ)(hm:dims d ≤ m)(i:Pages C d): A' d m (playlist i)=y (⟨d,⟨m,hm⟩,i⟩:S!):=by unfold A';rw [dif_pos hm];exact Module.Basis.constr_basis ..
    have he(i:S!): Tendsto (a i) (f.refine g).fuse (𝓝 (y i)):= Extraction.Order.along (hY.limits i) -- type reducible?
    have hp : (f.refine g).fuse ≤ f.fuse := (Tails.refine ..).fused
    refine ⟨g,A',fun d m hm i=> ?_,fun d m hm v=> ?_⟩
    · let j:S!:=⟨d,⟨m,hm⟩,i⟩; rw [hv d m hm i]; refine audible h (X d) (W j) H (hF d) hp (hx d) hm (size (playlist i)) (Eventually.of_forall fun _=>le_rfl) Y Ys hG (hP d) (ha j) (hK d) (he j) -- coerce Sigma def
    apply stand_fast _ v; intro i; let j:S!:= ⟨d,⟨m,hm⟩,i⟩
    rw [hv _ _ hm i]; exact tendsto_nhds_unique_of_eventuallyEq (arcing (W:=(R d).step) ((H.carries d).P.mono_left hp) (he j)) (he j) (Eventually.of_forall ((ha j).1))

variable {g:Extraction.Order} {Z:∀ d:ℕ,ℕ→ Palette C d→ₗ[ℂ] C.label d}(hZ:Tune (dims:=dims) H X g Z)
include hZ
-- pads report ANY θ. Requires observer sequence bounded over original f.
lemma Tune.projection (hm:dims d ≤ m){A:Palette C d}{φ:Filter Cutoffs}(hp:φ ≤ (f.refine g).fuse)(hA:Tendsto M φ (𝓝 A))(hL:∃ c:ℝ,∀ᶠ i in f.fuse,size (M i) ≤ c):
    Script (X d) M m φ T H.kernel (Z d m A) ∧ ∀ᶠ k:ℕ in atTop,∃ V:Rowe C d,exactP C f (code m k (fastU (X d) M m)) R V∧ Tendsto V φ (𝓝 (Z d m A)):=by
     have hg:= hp.trans (Tails.refine f g).fused; have he:= echo_all (X d) M H hg hA (Z:=Z d m) (m:=m) (fun i j P=> (hZ.pending d m hm i j P).mono_left hp); refine ⟨he,?_⟩
     obtain ⟨c',hc⟩:= hL; obtain ⟨j,p,Q,c,hP⟩:= forums H d
     filter_upwards [eventually_all.mpr (fun i:Fin p=>eventually_ge_atTop (craving (Q i) d))] with k hi; have ht:=onboard h (X d) M (hx d) hm c' hc; obtain ⟨v,hx'⟩:= favored h (X d) M (hx d) hm _ hc Y Ys hG H (hF _) hP le_rfl (by simpa using ht) hi
     refine ⟨v,hx',sounding H hg hP _ (Z d m A) (fun i=>?_) (hZ.fixed d m hm A) v hx' (fun i=> (with_pledge h (m:=m) (Q i) _ Y hG ht (hi i)).mono_left hg)⟩
     have hv:=he j (Q i); rwa [Poem.intact (h:=H.kernel.laws.toSymmetric)] at hv
end YM.RG05Readout.Petals
