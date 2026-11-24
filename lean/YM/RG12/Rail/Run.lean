import YM.RG12.Rail.End
import YM.RG12.Common.Concourse
/-! # Schedule and public intermediate physical profile

At every pair of contiguous *interior* levels of all sufficiently late stages, prove
polynomial-in-meter (log-inverse-coupling PURPOSE; not coupling powers) error for
reading calibrated engineering & filtration-compatible frames *across* the two
ACTUAL measuring radii. This is where k comparisons transition to progressions,
and identifies the specific residual rate still missing for full-history RG12.
The techniques cover arbitrary all-separation fixed demands on the indicated rays,
not contacts, use actual cells/on-axis configurations and require no putative
coincidence identities or series. Don't re-extract for each dimension or mask;
can order as in RG12.Canonical.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Rail
open Function Set Filter Lattice RG Wilson Next.Rank Next.Rank.Atlas Station Prayer Perch Glimmer
open RG.Supply Push.PriceCompiler PhysicalNext.RankCovariance
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G} (h:G.Simple)
section scheduling
variable {X:Sheet G} {P:Rolls X} {D:Protection P}
-- force Slugg by selecting appropriately, not relying on any diagnostic-measuring estimates
-- that depend on the resulting calendar.
lemma fits (U:Delays D) : ∃ V:Delays D, DelayLe U V ∧ ∀ (Q:Delays D)(Z:Bar Q)(B:Wait Z), DelayLe V Q → ∀ A:Levels G,Paid B A→ Slugg A:=by
    let d (i:ℕ):=(i+1:ℝ)⁻¹
    choose x hx using fun i => eventually_atTop.mp ((bill_lo (show 0 < d i from by unfold d; positivity)).eventually_ge_atTop ((P.L i).val:ℝ))
    refine ⟨{U with betaEntry:= fun i=>max (U.betaEntry i) (x i)},⟨fun _=>le_max_left ..,le_rfl,le_rfl,le_rfl⟩,?_⟩
    intro Q Z W h A hA b hb
    have hq := ((tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R:=ℝ)|>.atTop_add (tendsto_const_nhds (x:=(1:ℝ))))).comp (A.fits.deep.comp (tendsto_add_atTop_nat 1))).eventually (ge_mem_nhds hb)
    filter_upwards [hq] with k hk
    let i:=A.clock.J (k+1); specialize hx i (A.clock.hatBeta k) ((le_max_right ..).trans ((h.beta i).trans (hA.pays k))) -- delay projection
    change ((A.clock.schedule.block k).val:ℝ) ≤ _; rw [← A.fits.sameFactor,hA.lengths]; exact hx.trans (billed _ hk)
end scheduling
open Commission
-- Specifies interior sets and common coverage. C-rate f may exchange k->older emergency connector,
-- no claim illuminates all k. Port is championed same M. d arbitrary finite.
structure Outbound (P:Port C)(lit:ℕ→ Prop) (hC:C.Makes):Prop where
    speed : Slugg C.path.levels
    covered : Covered P hC
    
    offers (d : ℕ): ∀ᶠ k in atTop, lit k →∃ U:ℕ→ℕ→MergeProof.East.TableL C d,MergeProof.East.Poised (P.panels d) P.chart hC P.haar P.locality (MergeProof.East.trays d) (P.budget d) k U
    scope : ∀ᶠ k in atTop,lit (P.rate k)
-- strengthen Concourse.staff
open Pert.Dense Precision
lemma allLit {p:Sheet G}{w:Rolls p}{θ:Protection w}{D:Delays θ}{B:Bar D}{M: MapPrices}{O:HaarBudget G}{J:ChartRatio G}
    {W:Wait B}(U:StationPort W M O J)(h:U.Certified) (hW:Paid W C.path.levels) (g:ℕ→ℕ) (hg:Tendsto g atTop atTop) (he: ∀ᶠ k:ℕ in atTop,
     g k ≤ k ∧ Interior W C.path.levels (g k) ∧ (C.S.a (g k))/(C.S.a k) ≤ C.path.levels.clock.hatBeta k)(hv:Slugg C.path.levels) (hC:C.Makes)(x:Binding C)(hK:x.prices=M)(hG:Next.Rank.East.ParadeX C):
      Outbound (⟨g,U.panels,U.cost,O,J,x⟩:Port C) (Interior W C.path.levels) hC:=by
     refine ⟨hv,⟨hg,h.reasonable,fun d=>?_⟩,h.orders C hW x hK hC hG,he.mono fun _ h=> h.2.1⟩ -- h.orders args
     filter_upwards [he,hg.eventually (h.orders C hW x hK hC hG d)] with k he hT
     exact ⟨he.1,he.2.2,hT he.2.1⟩
open Spec Extraction OPE Arche Shapes Roof RG12.Frames YM.MergeProof.East
/-! Public k advancement. After the same filter all-cutoff limit, single choice of Φ across
    all k and horizons at this filter. Only after quota coordinate reads, geometric `Torch` layout
    chooses any sufficiently large fixed denominator N for breaking axis symmetry; no smearing.

`Assembly` stores precise measurement matrix clause on all lit k (including k reached by
an emergency short run-back; Outbound records which k, via exact comparisons in Interior),
and tighter coupling on **contiguous lit pairs only**. `aim` ensures compatible; doesn't assume
rotation compatibility. Inputs to all matrix estimates in EXACT filtration-compatible units.
 -/
open RG12.Desk.Paired
variable {S:Table C.book}{F:Extraction.Order}(U:Final C F S)(P:Port C){lit:ℕ→Prop}
variable {M:∀ d,ℕ→RepChart C d}{ϕ:Filter UVIndex}[ϕ.NeBot]
local notation "B!"=>U.sector.derivatives
local notation "A!"=> C.path.levels
set_option quotPrecheck false
structure Assembly (U:Final C F S)(P:Port C)(lit:ℕ→Prop)(M:∀ d,ℕ→RepChart C d) (Q:Prescription U.sector.derivatives)(hq:Q.Coherent)(ϕ:Filter UVIndex)[ϕ.NeBot] : Prop where
   matrices (d:ℕ)(i₀:Fin 3) (a:Axis):
       let t₀:=(P.panels d i₀).arc; let n:=trays d
       let V:=Desk.Sector U.sector.derivatives d
       let x:=stepLense U d M
       ∃ (Z:ℕ → TableL C d)(K:ℝ), 1 ≤ K ∧
       (∀ᶠ k in atTop,lit k → Good (n:=n) (ϕ:=ϕ) (P.panels d) P.chart U.room.cutoff P.haar P.locality (P.budget d) i₀ (Z k) k) ∧ ∀ᶠ N:ℕ in atTop, let t(k):=torchR C.path.levels t₀ N k
       let R k:= sampleForm U (Shapes.scope a N) d (t k)
       let v k:= x k (Z k) N t₀
       let g k:=Real.sqrt ∘ (R k).eval
       ∀ᶠ k in atTop, lit k → Frames.triangular V ((Desk.official Q hq d).symm.toLinearMap.comp (v k)) ∧ Gram.Regular (R k) (v k) K ∧
         (lit (k+1)→1 ≤ t k/t (k+1)∧∀ i, let u := i; let o:=4*K*fineprint C.path.levels n k
                                g k ((v (k+1)) (Frames.dilate (t k/t (k+1)) u)) ≤ (1+o)*g (k+1) (v (k+1) u) ∧
                                g (k+1) (v (k+1) u) ≤ (1+o)*g k ((v (k+1)) (Frames.dilate (t k/t (k+1)) u)))
open RG12.Desk.Paired -- late?
open MergeProof PhysicalNext.Repeat.Legato.Bandage Org Next.Rank.Tapes.West
include h
lemma charter (hV:Outbound P lit U.room.cutoff)(H:Facilities C F S)(Q:Prescription U.sector.derivatives)(hq:Q.Coherent)(hA:Observing C U.room.cutoff ϕ M)(hJ:ϕ ≤ F.fuse) : Assembly U P lit M Q hq ϕ := by
   constructor
   intro d i₀ a t n V x
   obtain ⟨W,r,L,hR⟩:= H.costlier
   let H' := U.room.cutoff
   have he:0 ≤ (P.panels d i₀).arc:=by have e:=(P.panels d i₀).huge; linarith [Nat.cast_nonneg (α:=ℝ) d]
   have ho : ∀ᶠ k:ℕ in atTop,lit k → ∃ Z, Good (n:=n) (ϕ:=ϕ) (P.panels d) P.chart U.room.cutoff P.haar P.locality (P.budget d) i₀ Z k:=by
      filter_upwards [hV.offers d] with k hk Hx
      obtain ⟨T,hT⟩:=hk Hx
      have hr:1 ≤ mag C.path.levels t k:=by rw [mag_bill]; exact Glimmer.costed t _ he
      let l:Ultrafilter UVIndex:=Ultrafilter.of ϕ
      obtain ⟨q,hI⟩:= compare_in hA hT.early hT.charts _ hr l (Ultrafilter.of_le ϕ)
      exact ⟨q,T,hT,hI⟩ -- structure nest
   obtain ⟨m₀,hM⟩:= eventually_atTop.mp ho
   choose! Y hY using fun k hk hx=>hM k hk hx
   obtain ⟨K,hk,Hh⟩:= slopes (P.panels d) P.chart H' h (hR.toPackage.toTableTickets.system) P.haar P.locality (P.budget d) (hV.covered.2.1 d) i₀ U hA hJ (show 2 ≤ n from Nat.le_add_left ..) hV.speed a Q hq
   obtain ⟨B,hB,hZ⟩:= beacon_cost (n:=n) (P.panels d) P.chart H' h (hR.toPackage.toTableTickets.system) P.haar P.locality (P.budget d) (hV.covered.2.1 d) i₀ U hA hJ (Nat.le_add_left ..) hV.speed a Q hq
   let c:=max K B
   have hL :∀ᶠ k in atTop,lit k→Good (n:=n) (ϕ:=ϕ) (P.panels d) P.chart H' P.haar P.locality (P.budget d) i₀ (Y k) k:=(eventually_ge_atTop m₀).mono fun i hi h=>hY i hi h
   refine ⟨Y,c,hk.trans (le_max_left ..),hL,?_⟩
   filter_upwards [Hh,hZ] with N hH hZ t₁ R v g
   filter_upwards [hH,hZ,hL,(tendsto_add_atTop_nat 1).eventually hL] with k hk hV hz hv he'
   obtain ⟨hp,hH⟩:= hV _ (hz he'); let Z:=R k;let u:=v k
   have hy:0 < B:=zero_lt_one.trans_le hB
   refine ⟨hp,⟨hB.trans (le_max_right ..),fun x=> (hH.upper x).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)),fun x=> (hH.coerc x).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (nonneg_of_mul_nonneg_right ((sq_nonneg _).trans (hH.coerc x)) hy))⟩,fun hr=> ?_⟩
   obtain ⟨X,Y',h1,h2,h3,h4⟩:=hk Y (hz he') (hv hr)
   refine ⟨h3,?_⟩; intro i w o
   have hx(j):Y' j=v (k+1) j:= by change (Y').toLinearMap j =_; rw [h2]
   obtain ⟨hx₁,hx₂⟩:= h4 i; let D(j):= g j; let w':=v (k+1); let t₀:= t₁ k /t₁ (k+1); let z:=fineprint C.path.levels n k
   have hz : 1+4*K*z ≤ 1+o:= by unfold o z; have hf:0 ≤ z:= (Real.exp_pos _).le; change 1+4*K*z ≤ 1+4*c*z; nlinarith only [show K ≤ c from le_max_left ..,mul_le_mul_of_nonneg_right (show K≤c from le_max_left ..) hf]
   rw [hx,hx] at hx₁; rw [hx,hx] at hx₂
   exact ⟨hx₁.trans (mul_le_mul_of_nonneg_right hz (Real.sqrt_nonneg _)),hx₂.trans (mul_le_mul_of_nonneg_right hz (Real.sqrt_nonneg _))⟩
end YM.RG12.Rail
