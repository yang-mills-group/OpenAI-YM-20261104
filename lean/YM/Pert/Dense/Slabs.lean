import YM.Pert.Dense.Canopy
import YM.Pert.Dense.Supplier

/-! On an inflated wait obtain centers with entire rightward slabs of a growing number of eligible *lattice* radii for the old wait. The ratios of consecutive physical probe radii within a slab are still a schedule issue. -/

set_option autoImplicit false
noncomputable section
namespace YM.Pert.Dense
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec Supply PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{d n D k N p m:ℕ}
variable {Θ:Sheet G} {L:Rolls Θ}{E:Protection L}{H:Delays E}{Z:Bar H}
variable {O₀ : HaarBudget G} {J₀ : ChartRatio G} (U:Wait Z)

lemma slab (A:Levels G) (hA:Paid (inflate U) A) {j:ℕ}(hj:Θ.first≤j) : ∃ k, A.clock.J k=j ∧ ∀ m≤ span (A.S.scale k),Interior U A (k+m) := by
   let V:= inflate U; obtain ⟨a,h0,h1,h2⟩:=hA.run j hj
   let s:=A.S.scale a
   have ha:span s ≤ V.window j s:=Nat.le_add_left ..
   have ticks m (hx:m ≤ span s) : A.clock.J (a+m)=j:=h2 _ (by omega) (Nat.add_le_add_left (hx.trans ha) _)
   refine ⟨a,(by simpa using ticks 0 (Nat.zero_le _)),fun m hm=> ?_⟩
   let y:=A.S.scale (a+m); let ℓ:=Real.log ((L.L j).val:ℝ)
   have hs : y = s + m*ℓ:= by
      unfold y; induction m with
      | zero=> simp [s]
      | succ m ih=>
        rw [show a+(m+1)=(a+m)+1 from rfl, A.S.scale_succ,ih (by omega),← A.fits.sameFactor,hA.lengths, show A.clock.J (a+m+1)=j from ticks _ hm]
        push_cast;ring
   have hℓ:ℓ^2 ≤ s := le_trans (show _ ≤ barrier U j from (show ℓ^2 ≤ 1+ℓ^2 by linarith).trans (le_max_left ..)) h0
   have hℓ' : 0 ≤ ℓ := Real.log_nonneg (by
     have he : (3:ℝ) ≤ (L.L j).val:=by exact_mod_cast (L.large j).size
     linarith)
   have hS : y ∈ Set.Icc s (2*s):= by
     rw [hs]; have hp:=le_trans (Nat.cast_le (α:=ℝ).mpr hm) (Nat.floor_le (Real.sqrt_nonneg _))
     change _ ≤ Real.sqrt s at hp; have hy:ℓ ≤ Real.sqrt s:=by nlinarith only [Real.sqrt_nonneg s,hℓ',Real.sq_sqrt (show (0:ℝ) ≤ s by nlinarith only [hℓ]),hℓ]
     exact ⟨by have := Nat.cast_nonneg (α:=ℝ) m; nlinarith,by have hh:=mul_le_mul hp hy hℓ' (Real.sqrt_nonneg s); nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ s by nlinarith only [hℓ])]⟩
   have h0' : U.readyHere j≤ y∧ U.window j y≤ V.window j s := by
      obtain ⟨-, -,hu⟩ := ((Filter.eventually_atTop.mp (on_space U j (zero_lt_one : (0:ℝ)<1))).choose_spec s (le_trans ((show ((Filter.eventually_atTop.mp (on_space U j zero_lt_one)).choose) ≤ barrier U j from le_trans (le_max_right ..) (le_max_right ..))) h0))
      · exact ⟨((thicker U).ready j |>.trans h0 |>.trans hS.1), (hu _ hS).trans (by change _ ≤ canopy U j s+_; omega)⟩
   refine ⟨?_,?_,?_⟩
   · rw [ticks _ hm]; exact h0'.1
   · rw [ticks _ hm];exact h0'.2.trans (h1.trans (Nat.le_add_right ..))
   intro i hi hw; rw [ticks _ hm] at hi ⊢
   dsimp only [V,s] at ha; dsimp only [V,y,s] at h0'
   apply h2 <;> omega


structure Rectangles (C:Family G) : Prop where
   meet : ∃ center:ℕ→ℕ, Tendsto center atTop atTop ∧ Tendsto (fun i=>span (C.S.scale (center i))) atTop atTop ∧
     ∃ arc : ℕ→ℝ,(∀ d,d+6 ≤ arc d) ∧ ∀ h' : (standard C).RealSpin, (standard C).Smooth → ∀ d (N) (R:ℝ),N≤d+2 → 0<R→
       ∀ F:Extraction.Order,∀ World:Table C.book,∀ h:World.Hierarchy,F.Ordered C World→F.PointLimits C World→∀ ε:ℝ,0<ε→
       ∀ᶠ j:ℕ in atTop, ∀ i : ℕ, i ≤ span (C.S.scale (center j)) → Reaches C N d (gap C.path.levels (arc d) (center j+i)) World h h' R ε
lemma rectangles (hC:Paid (inflate U) C.path.levels) (hw:OnPath U C) : Rectangles C:= by
   choose center h using fun j=>slab U _ hC (Nat.le_add_right Θ.first j)
   have hc : Tendsto center atTop atTop := tendsto_atTop.2 fun m=> (eventually_gt_atTop (C.path.levels.clock.J m)).mono
      fun j hj=> (lt_of_not_ge fun hT=> (h j).1 ▸ C.path.levels.fits.mono hT |> fun he=>by omega).le
   have hs : Tendsto (fun i=>span (C.S.scale (center i))) atTop atTop := tendsto_nat_floor_atTop.comp (Real.tendsto_sqrt_atTop.comp (C.S.divergent.comp hc)) -- lemma names
   obtain ⟨arc,hA,hOrder⟩:=hw.reports; refine ⟨center,hc,hs,arc,hA,fun h' hS d n R hn hR F World ht hF h'F ε hε=>?_⟩
   obtain ⟨k,hk⟩:= eventually_atTop.mp (hOrder h' hS d n R hn hR F World ht hF h'F ε hε)
   exact (hc.eventually_ge_atTop k).mono fun j H i hi=>hk _ (H.trans (Nat.le_add_right ..)) ((h j).2 i hi)
end YM.Pert.Dense
