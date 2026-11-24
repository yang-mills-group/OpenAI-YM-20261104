import YM.MergeProof.West.Shacks
import YM.MergeProof.West.Commerce

/-!
# Commission the actual windows

Adapted from the Shacks/Commerce clocked proofs. Those rent only when
*all* the Waiting window is available behind the reading scale. It may
be arbitrarily much larger than polynomial log in actual space (only asks
`o(scale i)` **per stage**). Thus to get the *right* nearby-scale cost,
we prove it suffices to have the actual bench length of the panel being
used. The paid window, often much larger, doesn't have to fit here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Lattice Wilson Pressure RG Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Org Input
     Display Display.Docking Filter RG.Supply Next.Rank.Station Next.Rank.Spindle Finset Bid Atlas Cells Edition Dash Spec OS Extraction OS.Ground Analysis West Pump
open scoped Topology BigOperators Classical
variable {G : Gauge} {X : RG.Supply.Sheet G} (B : MapPrices)
variable (O : HaarBudget G) (J : ChartRatio G) {w : Rolls X} {D : Protection w} {T : Delays D} {Z : Bar T}
section Exact

structure RG12Clock (B:MapPrices)(O:HaarBudget G)(J:ChartRatio G) (U : Wait Z)
    (P:∀ d,Tapes.Panel d)(m:ℕ→ℝ)(p:ℕ→ℕ)(k:ℕ→Finset ℕ):Prop where
    rent : ∀ C : Family G, Paid U C.path.levels → ∀ K:Binding C,K.prices=B→∀ᶠ k₀ in atTop,
       let A:= C.path.levels; let j:=A.clock.J k₀
       X.first<j → U.readyHere j ≤ A.S.scale k₀ →
       ∀ i∈k j, let t:= Ship.benchCost Z (P i).arc j (A.S.scale k₀)
       t ≤ k₀ → (∀ i', k₀-t ≤ i' → i' ≤ k₀ → A.clock.J i'=j) →
       ∃ l r, LegacyCost K J (-3) (m i) ((P i).bag j) k₀ (p i) i O l r

lemma rg12_print {k P m p U} (h:RG12Clock B O J (Z:=Z) U P m p k)(W:Wait Z)
    (hs:U.minLength ≤ W.minLength)(hv:U.readyHere ≤ W.readyHere)
    (ht:U.window ≤ W.window): RG12Clock B O J W P m p k := by
   constructor; intro C hc K hp
   filter_upwards [h.rent C (retains_budget hs (fun j=>⟨hv j,ht j⟩) hc) K hp] with i hj
   intro A j he hk; exact hj he ((hv j).trans hk)

-- At fixed commission, limit the comparison-only window; don't
-- rebuild any underlying witness with the new Wait!
private def trimBench (B : Wait Z) (b : ℝ) : Wait Z :=
 { B with
   window := fun j s => min (B.window j s) (Ship.benchCost Z b j s)
   sublin := fun j => squeeze_zero' (by
     filter_upwards [eventually_ge_atTop (0:ℝ)] with s hs
     exact div_nonneg (Nat.cast_nonneg _) hs) (by
     filter_upwards [eventually_ge_atTop (0:ℝ)] with s hs
     exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.min_le_left _ _) hs) (B.sublin j) }

private lemma trim_paid {W : Wait Z} {A : Levels G} (h : Paid W A)(b : ℝ) : Paid (trimBench W b) A :=
  retains_budget (W:=W) (F:=trimBench W b) (show _ from le_rfl) (fun _=>⟨le_rfl,fun _=>min_le_left ..⟩) h

private lemma trim_fired {W:Wait Z} {k b a E} (h:Fired Z W O k b a E) : Fired Z (trimBench W b) O k b a E:=
  fun s hs=> ⟨(h s hs).1,Nat.le_min.mpr ⟨(h s hs).2,Nat.le_refl _⟩⟩

lemma rg12_glide {P k M} (d : ℕ→ℕ→ℝ) (wL : ℕ→ℝ) (m : ℕ→ℝ)(p:ℕ→ℕ) (hm : ∀ d,0 ≤ m d)(hx:∀ d,2 ≤ p d) (simple : G.Simple)
    (hw : ∀ i,0<wL i) (hJ : LocalRatio J) (hs : PreStand X B P k M) (hl : ∀ j,M j≤ (w.L j).val)
    (he:∀ i j,i∈ k j→ Coul ((P i).bag j) (p i) ∧ HLane ((P i).bag j) (p i) (w.L j)∧ reserveX (prepared X.kernel) (p i) j (P i).θ (P i).arc (w.L j).val)
    (hp : ∀ i j,i∈ k j →∀ᶠ s in atTop,Timing (initials B X.profile X.kernel j j) J j (w.L j) ((P i).bag j) (wL j) (d i j) s)
    (U : Wait Z) : ∃ (W : Wait Z), U.minLength ≤ W.minLength ∧ U.readyHere ≤ W.readyHere ∧ U.window ≤ W.window ∧ RG12Clock B O J W P m p k:= by
  obtain ⟨V,hL,hG,hV⟩:= served Z simple O U p (fun i=>(P i).arc) (fun j i=> ((P i).bag j).era) k (fun i=> by have h:=hx i;omega) (fun j=> by linarith only [(P j).huge,Nat.cast_nonneg (α:=ℝ) j]); have hδ:=hp
  have hp i j (h:i∈k j):= hs.reg i j h|>.2 (w.L j) (hl j)
  have ht : Tendsto (Ship.preHat Z) atTop atTop:= Filter.tendsto_atTop_add_const_left _ _ (tendsto_id.const_mul_atTop (Gauge.slopeConstant_pos simple))
  choose! u hD hF using fun i j (h:i∈k j)=> polite J B X.profile X.kernel j ((P i).bag j) hJ (w.L j) (hs.potion _ _ h _ (hl j)).1 (wL j) (hw j)
  let t j:= (w.L j)
  have hQ (i j)(h:i∈k j) (n:ℕ)(hY:n ≤ p i) : ∀ᶠ s in atTop, let R:=(P i).bag j; Caff (G:=G) R (Ship.preHat Z s) (bump (t j).val R.band (Ship.preHat Z s)) (p i) n:=by
     obtain ⟨hs₁,hR,H⟩:= he i j h; let v:= (hp i j h).1
     exact ht.eventually (joys hs₁ _ hR v.bound.large v.bound.band v.credit (hx _) hY)
  have hE i j (h:i∈k j) := hs.potion i j h _ (hl j)|>.1
  have hΩ (i j)(h:i∈k j) := ht.eventually (pedestals (e:=p i) ((P i).bag j).era ((P i).bag j).goal (w.L j) (hE _ _ h).ceiling.1 (hE _ _ h).ceiling.2 (hE _ _ h).credits.1 (hE _ _ h).credits.2)
  have hh (j):= (eventually_all_finset (k j)).2 (fun i hi=> (ht.eventually ((hF i j hi).and (hδ i j hi))).and (((ht.eventually (clearingX (prepared X.kernel) (he _ _ hi).2.2 i)).and ((eventually_all_finset (range (p i+1))).2 (fun n hn=> hQ i j hi n (Nat.lt_succ_iff.mp (mem_range.mp hn))))).and ((late _ Z _ (hs.potion i j hi _ (hl j)).2 simple (by rw [(P i).factor j];linarith only [(P i).huge,Nat.cast_nonneg (α:=ℝ) i])).and (hΩ i j hi))))
  choose t' Ht using fun j=> eventually_atTop.mp (hh j)
  let U': Wait Z:= { V with readyHere:= fun j=>max (V.readyHere j) (t' j) }
  obtain ⟨W,hW,hr,hX⟩:= tabled simple U' k O (fun i j=> (P i).bag j) m (fun i=> (P i).arc) (fun i=> by linarith only [ (P i).huge,Nat.cast_nonneg (α:=ℝ) i]) hm (fun i j=> (P i).factor j) (fun i j hv=> (hp i j hv).1)
  have hg j: V.readyHere j≤W.readyHere j ∧ t' j≤W.readyHere j:= max_le_iff.mp (hr j).1
  refine ⟨W,hL.trans hW,fun j=> (hG j).1.trans (hg j).1,fun j s=>((hG j).2 s).trans ((hr j).2 s),⟨fun C hk K hK=>?_⟩⟩
  filter_upwards [vault_size C.path.levels simple] with a hT
  intro A j hx' hY i hj t'lim hw hz
  let y:= Ship.preHat Z (C.S.scale a); let L:= A.clock; let P':=(P i).bag j; let v:= (P i).patronize C (hm i)
  obtain ⟨⟨hf,hδ⟩,⟨hC,hρ⟩,hAdap,hW⟩ := Ht j _ ((hg j).2.trans hY) i hj
  let β:= (P i).arc; have hwt: ReadyRack O j P' (m i) (trimBench W β):=
    ⟨by rw [show P'.band = β from (P i).factor j]; exact trim_fired O (by
        convert (hX i j hj).1 using 1; exact ((P i).factor j).symm), (hX i j hj).2⟩
  have htrim : (trimBench W β).window j (C.S.scale a) ≤ t'lim := min_le_right ..
  obtain ⟨ho,hP⟩:= affords simple O v _ (trim_paid hk β) hwt hx' (show C.path.levels.clock.J a=j from rfl) (show (trimBench W β).readyHere j≤_ from hY) (htrim.trans hw)
      (fun i hh hk=> hz i (le_trans (Nat.sub_le_sub_left htrim a) hh) hk)
  have h : y=clim A a:= by unfold y Ship.preHat; change _=Calendar.hatBeta _ _; rw [Calendar.hatBeta,hk.bar]
  have hG': Paint.TableReady C a (-3) (load P'.era) P'.era.coast.a := ho.cost.pane
  have hy : Metering v O a (-3):=ho; have hf':Launch C a P' (-3) (m i):= ho.cost
  have hl' : ShowHours J K P' a (-3) (wL j) (d i j):=by
    refine ⟨?_,hP,hT _ ho.cost.coup,?_,?_⟩
    · unfold Ceremony; rw [hK, show C.path.levels.clock.J a=j from rfl, show C.path.levels.clock.kernel=_ from hk.kernel, show C.path.levels.clock.stage=_ from hk.stage, show C.path.levels.clock.factor=_ from hk.lengths]; exact h ▸ (Pump.proclaimed B X hδ.onRoad hf)
    · intro s hs hX'; have hi := hf'.coup
      have hr : C.path.levels.clock.J s=j:= hi.heft.plateau s hX' hs
      have hD : C.path.levels.params s=X.profile j:= by change A.clock.stage (C.path.levels.clock.J s)=_; rw [show A.clock.stage=_ from hk.stage,hr]
      have hw:= hi.court s hX' hs
      unfold Paint.TableReady; rw [hD]
      have hp:SlotPrice P' (m i) G (X.profile j) (w.L j) (clim A a):= h ▸ (hX i j hj).2 _ hY
      exact hp.dating _ hw
    · unfold Levels.params Calendar.params; rw [show C.path.levels.clock.J _ = j from rfl, show C.path.levels.clock.stage=_ from hk.stage, show C.path.levels.clock.factor=_ from hk.lengths]; exact h ▸ hAdap
  have hv:= hV j i hj
  have hprior : Paid V C.path.levels:=retains_budget
      (show V.minLength≤ W.minLength from ‹U'.minLength≤W.minLength›)
      (fun j=> ⟨(hg j).1,(hr j).2⟩) hk
  have he1: Charge A P'.band a (p i) O P'.era:=by
    rw [show P'.band=β from (P i).factor j]; let s:= C.S.scale a
    have hw' : (trimBench V β).window j s ≤ t'lim:= min_le_right ..
    exact held_at (trimBench V β) A (trim_paid hprior β) hx' rfl ((hg j).1.trans hY) (hw'.trans hw)
      (fun i hh hk=> hz i (le_trans (Nat.sub_le_sub_left hw' a) hh) hk) O (p i) β P'.era (trim_fired O hv) simple
  have ht : wheel A a=(w.L j).val:=by unfold wheel; rw [hk.lengths]
  refine ⟨_,_,hf', he1,hl',?_,?_,?_,?_⟩
  · constructor; change Timing (initials K.prices A.clock.stage A.clock.kernel _ _) J _ _ P' _ _ _
    rw [hK, show A.clock.J a=j from rfl,hk.stage,hk.kernel,hk.lengths]; exact h ▸ hδ
  · change Eark (prepared A.clock.kernel) (p i) j i P'.taylor P'.band (wheel A a) (clim A a)
    rw [show P'.band= _ from (P i).factor j, show P'.taylor=_ from (P i).stable j,hk.kernel, ht,←h]; exact hC
  · intro n hn; change Caff P' (clim A a) (a - middle A P'.band a) (p i) n; rw [he1.allot.permitted.full,height,ht,← h,show A.clock.hatBeta a=y from h.symm]; exact hρ n (mem_range.mpr (Nat.lt_succ_iff.mpr hn))
  intro n hn; rw [show C.path.levels.clock.factor = _ from hk.lengths,←h]; exact hW n hn
end Exact

-- expose W shifts from same P.age; transportability with arbitrary further delay.Monetized M. K Legacy.Within Width bounds.
variable {ι:Type}[Fintype ι] {p m:ℕ→ℕ} {μ:ℕ→ℝ} {k P}
lemma rg12_y_tour (h: G.Simple)(he:Fortified (ι:=ι) X B p P k m) (H:∀ d,0≤μ d)(hx:∀ d,2 ≤ p d)(ht:∀ i,m i ≤ (w.L i).val) (hJ:LocalRatio J) (U:Wait Z) :∃ W:Wait Z, ∃ P':∀ d,ι → Tapes.Panel d,U.minLength ≤ W.minLength ∧ U.readyHere ≤ W.readyHere ∧ U.window ≤ W.window ∧ (∀ d i,(P d i).arc=(P' d i).arc) ∧
    (∀ d i j,(P' d i).θ= (P' d j).θ ∧ ∀ k:ℕ, ((P' d i).bag k).era.coast.Q=((P' d j).bag k).era.coast.Q) ∧ ∀ χ, RG12Clock B O J W (fun d=> P' d χ) μ p k:=by
   choose W hv hw v z hV Ht hz hp using fun χ:ι=> retailers _ J (he.shops χ) ht (fun _=>1) (fun _ _=>1) (fun _ _=> zero_lt_one) hJ
   let P' := fun d χ=> curtain (P d χ) (v χ d) (hV χ d)
   have hh(χ) : PreStand X B (fun d=>P' d χ) k m:= recultivate X B (he.buys χ) (v χ) (hV χ) (hz χ)
   have hh' χ i j (hi:i∈ k j): Coul ((P' i χ).bag j) (p i) ∧ HLane ((P' i χ).bag j) (p i) (w.L j) ∧ reserveX (prepared X.kernel) (p i) j (P' i χ).θ (P' i χ).arc (w.L j).val:=by
      obtain ⟨⟨h1,h2,h3,h4⟩,⟨h5⟩,h6⟩:=he.lifts χ i j hi (w.L j) (ht j); exact ⟨⟨h1,h2,h3,h4⟩,⟨h5⟩,h6⟩
   have hyp (S:Finset ι) :∃ U':Wait Z, U.minLength ≤ U'.minLength∧ U.readyHere ≤ U'.readyHere ∧ U.window ≤ U'.window ∧ ∀ χ∈ S,RG12Clock B O J U' (fun d=> P' d χ) μ p k:=by
      induction S using Finset.induction with
      | empty=> exact ⟨U,le_rfl,le_rfl,le_rfl,by simp⟩
      | insert i S hi IH =>
        obtain ⟨Y,h1,h2,h3,h4⟩:= IH; obtain ⟨U',ha,hb,hc,hd⟩:= rg12_glide B O J (z i) (W i) μ p H hx h (hw i) hJ (hh i) ht (hh' i) (hp i) Y
        refine ⟨U',h1.trans ha,h2.trans hb,h3.trans hc,fun χ hi=> ?_⟩; rcases mem_insert.mp hi with rfl|hi; exact hd; exact rg12_print B O J (h4 χ hi) U' ha hb hc
   obtain ⟨V,ha,hb,hc,hh⟩:= hyp univ; exact ⟨V,P',ha,hb,hc,fun i j=> rfl,fun d i j=> (he.same d i j),fun i=> hh _ (mem_univ _)⟩

end YM.PhysicalNext.InteractingRank.Soft
