import YM.Integration.WilsonNeutralPointWeakTransfer
import YM.FormalBulk08.Elm.Twig

/-! Downward summation of the true unaveraged weak estimates at all ultraviolet
cutoffs and their actual grade/slot/valence/test orders. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNeutralPointWeakYears
open FormalBulk08 Matrix Laurent Precision Exterior PowerSeries Lattice RG Wilson Tree Stationary
open Push.Uniform Bloch Reef Jets Orb Wick Flat Next.Free UVExtension.Free
open Function Filter Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove
open Quire Palm Grail Chapel Borough Sable Tundra Aster Clover Series Work.F03 Work.F05 Work.F08
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{d D E e r u:ℕ}{X I:Type}{o:Loc G 1}{F:Frame G d}
variable {P:Page X}{C:Pin P}{τ:Time X}{s:Time I}

private theorem lift {g:X→I}{T:I→Studio D→Tile (edgeL G) r}
    (fee:Soft τ (fun i=>s.day (g i)))(h:Sigh u s o (fun _=>1) T):
    Sigh u τ o (fun _=>1) (fun i p=>T (g i) p):=by
  obtain ⟨A,w,b,pay⟩:=h
  exact ⟨_,town_fold (g:=g) fee w,fun i=>b _,fun i p=>pay (g i) p⟩

private theorem dates {T:Deck C→Studio D→Tile (edgeL G) r}(years:Years P)
    (edge:Sugar o (tide C) u (Turn.rad (1/2:ℝ)) (fun _=>1) r (fun i=>T i.ups) (fun i=>T i.bed))
    (born:Sigh u ((sage C).reach (peak C)) o (fun _=>1) (fun i=>T (peak C i))):
    Sigh u (sage C) o (fun _=>1) T:=by
  let f(x:Deck C)(b:ℝ):Prop:=∀p,Knoxville (grain (fame _) 1) u (0,o) (T x p) (b*‖p‖)
  obtain ⟨A,hA,apos,pay⟩:=edge
  obtain ⟨B,hB,bpos,fine⟩:=born
  have top (i:X):f (peak C i) (B i):=fun p=>by simpa only [one_mul] using fine i p
  have next (i:Turn C)(b:ℝ)(h:f i.ups b)(p:0≤b): f i.bed (Turn.rad (1/2:ℝ) i*b+A i):=
    fun v=>by simpa only [mul_one] using pay i b p h v
  obtain ⟨b,rent,nonneg,issued⟩:=upward (f:=f) years (show 0<(1/2:ℝ) by norm_num)
    (fun i a h b cost test=>(h test).mono (mul_le_mul_of_nonneg_right cost (norm_nonneg _))) hB top hA next
  exact ⟨_,rent,nonneg,fun i p=>by simpa only [one_mul] using issued i p⟩

theorem bare (F:Frame G d)(Y:SectionData F)(depth:d+1≤D)(v:Letter F)(he:e≤E)(o:Loc G 1)
    (τ:Time X)(r u:ℕ):Sigh u τ o (fun _=>1) (fun _ p=>sectionY Y depth v p e r):=by
  obtain ⟨b,hb,paid⟩:=sectionQual F Y depth v o E 1 e he r
  refine ⟨fun _=>sack u 1*b,soft_coin τ _,fun _=>mul_nonneg (sack_pos _ zero_lt_one) hb,fun _ p=>?_⟩
  simpa only [one_mul,mul_assoc] using sack_to u zero_lt_one (ε:=1) le_rfl (paid p)

variable (C)
def Row (o:Loc G 1)(F:Frame G d)(u:ℕ)(Y:Deck C→Plaza F D)(v:Letter F)(j k:ℕ):Prop:=
  Sigh u (sage C) o (fun _=>1) (fun i p=>Y i v p j k)

def Edges (o:Loc G 1)(F:Frame G d)(E u:ℕ)(Y:Deck C→Plaza F D)(M:Turn C→Tilework F):Prop:=
  ∀(v:Letter F)(e r:ℕ), e≤E → r ≤ e+slots F v→
  (∀j k,precede e r j k→Wayfarer (fun i:Turn C=>Y i.ups v) j k u (tide C) o (fun _=>1))→
  (∀y j k,itinerary F v e r y j k→
     Sigh u (tide C) o (fun _=>1) (fun i p=>Y i.bed y p j k))→
  Sugar o (tide C) u (Turn.rad (1/2:ℝ)) (fun _=>1) r (fun i p=>Y i.ups v p e r) (fun i p=>Y i.bed v p e r) ∧
  ∀j y,j<e ∨ j=e∧r ≤ slots F y→Faint (tide C) (fun _=>1) (fun i=>coeff j (M i y v))

theorem original (years:Years P)(F:Frame G d)(Y:Deck C→Plaza F D)(M:Turn C→Tilework F)
    (hv:∀i,Court o F (Y i))(bought:Edges C o F E u Y M)
    (top:∀v e,e≤E→∀r,Sigh u ((sage C).reach (peak C)) o (fun _=>1) (fun i p=>Y (peak C i) v p e r)):
    (∀v e,e≤E→∀r,Row C o F u Y v e r) ∧
    ∀v y j,j≤E→Soft (tide C) (fun i=>coeff j (M i y v)):=by
  have silent (v:Letter F)(e r:ℕ)(h:e+slots F v<r):Row C o F u Y v e r:=by
    have z (i:Deck C)(p:Studio D):Y i v p e r=0:=by
      apply Classical.byContradiction;intro live
      exact (not_lt.mpr (((hv i).officers v).fare.1 p e r live)) (by simpa only [Nat.add_comm] using h)
    unfold Row Sigh Whey
    simp_rw [z]
    exact bear_void ..
  have every : ∀v e r,e≤E → r ≤ e+slots F v→Row C o F u Y v e r:=by
    apply Elm.avenues F E
    intro v e r he hr past
    have earlier (y:Letter F)(j k:ℕ)(hi:itinerary F v e r y j k):Row C o F u Y y j k:=by
      by_cases h:k≤j+slots F y
      · exact past y j k hi h
      exact silent y j k (Nat.lt_of_not_ge h)
    exact dates years (bought v e r he hr
      (fun j k h=>lift (g:=Turn.ups) (up_age C years) (earlier v j k (offhand v h)))
      (fun y j k h=>lift (g:=Turn.bed) (down_age C) (earlier y j k h))).1 (top v e he r)
  have allRows (v:Letter F)(e:ℕ)(he:e≤E)(r:ℕ):Row C o F u Y v e r:=by
    by_cases h:r≤e+slots F v
    · exact every v e r he h
    exact silent v e r (Nat.lt_of_not_ge h)
  refine ⟨allRows,fun v y j hj=>?_⟩
  have cap (x:Letter F)(k l:ℕ)(h:itinerary F v j 0 x k l):Row C o F u Y x k l:=by
    apply allRows
    rcases h with h|⟨rfl,_⟩
    · exact h.le.trans hj
    exact hj
  have f:=(bought v j 0 hj (Nat.zero_le _)
    (fun k r h=>lift (g:=Turn.ups) (up_age C years) (cap v k r (offhand v h)))
    (fun x k r h=>lift (g:=Turn.bed) (down_age C) (cap x k r h))).2 j y (Or.inr ⟨rfl,Nat.zero_le _⟩)
  exact f.pact (fun _=>le_rfl)

end YM.Integration.WilsonNeutralPointWeakYears
end
