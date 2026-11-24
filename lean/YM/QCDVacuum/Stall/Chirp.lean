import YM.QCDVacuum.Stall.FactionFlow
/-!
# Inactive logarithmic marker slots and absent K payloads disappear locally
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lotus
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable {J : Type*} [Fintype J]

namespace Faction
variable (M : Faction S R) (D:R.activities.K=0)
include D
lemma asleep (i:Wing)(h:i.blank R) (hi:i.badge S ∈ p) (he:i.badge S ∉ M.signs) (X : Coat T F)(u:Air f G) : M.premium X W a Ñ (Matter.own p) m u p=0:= by
  unfold premium; split; swap; · rfl
  have hv : X.vertex R Ñ W a (Matter.own p) m u (i.badge S)=0:= by
    rcases i with i|i
    · have he p' : R.activities.regularOccurrence R.p i p'=0:=by
        by_cases hb:Healthy R.p.threshold (R.activities.reg i).support p' <;> simp [Activities.regularOccurrence,hb, show R.activities.E i=0 from h]
      change Real.exp (-R.activities.regularOccurrence R.p i _ * _)-1=0; rw [he,neg_zero,zero_mul,Real.exp_zero,sub_self]
    change R.activities.K i _ * _=0; simp [D]
  rw [show X.term _ _ _ _ _ _ u _=0 from prod_eq_zero (Finset.mem_sdiff.mpr ⟨hi,he⟩) hv,mul_zero]
lemma blossoms_off (i:Wing)(h:i.blank R)(hi:i.badge S∈ p)(he:i.badge S ∉ M.signs)(T:Tube G S)(x:ℝ)(χ:Chi)(K:ℝ)(V:Config G c) : M.lotus T x χ K W a Ñ m V p=0:= by
  have hx {F : Forest S.ratio}(X:Coat T F): M.bloom X W a Ñ m p=0:=by
    have hh (Y:Coat T F)(y:F.Slice G × Air f G): M.into Y W a Ñ (Matter.own p) m p y=0:= M.asleep D i h hi he ..
    unfold bloom steep tithe; split; next=> unfold likely; simp_rw [hh]; simp
    next=>rfl
  unfold lotus likely; simp_rw [hx]; simp
lemma adjusts (U: Config G f) : M.cicada U = if R.activities.admissible R.p U M.gasDue then Real.exp (R.exponent U) * M.ingredients U else 0:=by
  unfold cicada; rw [tsum_eq_single M.gasDue]
  · by_cases h:R.activities.admissible R.p U M.gasDue <;> simp [bun,h,bill]
  intro k hk; unfold bun bill; split_ifs with h h'
  swap; · rfl
  swap; · rfl
  obtain ⟨x,hx,hm⟩:= Finset.exists_of_ssubset (lt_of_le_of_ne h' (Ne.symm hk))
  rw [show (∏ i∈k\ M.gasDue,R.activities.K i U) =0 from prod_eq_zero (Finset.mem_sdiff.mpr ⟨hx,hm⟩) (by simp [D]),mul_zero]
end Faction

def registry (S : StepData c f)(τ:J ↪ Wing) : J ↪ Head S := τ.trans ⟨_,Faction.badged S⟩
def tick (τ:J ↪ Wing)(p:Molecule S): Finset J:= p.preimage (registry S τ) (registry S τ).injective.injOn
omit [Fintype J] in
lemma ticking {J : Type*} [Fintype J] (τ:J ↪ Wing)(p:Molecule S)(i:J): i ∈ tick τ p ↔ (τ i).badge S∈p := Finset.mem_preimage -- test
lemma harvest_keys (τ:J ↪ Wing)(p:Finset (Molecule S)): tick τ (p.biUnion id)=p.biUnion (tick τ):= by ext i; simp only [ticking,mem_biUnion,id_eq]
def pinKeys (S : StepData c f)(τ:J ↪ Wing)(A:Finset J): Finset ℕ:= Matter.own (A.map (registry S τ))
structure Quartet (J:Type*) (S : StepData c f) (R:Rep G f) (τ:J↪Wing) where
  has : J→Blade S R
  reserves i : (has i).turn=τ i
namespace Quartet
variable {τ : J ↪ Wing}(q:Quartet J S R τ)(A:Finset J)
omit [Fintype J] in
lemma singly {J : Type*} [Fintype J] {τ : J ↪ Wing} (q : Quartet J S R τ) : Injective q.has:=fun i j h=> τ.injective ((q.reserves i).symm.trans ((congr_arg Blade.turn h).trans (q.reserves j)))
def seat (A:Finset J): Faction S R:= ⟨A.map ⟨q.has,q.singly⟩, by
  intro i hi j hj h; obtain ⟨i,hi,rfl⟩:= mem_map.mp hi; obtain ⟨j,hj,rfl⟩:= mem_map.mp hj; exact (congr_arg q.has (τ.injective ((q.reserves i).symm.trans (h.trans (q.reserves j)))))⟩
lemma hei : (q.seat A).signs=A.map (registry S τ):= by
  unfold Faction.signs seat; ext i; simp [mem_image,registry,q.reserves]
lemma lock : (q.seat A).gasDue=pinKeys S τ A:=by
  rw [pinKeys,← q.hei,Faction.sign_spell]; simp only [Matter.own,issue,toRight_disjSum,toLeft_disjSum]
lemma ingred (U: Config G f) : (q.seat A).ingredients U= ∏ i∈A,(q.has i).ingredient U:= by simp [Faction.ingredients,seat]
lemma crack (D:R.activities.K=0)(U: Config G f): (q.seat A).cicada U = if R.activities.admissible R.p U (pinKeys S τ A) then Real.exp (R.exponent U)* ∏ i∈A,(q.has i).ingredient U else 0:= by rw [(q.seat A).adjusts D,lock,ingred]
open Greenbelt
lemma anthology (D:R.activities.K=0)(T:Tube G S)(x:ℝ)(χ:Chi)(K:ℝ)(V : Config G c) (Z:Finset (Molecule S)) :
    (q.seat A).blossom T x χ K W a Ñ m V Z = if joints T R m (radiusB x) Z ∧ permitsA x V Z ∧ A=Z.biUnion (tick τ) then
      ∏ j∈Z,(q.seat (tick τ j)).lotus T x χ K W a Ñ m V j else 0:=by
  unfold Faction.blossom; by_cases he:A=Z.biUnion (tick τ)
  · rw [← harvest_keys] at he
    have hp : (q.seat A).signs⊆ Z.biUnion id:=by
      rw [q.hei,he]; intro i hi; obtain ⟨j,hj,rfl⟩:= mem_map.mp hi; exact (ticking ..).1 hj
    split_ifs with hz hu hu
    · apply Finset.prod_congr rfl; intro j hj
      suffices ht:(q.seat A).locate j=q.seat (tick τ j) by rw [ht]
      suffices ht:((q.seat A).locate j).own=(q.seat (tick τ j)).own by
        generalize Ha : (q.seat A).locate j=P at *; generalize Hz:q.seat (tick τ j)=Q at *; cases P; cases Q; congr
      ext p; constructor
      · intro hi; obtain ⟨hi,h⟩:= mem_filter.mp hi; obtain ⟨i,hi,rfl⟩:= mem_map.mp hi; exact mem_map_of_mem _ ((ticking ..).2 (show _ from q.reserves i ▸ (show (q.has i).turn.badge S∈ j from h)))
      intro hi; obtain ⟨i,hI,rfl⟩:=mem_map.mp hi
      have hs := (ticking ..).1 hI
      refine mem_filter.mpr ⟨?_,(?_: (q.has i).turn.badge S∈j)⟩
      · refine mem_map_of_mem _ ?_; rw [he]; exact (ticking ..).2 (mem_biUnion.mpr ⟨j,hj,hs⟩)
      rw [q.reserves]; exact hs
    · exact (hu ⟨hz.1,hz.2.1,he.trans (harvest_keys ..)⟩).elim
    · exact (hz ⟨hu.1,hu.2.1,hp⟩).elim
    · rfl
  have hZ : ¬ (joints T R m (radiusB x) Z ∧ permitsA x V Z ∧ A=Z.biUnion (tick τ)):= fun h=>he h.2.2
  rw [if_neg hZ]
  split; swap; · rfl
  next hp =>
    have hz: A ⊆ Z.biUnion (tick τ):=by
      rw [← harvest_keys]; intro i hi; exact (ticking ..).2 (hp.2.2 (show (registry S τ) i ∈ (q.seat A).signs by rw [q.hei]; exact mem_map_of_mem _ hi))
    obtain ⟨i,hI,hJ⟩:= Finset.exists_of_ssubset (lt_of_le_of_ne hz he)
    obtain ⟨j,hj,h⟩:= mem_biUnion.mp hI; refine Finset.prod_eq_zero (f:=fun i=>((q.seat A).locate i).lotus T x χ K W a Ñ m V i) hj (((q.seat A).locate j).blossoms_off D (τ i) (q.reserves i ▸ (q.has i).blank) ((ticking ..).1 h) ?_ ..)
    rw [(q.seat A).lsign,q.hei]; exact fun hx=> hJ ((Finset.mem_map' (registry S τ)).mp (mem_inter.mp hx).1)
end Quartet
end YM.PhysicalNext.Repeat.Lotus
