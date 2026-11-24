import YM.PhysMS.Frame.Stage
import YM.Integration.WilsonPositionThermometerReading

/-! Retain the original signed field lifts, on their actual extraction station,
when choosing the all-radii Maxwell frame. All occupied and unit slots of the
three-field thermometer can use one grade-six cutoff limit. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionThermometerOrientedStation
open Function Set Filter Table Spec Climb Spin Trace Trace.Pilot Next.UVStress
open MergeProof.East Next.Rank Next.Rank.East Maxwell PhysMS PhysMS.Frame
open scoped Topology ContDiff Classical BigOperators

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable {Y : Ultrafilter (ℕ × ℕ)} (h : G.Simple) (F : Final C f S) (H : (Bel C.book).Hierarchy)
variable {Z : Terrace.Arch C} (hZ : Bliss F Y Z H)
variable {I : Type} [Fintype I] {d : ℕ} (u : I → (Bel C.book).Field d)

structure Filing (C : Family G) (d : ℕ) (I : Type) where
  horizon : ℕ
  level : Fin (horizon+1)
  grade : level.val = d
  station : Vane C horizon
  lift : Lifts C horizon
  vector : I → (Bel C.book).Field d

def Filed (r : ℝ) (P : tower S) (m : ℕ) (A : Filing C d I) : Prop :=
  m ≤ A.station.k ∧ A.station.checked f H A.horizon ∧ A.station.wheel.r = r ∧
    Tendsto A.station.wheel.atCut (Y : Filter _) (𝓝 A.lift) ∧
    ∀ i, P d (u i) = S.project d (A.grade ▸ A.lift A.level (A.grade.symm ▸ A.vector i)) ∧
      ‖A.vector i - u i‖ ≤ costHint m

include hZ in
theorem original (m : ℕ) : ∀ᶠ r in trail, ∃ P : tower S, ∃ A : Filing C d I,
    ∀ j ≤ m, Staff (Y:=Y) h F H r P j ∧ Filed (f:=f) (Y:=Y) H u r P j A := by
   by_contra hd
   obtain ⟨s,hs,hS⟩ := contradictionTrail _ hd
   obtain ⟨v,hv,X,hX,V,hB⟩ := hZ.picks s (hs.mono_right nhdsWithin_le_nhds) (fun i => (hS i).1)
   obtain ⟨A,hA,hT,hα,h₁⟩ := survey h F H X hB
   obtain ⟨W,hk,hw,hrow⟩ := hB.monorail.money
   have he (m:ℕ): ∀ᶠ i in atTop, Staff (Y:=Y) h F H (X.r i) (A i) m:=by
      have he'(n:Fin (m+1))(d:Fin n→Fin (m+1))(w:∀ i,PegC C (d i))(j: Fin (m+1)):= Metric.tendstoUniformlyOn_iff.mp (path_lead F H X hB hA n _ (fun i=> PoleC C (d i) (w i)) j (Scaling.window (sizeHint m) n) (window_closed ..) (fun x hx=>spaced_conf (cost_pos _) hx.1)) _ (cost_pos m)
      filter_upwards [hT,eventually_all.mpr (fun i:Fin (m+1)=>hα i), eventually_all.mpr (fun e:Fin (m+1)=> eventually_all.mpr fun d:Fin (e.val+1)=> h₁ _ _ (Nat.le_of_lt_succ d.isLt)),eventually_all.mpr fun i=> eventually_all.mpr fun d=> eventually_all.mpr fun w=> eventually_all.mpr (he' i d w)] with k hv he h₁ ht
      exact ⟨hv,he,h₁,fun n d v j x hx=> ( (dist_eq_norm ..).symm.trans (dist_comm ..)).trans_le ((ht n d v j x hx).le)⟩
   have oriented (j : ℕ) (i : I) :
       ∀ᶠ k in atTop, ‖(X.U k d).symm (A k d (u i)) - u i‖ ≤ costHint j := by
     filter_upwards [Metric.tendsto_nhds.mp (hA d (u i)) _ (cost_pos j)] with k hki
     exact (dist_eq_norm ..).symm.trans_le hki.le
   obtain ⟨k,staff,indices,cofinal,cutoff,nearby⟩ :=
     ((eventually_all.mpr (fun j : Fin (m+1) => he j)).and
       ((eventually_ge_atTop d).and ((hk.eventually_ge_atTop m).and ((hrow d).and
         (eventually_all.mpr fun j : Fin (m+1) =>
           eventually_all.mpr fun i : I => oriented j i))))).exists
   let idx : Fin (k+1) := ⟨d,Nat.lt_succ_of_le indices⟩
   obtain ⟨L,hL,hread⟩ := cutoff idx rfl
   let B : Filing C d I := ⟨k,idx,rfl,W k,L,fun i => (X.U k d).symm (A k d (u i))⟩
   apply (hS (v k)).2
   refine ⟨A k,B,fun j hj => ?_⟩
   have radius : X.r k = s (v k) := congr_fun hX k
   rw [← radius]
   refine ⟨staff ⟨j,Nat.lt_succ_of_le hj⟩,hj.trans cofinal,(hw k).1,(hw k).2,hL,fun i => ?_⟩
   refine ⟨?_,nearby ⟨j,Nat.lt_succ_of_le hj⟩ i⟩
   simpa [B,idx] using hread ((X.U k d).symm (A k d (u i)))

include hZ in
theorem simultaneous : ∃ (P : ℝ → tower S) (A : ℝ → Filing C d I), ∀ m : ℕ,
    ∀ᶠ r in trail, Staff (Y:=Y) h F H r (P r) m ∧ Filed (f:=f) (Y:=Y) H u r (P r) m (A r) := by
  let B (r : ℝ) (m : ℕ) := {p : tower S × Filing C d I |
    ∀ j ≤ m, Staff (Y:=Y) h F H r p.1 j ∧ Filed (f:=f) (Y:=Y) H u r p.1 j p.2}
  have supplied (m : ℕ) : ∀ᶠ r in trail, (B r m).Nonempty :=
    (original h F H hZ u m).mono fun _ ⟨P,A,hi⟩ => ⟨(P,A),hi⟩
  let M (r : ℝ) := (Finset.range (glen C.S r+1)).filter fun m => (B r m).Nonempty
  have available (r : ℝ) {m} (hm : m ∈ M r) : (B r m).Nonempty := (Finset.mem_filter.mp hm).2
  obtain ⟨r₀,defaultPair,_⟩ := (supplied 0).exists
  let W (r : ℝ) := if h : (M r).Nonempty then (available r (Finset.max'_mem (M r) h)).choose else defaultPair
  refine ⟨fun r => (W r).1,fun r => (W r).2,fun m => ?_⟩
  filter_upwards [supplied m,(glen_leads C.S).eventually_ge_atTop m] with r hr hg
  have hm : m ∈ M r := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hg),hr⟩
  have live : (M r).Nonempty := ⟨m,hm⟩
  dsimp only [W]
  rw [dif_pos live]
  exact (available r (Finset.max'_mem (M r) live)).choose_spec m (Finset.le_max' _ _ hm)

end YM.Integration.WilsonPositionThermometerOrientedStation
end
