import YM.Integration.WilsonPositionThermometerOrientedStation

/-! A single original Wilson station for the three thermometer horizons:
cap six for the cubic, cap four for both quadratics. Its entire cutoff lift,
signed symmetry and physical unit are retained at every selected cap. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionThermometerCapStation
open Function Set Filter Table Spec Climb Spin Trace Trace.Pilot Next.UVStress
open MergeProof.East Next.Rank Next.Rank.East Maxwell PhysMS PhysMS.Frame
open scoped Topology ContDiff Classical BigOperators

open WilsonPositionThermometerOrientedStation
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    {Y : Ultrafilter (ℕ × ℕ)} {arch : Trace.Terrace.Arch C}
    (h : G.Simple) (F : Final C f S) (H : (Bel C.book).Hierarchy)
    (hZ : Bliss F Y arch H) {c : ℕ} {I : Type} [Fintype I]
    (d : I → Fin (c+1)) (u : ∀ i, (Bel C.book).Field (d i))

structure Group (C : Family G) (c : ℕ) where
  horizon : ℕ
  fits : c ≤ horizon
  station : Vane C horizon
  lift : Lifts C horizon
  change : ∀ j : Fin (c+1), (Bel C.book).Field j ≃ₗ[ℂ] (Bel C.book).Field j

def index (A : Group C c) (j : Fin (c+1)) : Fin (A.horizon+1) :=
  ⟨j.val,Nat.lt_succ_of_le ((Nat.le_of_lt_succ j.isLt).trans A.fits)⟩

def projects (A : Group C c) (P : tower S) (m : ℕ) (r : ℝ) : Prop :=
  m ≤ A.station.k ∧ A.station.checked f H A.horizon ∧ A.station.wheel.r = r ∧
  Tendsto A.station.wheel.atCut (Y : Filter _) (𝓝 A.lift) ∧
  (∀ j : Fin (c+1), Coherent H.spin H.spin j (A.change j) ∧
    A.change j ((Bel C.book).unit j) = (Bel C.book).unit j ∧
    ∀ x, P j x = S.project j (A.lift (index A j) (A.change j x))) ∧
  ∀ i, ‖A.change (d i) (u i)-u i‖ ≤ costHint m

include hZ in
theorem original (m : ℕ) : ∀ᶠ r in trail, ∃ P : tower S, ∃ A : Group C c,
    ∀ j ≤ m, Staff (Y:=Y) h F H r P j ∧ projects (f:=f) (Y:=Y) H d u A P j r := by
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
       ∀ᶠ k in atTop, ‖(X.U k (d i)).symm (A k (d i) (u i)) - u i‖ ≤ costHint j := by
     filter_upwards [Metric.tendsto_nhds.mp (hA (d i) (u i)) _ (cost_pos j)] with k hki
     exact (dist_eq_norm ..).symm.trans_le hki.le
   have seats := eventually_all.mpr (fun i : Fin (c+1) => hrow i)
   have rights := eventually_all.mpr (fun i : Fin (c+1) => hB.monorail.units i)
   have joint := ((eventually_all.mpr (fun j : Fin (m+1) => he j)).and
       ((eventually_ge_atTop c).and ((hk.eventually_ge_atTop m).and (seats.and
          (rights.and ((he c).and (eventually_all.mpr (fun j : Fin (m+1) =>
           eventually_all.mpr (fun i : I => oriented j i)))))))))
   obtain ⟨k,staff,cap,cofinal,lookup,coherent,capstaff,nearby⟩ := joint.exists
   let ix (n : Fin (c+1)) : Fin (k+1) := ⟨n.val,Nat.lt_succ_of_le ((Nat.le_of_lt_succ n.isLt).trans cap)⟩
   obtain ⟨L,hL,hread⟩ := lookup (Fin.last c) (ix (Fin.last c)) rfl
   let B : Group C c := ⟨k,cap,W k,L,fun n => (A k n).trans (X.U k n).symm⟩
   have lands (n : Fin (c+1)) : ∀ x, A k n x=S.project n (L (ix n) (B.change n x)) := by
     obtain ⟨T,Tlim,read⟩ := lookup n (ix n) rfl
     have eq : T = L := tendsto_nhds_unique Tlim hL
     subst T
     intro x
     simpa [B,ix] using read ((X.U k n).symm (A k n x))
   have paired (n : Fin (c+1)) : Coherent H.spin H.spin n (B.change n) ∧
        B.change n ((Bel C.book).unit n)=(Bel C.book).unit n := by
     have p := capstaff.spins n
     have a := obedient_realH F h H p
     have b := flips (coherent n).1
     constructor
     · constructor
       · intro x
         exact (congrArg (X.U k n).symm (a.2 x)).trans (b.stars _)
       · intro i x
         exact (congrArg (X.U k n).symm (a.1 i x)).trans (b.signed _ _)
     · change (X.U k n).symm (A k n ((Bel C.book).unit n)) = _
       rw [p.unit,← (coherent n).2, LinearEquiv.symm_apply_apply]
   apply (hS (v k)).2
   refine ⟨A k,B,fun j hj => ?_⟩
   have radius : X.r k=s (v k) := congr_fun hX k
   rw [← radius]
   exact ⟨staff ⟨j,Nat.lt_succ_of_le hj⟩,hj.trans cofinal,(hw k).1,(hw k).2,hL,
     fun n => ⟨(paired n).1,(paired n).2,lands n⟩,
     fun i => nearby ⟨j,Nat.lt_succ_of_le hj⟩ i⟩

include hZ in
theorem simultaneous : ∃ (P : ℝ → tower S) (A : ℝ → Group C c), ∀ m : ℕ,
    ∀ᶠ r in trail, Staff (Y:=Y) h F H r (P r) m ∧ projects (f:=f) (Y:=Y) H d u (A r) (P r) m r := by
  let B (r : ℝ) (m : ℕ) := {p : tower S × Group C c |
    ∀ j ≤ m, Staff (Y:=Y) h F H r p.1 j ∧ projects (f:=f) (Y:=Y) H d u p.2 p.1 j r}
  have supplied (m : ℕ) : ∀ᶠ r in trail, (B r m).Nonempty :=
    (original h F H hZ d u m).mono fun _ ⟨P,A,hi⟩ => ⟨(P,A),hi⟩
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

end YM.Integration.WilsonPositionThermometerCapStation
end
