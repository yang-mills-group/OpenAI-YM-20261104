import YM.Integration.WilsonPhysicalWeakWallStaff
import YM.Integration.WilsonThermometerOrdinaryPanels
import YM.SignedWilsonExpansion.Homes.AttachP
import YM.SignedWilsonExpansion.Homes.Universal
/-! Full ticket election at fixed period. Proof of WeakWallStaff with additional track. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalWeakWallStaff
open Function Set Filter Table Spec Climb Spin Trace Trace.Pilot Next.UVStress
open MergeProof.East Next.Rank Next.Rank.East Maxwell PhysMS PhysMS.Frame
open scoped Topology ContDiff Classical BigOperators

open WilsonPositionThermometerOrientedStation WilsonPositionThermometerCapStation
open WilsonPhysicalWeakWheelOffers
open SignedWilsonExpansion.Homes
variable {G : Gauge} (R:PhysicalNext.Repeat.Legato.Run G) {f : Extraction.Order} {S : Table R.family.book}
    {Y : Ultrafilter (ℕ × ℕ)} {arch : Trace.Terrace.Arch R.family}
    (h : G.Simple) (F : Final R.family f S) (H : (Bel R.family.book).Hierarchy)
    (hZ : Bliss F Y arch H) {c : ℕ} {I : Type} [Fintype I]
    (d : I → Fin (c+1)) (u : ∀ i, (Bel R.family.book).Field (d i))

local notation "C"=> R.family

open YM PhysicalNext PhysicalNext.Repeat.Legato FullVolume
open Integration.WilsonLimitConstruction
include hZ

theorem windowsPV (m:ℕ) (trackP:(track f).Ordered R.family S) (hT:FullVolume.PositionsUV R.family Extraction.Sequence.full)
     (budget:R2I.RG05Joint.AcrossPanels R.kit):∀ᶠ r in trail,∃w:Seats C S c, w.room.station.checked (track f) H w.room.horizon ∧ Booked (Y:=Y) h F H d u w r m:=by
   obtain ⟨K,O,z,-,fee,hξ,-⟩:=WilsonThermometerOrdinaryPanels.original R budget
   by_contra hd
   obtain ⟨s,hs,hS⟩ := contradictionTrail _ hd
   obtain ⟨v,hv,X,hX,V,hV,hB⟩ := Escort.picksPV F K R.makes O _ hZ trackP (whole hT F.room.generic)
      h (R.again h).1.scrim fee hξ s (hs.mono_right nhdsWithin_le_nhds) (fun i => (hS i).1)
   obtain ⟨A,hA,hT,hα,h₁⟩ := survey h F H X hB
   obtain ⟨Y₀,book⟩:=hB.meters
   have he (m:ℕ): ∀ᶠ i in atTop, Staff (Y:=Y) h F H (X.r i) (A i) m:=by
      have he'(n:Fin (m+1))(d:Fin n→Fin (m+1))(w:∀ i,PegC C (d i))(j: Fin (m+1)):= Metric.tendstoUniformlyOn_iff.mp (path_lead F H X hB hA n _ (fun i=> PoleC C (d i) (w i)) j (Scaling.window (sizeHint m) n) (window_closed ..) (fun x hx=>spaced_conf (cost_pos _) hx.1)) _ (cost_pos m)
      filter_upwards [hT,eventually_all.mpr (fun i:Fin (m+1)=>hα i), eventually_all.mpr (fun e:Fin (m+1)=> eventually_all.mpr fun d:Fin (e.val+1)=> h₁ _ _ (Nat.le_of_lt_succ d.isLt)),eventually_all.mpr fun i=> eventually_all.mpr fun d=> eventually_all.mpr fun w=> eventually_all.mpr (he' i d w)] with k hv he h₁ ht
      exact ⟨hv,he,h₁,fun n d v j x hx=> ( (dist_eq_norm ..).symm.trans (dist_comm ..)).trans_le ((ht n d v j x hx).le)⟩
   have oriented (j : ℕ) (i : I) :
       ∀ᶠ k in atTop, ‖(X.U k (d i)).symm (A k (d i) (u i)) - u i‖ ≤ costHint j := by
     filter_upwards [Metric.tendsto_nhds.mp (hA (d i) (u i)) _ (cost_pos j)] with k hki
     exact (dist_eq_norm ..).symm.trans_le hki.le
   have seats:=eventually_all.mpr fun n:Fin (c+1)=>book.terminal n
   have rights:=eventually_all.mpr fun n:Fin (c+1)=>hB.monorail.units n
   have usable:=WilsonPhysicalWeakWheelOffers.along F h hZ hB c
   have joint:=((eventually_all.mpr (fun j:Fin (m+1)=>he j)).and
     (usable.and ((book.growth.eventually_ge_atTop m).and (seats.and
       (rights.and ((he c).and (eventually_all.mpr (fun j:Fin (m+1)=>
         eventually_all.mpr (fun i:I=>oriented j i)))))))))
   obtain ⟨k,staff,⟨cap,offer⟩,cofinal,lookup,coherent,capstaff,nearby⟩:=joint.exists
   let ix (n:Fin (c+1)):Fin (k+1):=⟨n.val,Nat.lt_succ_of_le ((Nat.le_of_lt_succ n.isLt).trans cap)⟩
   obtain ⟨L,hL⟩:=WilsonPhysicalWeakWheelOffers.lift (V k) (book.season k).1 hZ.lies
   let B:Group C c:=⟨k,cap,V k,L,fun n=>(A k n).trans (X.U k n).symm⟩
   have captured(n:Fin (c+1)):L (ix n)=Y₀ n k:=by
     have tag:n.val≤k:=(Nat.le_of_lt_succ n.isLt).trans cap
     have prior:=tendsto_pi_nhds.mp hL (ix n)
     have later:Tendsto (fun z=>(V k).wheel.atCut z (ix n)) (Y:Filter _) (𝓝 (Y₀ n k)):=by
       have agree:Trace.Terrace.heightV V k n=(fun z=>(V k).wheel.atCut z (ix n)):=by
         funext z
         simp only [Trace.Terrace.heightV,dif_pos tag,ix]
       rw [←agree]
       exact (lookup n).1
     exact tendsto_nhds_unique prior later
   have lands (n:Fin (c+1)):∀x,A k n x=S.project n (L (ix n) (B.change n x)):=by
     rw [captured n]
     intro x
     simpa [B] using (lookup n).2 ((X.U k n).symm (A k n x))
   have paired (n : Fin (c+1)) : Coherent H.spin H.spin n (B.change n) ∧
        B.change n ((Bel (C).book).unit n)=(Bel (C).book).unit n := by
     have p := capstaff.spins n
     have a := obedient_realH F h H p
     have b := flips (coherent n).1
     constructor
     · constructor
       · intro x
         exact (congrArg (X.U k n).symm (a.2 x)).trans (b.stars _)
       · intro i x
         exact (congrArg (X.U k n).symm (a.1 i x)).trans (b.signed _ _)
     · change (X.U k n).symm (A k n ((Bel (C).book).unit n)) = _
       rw [p.unit,← (coherent n).2, LinearEquiv.symm_apply_apply]
   apply (hS (v k)).2
   have radius:X.r k=s (v k):=congr_fun hX k
   rw [←radius]
   refine ⟨⟨A k,B,fun n=>X.U k n⟩,hV k,offer,fun _=>rfl,fun j hj=>?_⟩
   exact ⟨staff ⟨j,Nat.lt_succ_of_le hj⟩,hj.trans cofinal,(book.season k).1,(book.season k).2,hL,
     fun n=>⟨(paired n).1,(paired n).2,lands n⟩,fun i=>nearby ⟨j,Nat.lt_succ_of_le hj⟩ i⟩

end YM.Integration.WilsonPhysicalWeakWallStaff
