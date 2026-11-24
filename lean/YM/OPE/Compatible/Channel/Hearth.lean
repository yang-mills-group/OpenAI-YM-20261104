import YM.OPE.Compatible.Channel.Biome
/-!
# Root flag shunts in costed multivariate operators
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Set Lattice Laurent MeasureTheory RG Finset Next.Free Bloch Precision Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Carrier Work.F08 Matrix Exterior
open scoped Topology BigOperators Classical
variable {r n m j k:ℕ}{L c f:Side}{η U v:ℝ}
namespace Script
open Page
variable {W:Type*}[Fintype W] [DecidableEq W]
lemma upland_sum {I:Type*} (s:Finset I) (x:I→ Bin r→ℝ):upland (∑ i∈s,x i)=∑ i∈s,upland (x i):=by ext1 p; simp only [upland,Finset.sum_apply]; split_ifs; rfl; simp only [Finset.sum_const_zero]
lemma midland_sum {I:Type*} (s:Finset I) (x:I→ Bin (r+1)→ℝ)(h:∀ i∈s,Summable (x i)): midland (∑ i∈s,x i)=∑ i∈s,midland (x i):=by
   ext1 y; simp only [midland,Finset.sum_apply]; rw [Summable.tsum_finsetSum]
   exact fun i hi=> (h i hi).comp_injective (fun u v g=> (Prod.mk.inj ((wreath r).injective g)).1)
lemma lifters {P:Flight j k} {p:Script (Palette W) (r+1)} (hh: p.pinned) (hp:soot m p U)
   (hk:4 ≤ k)(he:0<v)(b:Ink (Palette W) (r+1)): sliceP (payVolume (chrome W (linesOf P v)) p) b =∑ i:Ink (Palette W) (r+1),upland (if ringTone i=ringTone b then pilgrim P (ringList i) (ringList b) v (crop p i) else (0:Bin r→ℝ)) :=by
      let y:= linesOf P v; let E:= chrome W y; let S (i: Site P.L):= countermove E (lift i) p
      let Z(i:Ink (Palette W) (r+1))(a:Site P.L):= courier (parcelK (fun _=>y) (ringList i) (ringList b) (fun _=> lift a)) (upland (crop p i)); let K(i)(a:Site P.L):=if ringTone i=ringTone b then Z i a else 0
      have ht(i:Ink (Palette W) (r+1))(a:Site P.L): Summable (Z i a):=by
         obtain ⟨η,B,hσ,hB,H⟩:= horns v he _ _ P.legal hk; let u:= shrill (r+1) m η B/(P.L.val:ℝ)^(r+1); have hu:0 ≤ u:=by
             have hv:=widthCost_ge hσ m; have ht:0≤widthCost η m:=zero_le_one.trans hv; unfold u shrill; positivity
         have h:= (Sack.carried (upland_bill (crops hp i)) (fun x=> parcel_budget0 m x (ringList i) (ringList b) (fun _=> lift a) (fun _=>lift_charge a) hσ hB.le (H P) P.odd) hu).draw (poise_one m); exact h.water (poise_one m)
      have hs(a:Site P.L): sliceP (S a) b=∑ i,K i a:=by
          rw [show sliceP (S a) b= _ from pay_div _ (stored P v he hk) hp (lift a) b]; exact sum_congr rfl fun i _=> by rw [show sliceP p i=upland (crop p i) from funext fun x=> pin_slots _ _ _ hh]
      have hx(a):sliceP (silt (S a)) b=∑ i,upland (midland (K i a)):=by rw [from_rows,hs,midland_sum,upland_sum]; exact fun i _=> by unfold K; split; exact ht i a; exact summable_zero
      have hz(i): (∑ a,upland (midland (K i a)))=upland (if ringTone i=ringTone b then pilgrim P (ringList i) (ringList b) v (crop p i) else 0 ) := by
           rw [← upland_sum]; apply congr_arg; unfold K; split
           next h=> rfl
           next h=> simp only [show midland (0: Bin (r+1)→ℝ) =0 from funext fun i=>by simp [midland], Finset.sum_const_zero]
      change sliceP (∑ i:Site P.L,silt (S i)) b=_; rw [show sliceP _ _=∑ i:Site P.L, sliceP (silt (S i)) b from funext (fun a=>by simp [sliceP])] -- fill elab
      simp_rw [hx]; rw [Finset.sum_comm]; exact Finset.sum_congr rfl (fun i _=> hz i)
end Script
end YM.OPE.Flume
