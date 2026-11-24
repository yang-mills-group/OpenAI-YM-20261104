import YM.OPE.Compatible.Slope.Price
/-!
# Trans stamp reroute itself with loss-free wells
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Lattice Laurent Filter MeasureTheory RG Finset Next.Free Bloch Precision Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical
variable {I J:Type*} {r k j n d m:ℕ}{x U V:ℝ}{P:Flight j k}
lemma wellsSet [Fintype I] (p:J→ Shift I→ℝ)(s:Finset J)(a:Lieu I→ℝ)(hp:a∈Flavor I d)(h:∀ j∈s,∃ U, Sack (poise d) (p j) U): well (∑ j∈s,p j) a=∑ j∈s,well (p j) a:=by unfold well; simp_rw [Finset.sum_apply,sum_mul]; refine Summable.tsum_finsetSum fun i hi=> gardens hp (h i hi).choose_spec
-- variants D only
local notation "P!"=> P.L
local notation "L"=> ((P.L.val:ℝ)⁻¹)
local notation "Y"=>linesOf P x
lemma pilgrim_well (i:Bin r→ℝ)(hi: Sack (poise m) i U) (l:List (Keys r))(hc:l.length≤m)(he:l.length<j)(hv:0<x)(hk:4 ≤ k)(a b: Fin (r+1)→Axis)(h:purewell i l.length):
   well (pilgrim P a b x i) (tasting l)= (P.L.val:ℝ)^4 * (if a=b then L^(r+1+l.length) else 0)*well i (tasting l):=by
   let f (j:Site P.L):= courier (parcelK (fun _=>linesOf P x) a b (fun _=>lift j)) (upland i)
   obtain ⟨η,Q,hη,hQ,H⟩:= horns x hv _ _ P.legal hk
   let L':ℝ := P.L.val
   have hp(j):∃ ξ, Sack (poise m) (f j) ξ:=by
      let N:= shrill (r+1) m η Q / L'^(r+1); have hh: 0 ≤ N:=by
          unfold N shrill L'; have he:= widthCost_ge hη m; have hx:0≤widthCost η m:= zero_le_one.trans he; positivity
      have hz:= Sack.carried (upland_bill hi) (fun v=> parcel_budget0 m v a b (fun _=> lift j) (fun _=> lift_charge j) hη hQ.le (H P) P.odd) hh
      exact ⟨_, hz.draw (poise_one m)⟩
   choose ξ hξ using hp
   let t:= (if a=b then L^(r+1+l.length) else 0)
   have hg(j): well (midland (f j)) (tasting l)= t*well i (tasting l):=by
       have hy(w:List (Keys (r+1)))(hg:w.length=l.length) : well (f j) (tasting w)= t*well (upland i) (tasting w):=by
           simpa only [hg] using! stock_stamp (upland_bill hi) hk hv a b (fun _=>lift j) (fun _=>lift_charge j) w (hg.trans_lt he) (hg.trans_le hc) (hg.symm ▸ uplight i h hc hi)
       rw [mid_price (hξ j) l hc, grab_rank hc (hξ j) (upland_bill hi) hy (fall_charm _),← mid_price (upland_bill hi) _ hc, show midland (upland i)=i from funext (upright i)]
   change well (∑ i: Site P.L,midland (f i)) (tasting l)=L'^4*t*_
   rw [wellsSet (d:=m) _ _ _ (flavor_part l m hc) (fun i _=> ⟨_, midland_bill (hξ i)⟩)]; simp only [hg,sum_const,nsmul_eq_mul,card_univ,site_card]; unfold L'; push_cast; ring
end YM.OPE.Flume
