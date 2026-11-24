import YM.OPE.Compatible.Slope.Tame
/-!
# Fold_pay identity. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Lattice Laurent Filter MeasureTheory RG Finset Next.Free Precision Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical
variable {r k j n d m:ℕ}{x:ℝ}{P:Flight j k}
variable {p:Bin r→ℝ}{U:ℝ}(h: Sack (poise m) p U)
variable (u:4 ≤ k)(hv:0<x)
local notation "Y"=>fun _ : Fin r=> linesOf P x
local notation "L"=> ((P.L.val:ℝ)⁻¹)
include u hv
lemma parcel_me (a b: Fin r→Axis) : Alive (parcelK Y a b 0 0):=by
   obtain ⟨σ,C,hσ,hC,hB⟩:= horns x hv _ _ P.legal u; intro n
   exact ⟨_, parcel_budget0 n 0 a b _ (fun _=>by simp [size]) hσ hC.le (hB P) P.odd⟩
lemma total_me (a b:Fin r→Axis) : ∑' x:Bin r, parcelK Y a b 0 0 x= if a=b then (L)^r else 0:=by
    let f(i:Fin r):= fling (linesOf P x) (a i) (b i) 0; have hf(i) : Summable (f i) := ((overall (stored P x hv u) (a i) (b i) 0 0).choose_spec).water (poise_one 0)
    have hx(i): (∑' j,f i j)= if a i=b i then L else 0:=by unfold f fling; simp only [zero_cellar,sub_zero]; exact origin_money x hv P u 0 _ _
    change ∑' i:Bin r, weave f i=_; rw [(arrayRead f hf).tsum_eq]; simp_rw [hx]; split
    next h=>subst b; simp
    next h=>
       obtain ⟨j,hj⟩ : ∃ i,a i≠b i:= not_forall.mp (fun h' => h (funext h')); exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)
include h
-- controls shift reading from actual fine
lemma courier_tx (a b:Fin r→ Axis)(c:Fin r→Cover)(hc:∀ i:Fin r,size (c i)≤4*P.L.val)(l:List (Keys r))(hl:l.length≤m) :
    well (courier (parcelK Y a b c) p) (tasting l)=∑' z:Bin r,p z* well (parcelK Y a b c z) (tasting l) :=by
       let T:= parcelK Y a b c
       obtain ⟨σ,B,hσ,hB,hP⟩:=horns x hv _ _ P.legal u
       have he := Sack.carried h (fun i=>parcel_budget0 m i a b c hc hσ hB.le (hP P) P.odd) (by
          have hz:= widthCost_ge hσ m; have hs:0≤ widthCost σ m:=zero_le_one.trans hz
          unfold shrill; positivity)
       let f z y:= p z*T z y*tasting l (translit y)
       have hk(z:Bin r): Summable fun y:Bin r=> tasting l (translit y)*T z y:=by
          have hm:= gardens (flavor_part l m hl) (parcel_budget0 m z a b c hc hσ hB.le (hP P) P.odd); simpa [mul_comm] using! hm
       obtain ⟨U,hU,H⟩:= tasting_cost (flavor_part l m hl)
       let g(x:Bin r×Bin r):= ‖p x.1*T x.1 x.2‖ * poise m x.2
       have hg: Summable g:= he.2.1.congr fun j=> by change poise m j.2*‖p j.1*T j.1 j.2‖=_; exact mul_comm ..
       have hh: Summable (Function.uncurry f):= by
          apply (hg.mul_left U).of_norm_bounded; intro j; dsimp only [uncurry,f]; rw [norm_mul]; apply (mul_le_mul_of_nonneg_left (H _) (norm_nonneg _)).trans_eq; unfold g; ring
       calc
          _ = ∑' y,∑' z:Bin r,f z y:=by unfold well courier; refine tsum_congr fun z=> ?_; rw [← tsum_mul_right]; rfl
          _ = ∑' z, ∑' y:Bin r,f z y:= hh.tsum_comm
          _ = _:= tsum_congr fun z=> by unfold f well; simp_rw [mul_assoc]; rw [tsum_mul_left]
lemma stock_stamp (a b:Fin r→ Axis)(c:Fin r→Cover)(hc:∀ i:Fin r,size (c i)≤4*P.L.val) (l:List (Keys r))(hx:l.length < j)(hl:l.length≤m)(ha:purewell p l.length):
   well (courier (parcelK Y a b c) p) (tasting l)= (if a=b then L^(r+l.length) else 0)*well p (tasting l):=by
      rw [courier_tx h u hv a b c hc l hl]
      let f:=parcelK Y a b 0 0; let w:= L • translit (lace r c); obtain ⟨q,hq,hZ,hu⟩:= tame f l L w (parcel_me u hv a b)
      let W:= (L^l.length*(∑' i,f i)); let g i:= tasting l (translit i)
      have he(i:Bin r): well (parcelK Y a b c i) (tasting l)= W*g i+q (translit i):= by
          rw [transmute (P:=P) u hv hx, wedge_input,smul_add]; simp_rw [add_assoc]; exact hu _
      simp_rw [he,mul_add]; rw [Summable.tsum_add]; swap
      · have hx:= gardens (flavor_part l m hl) h; apply (hx.mul_left W).congr (fun i=>?_); unfold g; ring
      swap; · exact gardens (flavor_up (Nat.le_trans (Nat.sub_le ..) hl) hq) h
      have hq: well p q =0:= by
         by_cases hh:l=[]
         · rw [hZ hh]; simp [well]
         exact wells ha hq (by have hz : 0<l.length:= List.length_pos_iff.mpr hh; omega) ((Nat.sub_le ..).trans hl) h
      have hn: (∑' i,p i*q (translit i))=0:= hq; rw [hn,add_zero,show (∑' i,p i* (W*g i))=W*∑' i,p i*g i by simp_rw [mul_left_comm (p _) W, tsum_mul_left]]
      unfold W; rw [show ∑' i,f i=_ from total_me (P:=P) u hv _ _]; split_ifs; · rw [pow_add,mul_comm (L^l.length)]; rfl
      simp
end YM.OPE.Flume
