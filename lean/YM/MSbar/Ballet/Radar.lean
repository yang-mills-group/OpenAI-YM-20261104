import YM.MSbar.Ballet.Trellis
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Ballet
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure Matrix
open Precision Gauge Midpoint Rolling Tramp Exterior Tree Wilson Laurent Bloch Wave Parma Tin Bronze Asymptotics Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Alto Mosaic Mosaic.Issue
variable {G:Gauge}
open Supply Input
variable {O:ChartRatio G}{K:MapPrices}{B:Sheet G}{D:Rolls B}{Θ:Protection D}{Y0:Delays Θ}{W:Bar Y0}{I:Wait W}{P:PostCost D}(A:Directed G I O K P)
open Heath
variable (k p m s:ℕ)(hp:p+2 ≤ m)
variable {φ:Filter ℕ}[φ.NeBot]{X t:ℕ→ℝ}(hX:Tendsto X φ atTop)(ht:Run φ X t (-(1/2)))
    (hw:∀ᶠ i in φ, 0 < t i)
include hp hX ht hw
lemma grown : ∀ᶠ i in φ, ∀ g:Side, Ticket (X i) g (starP (t i) p (widthV G g)) s p m:=by
    let N:=m+1; obtain ⟨K,hK⟩:= paint_supply G N; let B:=quotation G K N; let v x:=vol (X x); have hR:Run φ X v 0:= by unfold v Mosaic.vol; simp_rw [div_eq_mul_inv]; exact Run.mulY hX (Run.stanza hX) _
    have hpB:0≤ B:=(guns (Classical.arbitrary (Face (Per (⟨1,by decide⟩:Side)))) hK 0 (norm_zero|>.trans_lt zero_lt_one)).nonneg -- implicit.Inh?
    let N0:=cities (Fintype.card PlaqAxes) 4; let M0:=cities (tintCost G) 4; let Q(i):= t i^(p+1)*(B*v i^(p+3)); let D(j i):=(v i)^(j+1)*((N0:ℝ)*rugL 1 (Q i) s 4 j M0)
    have hP(j):∀ᶠ i in φ,D j i≤ goalP (X i) p:=by
          have hq: Run φ X Q (epsW p):= (ht.tr hX).Yrat hX ((hR.Ypow hX _).mulK hX _); have hS: Run φ X (D j) (epsW p):=by unfold D rugL; exact (hR.Ypow hX _).Ycost hX (((hq.mulY hX _).mulK hX _).mulK hX _)
          exact (hS (pawn p) (mp0 p|>.2.1)).mono fun i hi=> (le_abs_self _).trans hi
    let v0:=range (m+1); have hf:Tendsto v φ atTop:=by unfold v Mosaic.vol; simp_rw [div_eq_mul_inv]; exact (Alto.broad.comp hX).atTop_mul_const (r:=_) (by norm_num)
    have hy:= (ht.Yrat hX hR).bouquet hX (by norm_num)
    filter_upwards [v0.eventually_all.mpr fun j _=> hP j,hw,hf.eventually_ge_atTop 1, (ht.bouquet hX (by norm_num)).eventually (ge_mem_nhds zero_lt_one), hy.eventually (eventually_lt_nhds zero_lt_one), (Geneva.ray hX).eventually (ge_mem_nhds zero_lt_one)] with i hf ht hv hr hs hz g; let F:=sitePrice G g
    have hg:widthV G g=fun x=> ∑ i,F i x:=rfl; have hp: p+3 ≤ N:=by unfold N; omega
    have hw:= fun (j:Face (Per g)) (x:Positions (Primary g G)) hx=>guns j hK x hx; have hh:0≤αm (X i):= zpow_nonneg (sq_nonneg _) _
    refine ⟨⟨fun j hj=>?_⟩,?_⟩
    · have hJ:= riches (U:=s) (Prod.fst:Face (Per g)→ Site g) F hg hv ht hr hs hp hpB hw (fun j=>lawn j G) hh hz (powerP g PlaqAxes) (starM G g) j (by omega : j < N); have he:D j i≤ goalP (X i) p:=hf j (mem_range.mpr (by omega)); split; exact JetTab.cast hJ he (Set.singleton_subset_iff.mpr (Metric.mem_closedBall_self (zero_le_one.trans hv))); exact JetTab.cast hJ he Set.Subset.rfl
    rw [spray F hg hv ht hr hs hp hpB hw]; exact fun x hx=> ContDiffAt.sum fun j _=> (scores F hv ht hr hs hp hpB hw x hx [] (by simp) j).2
end YM.MSbar.Ballet
