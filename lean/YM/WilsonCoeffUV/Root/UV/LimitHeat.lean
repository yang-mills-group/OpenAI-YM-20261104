import YM.WilsonCoeffUV.Root.UV.Limit
/-!
# Puck stage limiting from normalized vacuum at same witness.
Root and costs used after budgets. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{U V α β:Type*}{r h D l e j k a N M m b i q v':ℕ} {G:Gauge}{F:Labels.Frame G h}{H:Hol G}{s t t' A B C x y δ σ γ S O v:ℝ}
variable {E W U' V':Credit}{T:SectionData F}{p:h<D}{θ:ℕ→ℝ}
lemma Fleets.colorado [Fintype α][NormedAddCommGroup U][NormedSpace ℝ U][CompleteSpace U]{P:ℕ→ Layers U (Cloth α)}{A':Layers U (Cloth α)}{Q:ℕ→Layers ℝ (Cloth α)}{B':Layers ℝ (Cloth α)}{G:ℕ→ ropes Cover α α}{K:ropes Cover α α}(h:∀ᶠ n in atTop,Ballast s C (θ n) (G n) K)(u:∀ i≤ m, ∀ j≤ v',∀ r,Fleets θ s (fun n=>P n i j r) (A' i j r))(b:∀ i≤m,∀ j≤ v',∀ r,Cape θ s (fun n=> Q n i j r) (B' i j r))(he:t<s)(hu:0≤t)(k): Fleets θ t (fun n=> Soil.paintC (G n) (Q n) (P n) m v' k) (Soil.paintC K B' A' m v' k):=by
    simp_rw [Soil.paintC,Finset.sum_apply]; apply Fleets.fleetSum; intro i hi; apply Fleets.fleetSum; intro j hj; dsimp only [rondel]; apply Fleets.fleetSum; intro x hx; have hp:= Finset.mem_antidiagonal.mp hi; have ht:= Finset.mem_antidiagonal.mp hj
    obtain ⟨A,p⟩:= u i.2 (by omega) j.2 (by omega) (x.2+1); obtain ⟨B,q⟩:= b i.1 (by omega) j.1 (by omega) (x.1+1); exact ⟨_,(p.and (q.and h)).mono fun n ⟨u,g,v⟩=> Shelf.rondelTap (U:=P n i.2 j.2) (T:=A' i.2 j.2) (P:=Q n i.1 j.1) (Q:=B' i.1 j.1) g u v he hu (Finset.mem_antidiagonal.mp hx)⟩
variable (L:Theatre H T p e E W)
lemma plumeK (hu:L.V.anchor≤m): (inkPin (L.angle m hu)).patch= loose L.V.draws m:=by rw [(L.effort m hu).1]; rfl
lemma plumeP (hu:L.V.anchor≤ m): (inkPin (L.angle m hu)).s= (L.V.mint m hu).s:=by rw [(L.effort m hu).1]; rfl
lemma plume (hu:L.V.anchor≤m):(L.angle m hu).lamp.s <(L.V.mint m hu).s:= by rw [←plumeP L hu]; exact (L.angle m hu).lamp.outlet.trans_lt (L.angle m hu).lamp.path.holds
lemma plumeT (hu:L.V.anchor≤m):(L.angle m hu).lamp.s/(loose L.V.draws m).L.val ≤ (L.angle m hu).lamp.input:=by rw [← plumeK L hu]; exact (L.angle m hu).lamp.ports
abbrev FansN (L:Theatre H T p e E W)(N m:ℕ)(a: Alma F) (w:Site (loose L.V.draws m).L) := gatherT (loose L.V.draws m) w (lift w) ((L.lore N (m+1)).2 a)
abbrev fansW (L:Theatre H T p e E W)(m:ℕ)(a:Alma F)(w:Site (loose L.V.draws m).L):= gatherT (loose L.V.draws m) w (lift w) (L.matron (m+1) a)
-- Efficient! following syntactic LM
lemma prongs (u:L.V.anchor≤m)(v:i≤e)(j: Alma F)(w:Site (loose L.V.draws m).L)(g:t<(L.angle m u).lamp.s)(hp:0≤ t)(k): Fleets (L.V.ωJ m) t (fun n=>slidesJ (loose L.V.draws m) (middleF L.V.draws m n) (FansN L n m j w) i k) (slidesJ (loose L.V.draws m) (holdM L.V.draws m) (fansW L m j w) i k):=by
    let R:=L.V; let I:= L.angle m u; let s:= I.lamp.s; let S:=R.mint m u; have hq:0<s:= I.lamp.anger
    have hD (n:ℕ)(h:m<n): Ballast s S.D (R.ωJ m n) (upper (1:ropes Cover (Pick S.gear) (Pick S.gear)) (middleF R.draws m n)) (upper 1 (holdM R.draws m)):=Ballast.up (Ballast.same (dragCup.one.le S.credit) (R.ωJ_nn u n)) (((stride_pegs R u h le_rfl).1).mono (plume L u).le)
    obtain ⟨A,p⟩:= fleetOn L u v j k; exact ⟨_,(p.and (eventually_gt_atTop m)).mono (fun n ⟨U,v⟩=>
        Shelf.prismLens (P:=tiles (loose R.draws m).L (FansN L n m j w i)) (Q:=tiles (loose R.draws m).L (fansW L m j w i)) ((pays_feather (loose R.draws m) w U).portal (plumeT L u) hq.le) (hD n v) g hp)⟩
abbrev punchY (A: Levels G)(Ñ:ChartRatio G) (P:Single G D)(N m:ℕ):= puck (loose A m) A.clock.kernel Ñ (leftF A m N) (middleF A m N) (actionW A Ñ N (m+1)) P
abbrev punch (A: Levels G)(Ñ:ChartRatio G)(P:Single G D)(m:ℕ):= puck (loose A m) A.clock.kernel Ñ (holdΓ A m) (holdM A m) (timeless A Ñ (m+1)) P
lemma pike (u:L.V.anchor≤m)(v:i≤ e)(j: Alma F)(w:Site (loose L.V.draws m).L)(g:t<(L.angle m u).lamp.s)(hp:0≤ t)(q k): Fleets (L.V.ωJ m) t (fun n=> punchY L.V.draws L.V.paid (FansN L n m j w) n m q i k) (punch L.V.draws L.V.paid (fansW L m j w) m q i k):=by
   let R:=L.V; let s:=(L.angle m u).lamp.s; let S:= R.mint m u; let θ:= R.ωJ m
   let Piα n : ropes Cover (Helms S.gear) (Helms S.gear):=stair (upper (leftF R.draws m n) 0) 0; let V: ropes Cover (Helms S.gear) (Helms S.gear):= stair (upper (holdΓ R.draws m) 0) 0
   have hh : ∀ᶠ i in atTop,Ballast S.s S.D (θ i) (Piα i) V :=by
       filter_upwards [eventually_gt_atTop m] with i h; have hy:=R.ωJ_nn u i; have hp := zero_le_one.trans S.credit; exact Ballast.staged (Ballast.up (stride_pegs R u h le_rfl).2 (Ballast.zero.fee hy hp)) (Ballast.zero.fee hy hp)
   let F n:= punchY R.draws R.paid (FansN L n m j w) n m; let Q:= punch R.draws R.paid (fansW L m j w) m
   induction q using Nat.strong_induction_on generalizing t i k with
   | h q ih=>
      cases q with
      | zero=> simp_rw [punchY,punch,puck,level]; exact prongs L u v j w g hp k
      | succ n=>
        obtain ⟨a,hb,hc⟩:=exists_between g
        have ht:= hc.trans (plume L u); have hK:0≤a:= hp.trans hb.le
        have hX p (hp:p≤n) i' (hi:i'≤ i) r: Fleets θ a (fun x=> F x p i' r) (Q p i' r):= ih p (by omega) (by omega) hc hK r
        have he p' (_:p'≤ n) j (hj:j≤ i) k:= vapor_trail R u (show j≤e+1 from by omega) p' k ht hK
        have hx:= hh.mono (fun i p=>p.mono ht.le)
        have hg : Fleets θ t (fun v=> Soil.paintC (Piα v) (dew R m v) (F v) n i k) (Soil.paintC V (vapor R m) Q n i k):= Fleets.colorado hx hX he hb hp k
        have hG : Fleets θ t (fun v=>Soil.paintC ((Piα v).transpose) (dew R m v) (F v) n i k) (Soil.paintC (V.transpose) (vapor R m) Q n i k):= Fleets.colorado (hx.mono fun n p=> BankT p) hX he hb hp k
        obtain ⟨A,hq⟩:=hX n le_rfl i le_rfl (k+2); have hH: Fleets θ t (fun i'=>rime (Piα i') (F i' n i) k) (rime V (Q n i) k):= ⟨_,(hx.and hq).mono fun j p=> Shelf.rimming (P:=F j n i) (Q:=Q n i) p.2 p.1 hb hp⟩
        simp_rw [punchY,punch,puck,inchC]; exact ((hH.add hg).add hG).μ _

abbrev Gold (m:ℕ):Thesis F D:= fun i=> chorus (loose L.V.draws m) L.V.draws.clock.kernel L.V.paid (holdΓ L.V.draws m) (holdM L.V.draws m) (timeless L.V.draws L.V.paid (m+1)) h (L.matron (m+1) i)
abbrev copper (N m:ℕ): Thesis F D:= fun i=> chorus (loose L.V.draws m) L.V.draws.clock.kernel L.V.paid (leftF L.V.draws m N) (middleF L.V.draws m N) (actionW L.V.draws L.V.paid N (m+1)) h ((L.lore N (m+1)).2 i)
lemma golden (u:L.V.anchor≤m)(v:i≤e)(j: Alma F)(r): Fleets (L.V.ωJ m) (L.angle m u).lamp.exitS (fun n=> copper L n m j i r) (Gold L m j i r):=by
   simp_rw [copper,Gold,chorus,Pi.smul_apply,Finset.sum_apply,windsT, sluice,Finset.sum_apply]; refine Fleets.μ ?_ _;
   apply Fleets.fleetSum; intro w _; apply Fleets.gulp; exact Fleets.fleetSum (P:=fun q n=>punchY L.V.draws L.V.paid (FansN L n m j w) n m q i r) (fun q _=> pike L u v j w (L.angle m u).lamp.vio (L.angle m u).lamp.positive.le q r)
end YM.WilsonCoeffUV.Cosmos
