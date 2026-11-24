import YM.WilsonCoeffUV.Wick.Mesh
/-!
# Limit W and identities. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Exterior Next.Free Tree Precision Power Embroider Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm Fountain PathCost
open Bank.Carp
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {c n:Side}{U V α:Type*} {G:Gauge} {h D i j k e n' b m N M r:ℕ}{F:Labels.Frame G h} {H:Hol G} {T:SectionData F}
variable {z ξ σ A' B:ℝ} {s t:ℝ}{E W C C':Credit}{p:h<D}
variable (L:Theatre H T p e E W)(f:Weston L C)

def seaE (A:Levels G)(m:ℕ): ropes Cover (Hooks G) (Hooks G):= of fun i j=> coming (fun n=>sea A n m i j)
def Matthew (A: Levels G)(T: SectionData F)(p:h<D)(Ñ:ChartRatio G)(m:ℕ): Wall F:= of fun i j=> let Y:=glory A Ñ T p m j; echoS F (mason (seaE A m) (Y 0) h (valence F i)) i
include f
lemma frontS (u:L.V.anchor≤m)(w:m≤ b)(p:b≤N): let R:=L.V; let Z:=R.cash (C.prodC ((dome E).powC 2)) m; let P:= sea R.draws N m; let Q:=seaE R.draws m; shoulder P Z∧ shoulder Q Z∧ shoulder (P-Q) (Z*R.tempC m b):=by
   intro R Z P Q; have ht b (q:m≤b) N M (p:b ≤ N)(v:b≤ M):= tolling L.V C u q p v (f.hcap m u); let X:= R.tempC m
   have he i j:Tendsto (fun n=>sea R.draws n m i j) atTop (𝓝 (Q i j)):=by
       apply augC (δ:=fun n=>Z*X n) (by simpa using (PathCost.fade R.draws.S m).const_mul Z); filter_upwards [eventually_ge_atTop m] with b hv; intro i' j' hi hj; exact (ht b hv i' j' hi hj).2.2.2 i j
   have hz := (ht b w N N p p); refine ⟨hz.1,⟨hz.1.1,fun i j=> le_of_tendsto (he i j).norm ((eventually_ge_atTop b).mono fun n hv=> (ht b w N n p hv).2.1.2 i j)⟩, hz.2.2.1,fun i j=> le_of_tendsto (tendsto_const_nhds (x:=P i j) |>.sub (he i j)).norm ?_⟩; exact (eventually_ge_atTop b).mono fun n hn=> (ht b w N n p hn).2.2.2 i j
lemma Mackle (a:L.V.anchor≤m): let R:=L.V; breeze (fun n => Wray R.draws R.paid T p n m) (Matthew R.draws T p R.paid m):=by
    intro R i j; let Q:=R.draws; let K:= C.prodC ((dome E).powC 2); let V n:= (L.lore n m).2 j; let W':= L.matron m j
    let S:=(L.angle m a).lamp; have he:=S.positive
    let u:=(allPlays H T p e E W).choose; let P:= (∑ i'∈Finset.range (h+1), loft (Hooks G) (valence F i) S.exitS (S.exitS/2) i') * R.cash K m^h * R.cash u m
    have hv n (g:m≤ n): Shelf Bank.terrain 0 (S.exitS/2) P (R.tempC m n) (mason (sea Q n m) (V n 0) h (valence F i)) (mason (seaE Q m) (W' 0) h (valence F i)):=by
       obtain ⟨v,q,x⟩:=frontS L f a g (le_refl n); have hf:= (allPlays H T p e E W).choose_spec; exact ivory (half_lt_self he) (half_pos he) v q x (K.purchase (R.depth _ a)) (trail_pos ..).le (fun b _=> cheers L (hf 0 (valence F j) _ (Nat.zero_le _)) a g le_rfl j rfl)
    let Z:= threeP F D (S.exitS/2) (half_pos he) (valence F i)
    rw [tendsto_iff_norm_sub_tendsto_zero]; exact squeeze_zero' (Eventually.of_forall fun _=> norm_nonneg _) ((eventually_ge_atTop m).mono fun n hn=> (threeClicks (hv n hn) (half_pos he) i).gap) (show Tendsto (fun n=>Z*P*R.tempC m n) atTop (𝓝 0) from (by simpa only [mul_zero] using (PathCost.fade R.draws.S m).const_mul (Z*P)))
lemma fruit (a:L.V.anchor≤m): leaseM 1 F (Matthew L.V.draws T p L.V.paid m) := by
   have he n (g:m≤n): leaseM 1 F (Wray L.V.draws L.V.paid T p n m):= wick_stand (L.lore n m) (production L g a).1 m n
   have hx:=Mackle L f a; refine ⟨fun i j hv=> tendsto_nhds_unique (hx i j) (tendsto_const_nhds.congr' ((eventually_ge_atTop m).mono fun n hn=> ((he n hn).1 i j hv).symm)),fun i j v z=> tendsto_nhds_unique (hx i j) (tendsto_const_nhds.congr' ((eventually_ge_atTop m).mono fun n hn=> ((he n hn).2 i j v z).symm))⟩
lemma Glinv (a:L.V.anchor≤m): let R:=L.V; breeze (fun n=> (Wray R.draws R.paid T p n m)⁻¹) (Matthew R.draws T p R.paid m)⁻¹:=by
   intro R; let P:=Matthew R.draws T p R.paid m; let Q n:= Wray R.draws R.paid T p n m
   have H:breeze (fun n=> steed (Q n) 1) (steed P 1):= (breeze.const (saddle 1 F)).mul (breeze.sum (S:=Finset.range (ceiling h)) (fun i _=> ((breeze.const 1).sub ((Mackle L f a).mul (breeze.const (saddle 1 F)))).pow i))
   rw [steed_value (fruit L f a)]; intro i j; exact (H i j).congr' ((eventually_ge_atTop m).mono (fun n hn=> Eq.symm (congr_arg (fun P:Wall F=>P i j) (steed_value (wick_stand (L.lore n m) (production L hn a).1 _ _ (A:=R.draws))))))
lemma risenE (a:L.V.anchor≤m): let R:=L.V; let P:=lineS (Jacie R.draws R.paid T p m) 0; let Q j:=Matthew R.draws T p R.paid j; Q m * P=identum P * Q (m+1):=by
    intro R P Q; let X n:=lineS (Jacob R.draws R.paid T p n m) 0; let W n i:= Wray R.draws R.paid T p n i; have hu:breeze X P:= matrix_glim L a (Nat.zero_le e); have hx : breeze (identum ∘ X) (identum P):= by intro i j; simp only [Function.comp_apply,identum,of_apply]; split; exact hu ..; exact tendsto_const_nhds
    ext1 i j; apply tendsto_nhds_unique (f:=fun n=> (W n m * X n) i j) (((Mackle L f a).mul hu) i j)
    apply Tendsto.congr' _ ((hx.mul (Mackle L f (show L.V.anchor≤m+1 by omega))) i j); exact (eventually_gt_atTop m).mono (fun n hn=> congr_fun (congr_fun (intercore L a hn).symm i) j)
-- convergence rates to limit without minding singular M notation
omit L f in theorem pine (H:Hol G)(T:SectionData F)(p:h<D)(e:ℕ)(E W C:Credit):∃ D:Credit,∀ L:Theatre H T p e E W,Weston L C →∀ a b n, L.V.anchor≤a→ a≤b→ b≤n →∀ i j: Alma F, let R:= L.V; let P:= Matthew R.draws T p R.paid a; let A:= Wray R.draws R.paid T p n a; let U:=R.cash D a; twain U (R.tempC a b) (A i j) (P i j)∧twain U (R.tempC a b) (A⁻¹ i j) (P⁻¹ i j):=by
    obtain ⟨B,hB⟩:= tinged H T p E W C e
    obtain ⟨D',hD⟩:=belt (H:=H) (T:=T) (e:=e) (E:=E) (W:=W) (C:=C) (p:=p)
    refine ⟨B.plus D',fun L f a b n h ht p' i j=>?_⟩; intro R P A U
    have hz :=R.depth a h
    let Q:=R.tempC a b; have hx : 0≤ Q:= (trail_pos ..).le
    have hp(S:ℕ→Wall F)(T:Wall F)(w:Credit)(e:breeze S T)(p:∀ N:ℕ,b≤N→twain (R.cash w a) Q (S n i j) (S N i j))(v:w.buy (R.y a)≤U): twain U Q (S n i j) (T i j):=by
        refine (twain.lift (A:=w.buy (R.y a)) ?_ v hx); exact ⟨(p n p').main,le_of_tendsto (e i j).norm ((eventually_ge_atTop b).mono fun n hn=>(p n hn).side),le_of_tendsto (tendsto_const_nhds.sub (e i j)).norm ((eventually_ge_atTop b).mono fun n hn=>(p n hn).gap)⟩
    let S(m):= Wray R.draws R.paid T p m a
    exact ⟨hp S P B (Mackle L f h) (fun n hn=>hB L f a b _ n h ht p' hn i j) (Credit.thickens _ hz), hp (fun n=> (S n)⁻¹) P⁻¹ D' (Glinv L f h) (fun n hn=>hD L f a b _ n h ht p' hn i j) (Credit.thickened _ hz)⟩
end YM.WilsonCoeffUV.Cosmos
