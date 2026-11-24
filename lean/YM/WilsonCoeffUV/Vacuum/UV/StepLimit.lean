import YM.WilsonCoeffUV.Vacuum.UV.UVLimit
/-!
# Convergence of full coefficient step against actual values at UV limit
This lemma only needs aperture existence and eventual polynomial costs at fixed m,
so it uses unquantified constants. Quantitative rate recovered from the
already solved trajectory bounds.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Next.Free Extension.UV.Linear PathCost Realm PowerSeries
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{n N M e m i k r b j l:ℕ}{U V W :Credit}{α β ξ:Type*} {s t a:ℝ}{θ:ℕ→ℝ}

section
variable {X:Type*}[NormedAddCommGroup X] {P Q: ℕ→ Ten X (Cloth α) r}{F H: Ten X (Cloth α) r}

def Cape (θ:ℕ→ℝ)(s:ℝ)(P:ℕ→Ten X (Cloth α) r)(F:Ten X (Cloth α) r) := ∃ A:ℝ,∀ᶠ n:ℕ in atTop, PairA s A (θ n) (P n) F
lemma Cape.zero : Cape θ s (0:ℕ→Ten X (Cloth α) r) 0:=⟨0, Eventually.of_forall fun _=>PairA.zero⟩
lemma Cape.one (h:Amber terrain s a F)(e:∀ n,0≤θ n): Cape θ s (fun _=> F) F:=⟨a, Eventually.of_forall fun i=> PairA.echo h (e i)⟩
lemma Cape.add (h:Cape θ s P F)(p:Cape θ s Q H): Cape θ s (P+Q) (F+H):= by obtain ⟨a,h⟩:= h; obtain ⟨b,p⟩:=p; exact ⟨a+b,(h.and p).mono (fun i x=> x.1.add x.2)⟩
lemma Cape.sub (h:Cape θ s P F)(p:Cape θ s Q H): Cape θ s (P-Q) (F-H):=by obtain ⟨a,h⟩:=h; obtain ⟨b,p⟩:=p; exact ⟨_, (h.and p).mono fun i u=>u.1.sub u.2⟩
lemma Cape.lit (p:Cape θ s P F)(h:Tendsto θ atTop (𝓝 0))(x): Tendsto (fun n=>P n x) atTop (𝓝 (F x)):=by
   obtain ⟨a,p⟩:=p
   rw [tendsto_iff_norm_sub_tendsto_zero]; refine squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) (p.mono fun n x'=>x'.visit.2 x) ?_
   simpa only [mul_zero,zero_mul] using (h.const_mul a).mul_const (Real.exp (-s*soar terrain x))
lemma Cape.sum {S:Finset ξ}{P:ξ→ℕ→Ten X (Cloth α) r}{F:ξ→ Ten X (Cloth α) r}(h:∀ i∈ S,Cape θ s (P i) (F i)): Cape θ s (fun n=>∑ j∈S, P j n) (∑ j∈ S,F j):=by
   classical
   induction S using Finset.induction_on with
   | empty=> simp only [Finset.sum_empty]; exact Cape.zero
   | @insert j S p ih=> simp_rw [Finset.sum_insert p]; exact (h j (Finset.mem_insert_self ..)).add (ih fun k w=>h k (Finset.mem_insert_of_mem w))
lemma Cape.scoop {P:ℕ→ Ten X (Cloth (α⊕β)) r} {F: Ten X (Cloth (α⊕β)) r}(h:Cape θ s P F): Cape θ s (fun i=>scoop (P i)) (scoop F):=by obtain ⟨a,p⟩:=h; exact ⟨_, p.mono (fun i h=> h.spare)⟩
variable [NormedSpace ℝ X]
lemma Cape.pond (h:Cape θ s P F)(c:ℝ) : Cape θ s (c•P) (c•F):=by obtain ⟨a,p⟩:=h; exact ⟨_,p.mono fun i p=>p.coin c⟩
lemma Cape.repack {P:ℕ→Gen X (Cloth α)}{F:Gen X (Cloth α)}(h:Cape θ t (fun i=>P i r) (F r))(L:Side)(hp:0≤s)(he:s/L.val≤t): Cape θ s (fun i=> plants L (P i) r) (plants L F r):=by
   obtain ⟨a,p⟩:=h; exact ⟨_,p.mono fun i p=>PairA.pack (P:=P i) (Q:=F) p hp he⟩
variable [Fintype α][CompleteSpace X]
lemma Cape.crossed {M:ℕ→ ropes Cover α β}{N:ropes Cover α β}{P:ℕ→Gen X (Cloth α)}{F:Gen X (Cloth α)}(p:∀ᶠ n:ℕ in atTop,Ballast s a (θ n) (M n) N)(h:Cape θ s (fun i=> P i r) (F r))(e:∀ n,0≤θ n)(he:t<s)(hv:0≤t): Cape θ t (fun n=>prism (M n) (P n) r) (prism N F r):=by
   obtain ⟨b,h⟩:=h; refine ⟨_,(p.and h).mono fun i ⟨u,v⟩=> PairA.prune_bill (P:=P i) (Q:=F) u (e _) he hv v⟩
variable {M:ℕ→ ropes Cover α α}{N:ropes Cover α α}{P:ℕ→Gen X (Cloth α)}{F: Gen X (Cloth α)}
lemma Cape.helm (p:∀ᶠ n in atTop,Ballast s a (θ n) (M n) N)(h:Cape θ s (fun i=>P i (r+2)) (F (r+2)))(e:∀ n,0≤θ n)(he:t<s)(hv:0≤t): Cape θ t (fun i=>crimp (M i) (P i) r) (crimp N F r):=by
   obtain ⟨b,h⟩:=h; exact ⟨_, (p.and h).mono (fun i wh=> crimp_cap (P:=P i) (Q:=F) wh.1 (e i) he hv wh.2)⟩
lemma Cape.spoon {K:ℕ→Gen ℝ (Cloth α)}{H:Gen ℝ (Cloth α)}(p:∀ᶠ n in atTop,Ballast s a (θ n) (M n) N)(h:∀ j,Cape θ s (fun i=>P i j) (F j))(g:∀ j,Cape θ s (fun i=>K i j) (H j))(e:∀ n,0≤θ n)(he:t<s)(hv:0≤t): Cape θ t (fun i=> whittle (M i) (K i) (P i) r) (whittle N H F r):=by
   unfold whittle; apply Cape.sum; intro j hj; obtain ⟨b,h⟩:= h (j.2+1); obtain ⟨c,g⟩:=g (j.1+1)
   refine ⟨_,(p.and (g.and h)).mono (fun i ⟨d,u,v⟩=> loop_cap (P:=K i) (Q:=H) (F:=P i) (H:=F) d (e _) he hv u v (Finset.mem_antidiagonal.mp hj))⟩
end
namespace Realm
variable (R:Realm G e U) (m:ℕ)
abbrev ωJ (b:ℕ) := R.cash (doubling U) m* R.tempC m b
variable {m}
lemma ωJ_nn (h:R.anchor≤m)(b):0≤ R.ωJ m b:=mul_nonneg (zero_le_one.trans (Credit.purchase _ (R.depth _ h))) (trail_pos ..).le
lemma ωJ_vanish (m): Tendsto (R.ωJ m) atTop (𝓝 0):=by simpa only [mul_zero] using (PathCost.fade R.draws.S m).const_mul (R.cash (doubling U) m)
end Realm
variable (R:Realm G e U)
private lemma hired (h:R.anchor≤m)(v:k≤ e)(r): Cape (R.ωJ m) (R.mint m h).past (fun N=>actionW R.draws R.paid N (m+1) k r) (timeless R.draws R.paid (m+1) k r):= by
   have hu : R.anchor ≤ m+1:=by omega
   obtain ⟨T,p⟩:= full_vacuum G e U; exact ⟨_, (eventually_ge_atTop (m+1)).mono fun N hn=> (inherited (p k v r) R hu hn le_rfl).graded (R.also_temp h) (R.crossing m h)⟩
-- param ballast fixed
lemma coexistent (h:R.anchor≤m)(p:k≤e)(r)(hv:t < (R.mint m h).s)(hg:0≤ t): Cape (R.ωJ m) t (fun N=> stellar (loose R.draws m) R.draws.clock.kernel R.paid (middleF R.draws m N) (actionW R.draws R.paid N (m+1)) k r) (stellar (loose R.draws m) R.draws.clock.kernel R.paid (holdM R.draws m) (timeless R.draws R.paid (m+1)) k r):=by
    let I:=R.mint m h; let L:= loose R.draws m; let A:= middleF R.draws m; let B:= holdM R.draws m
    let u (n:ℕ):ropes Cover (Pick I.gear) (Helms I.gear):= upper 1 (A n); let v : ropes Cover (Pick I.gear) (Helms I.gear):= upper 1 B
    have ht:= R.ωJ_nn h
    have he:0≤ I.s:= hg.trans hv.le
    have hd : ∀ᶠ n in atTop,Ballast I.s I.D (R.ωJ m n) (u n) v:= (eventually_gt_atTop m).mono fun n hn=> Ballast.up (Ballast.same (dragCup.one.le I.credit) (ht n)) ((stride_pegs R h hn le_rfl).1)
    have hf : ∀ᶠ n in atTop, Ballast I.s I.D (R.ωJ m n) (stair (u n) ladder) (stair v (ladder (α:=Pick I.gear))):= hd.mono fun n hn=> Ballast.staged hn (Ballast.same (ladder_amber.le I.credit) (ht n))
    obtain ⟨a,b⟩:= bloom_bill R.paid k r I.past I.depth.le
    have hs:= Cape.crossed (P:=fun n=>plants L.L (bearingJ R.paid k)) (F:=plants L.L (bearingJ R.paid k)) hd (Cape.repack (P:=fun n=>bearingJ R.paid k) (F:=bearingJ R.paid k) (Cape.one b ht) L.L he I.lift) ht hv hg
    let W:= scrub (warren L R.draws.clock.kernel G) k
    have hx:∃ a:ℝ, Amber terrain I.s a (W r):=by unfold W scrub; split; exact ⟨0,Amber.zero⟩; exact tide_pay _ _ _ k _ _ he
    obtain ⟨t,hw⟩:= hx
    have hp:= Cape.crossed (P:=fun _=> W) (F:=W) hf (Cape.one hw ht) ht hv hg
    let P n:= scrub (actionW R.draws R.paid n (m+1)) k
    let Q:= scrub (timeless R.draws R.paid (m+1)) k
    have hh: Cape (R.ωJ m) I.past (fun i=>P i r) (Q r):=by unfold P Q scrub; split <;> first | exact Cape.zero | exact hired _ h p r
    have hu:= Cape.crossed (P:=fun n=>plants L.L (P n)) (F:=plants L.L Q) hd (Cape.repack (P:=P) (F:=Q) hh L.L he I.lift) ht hv hg
    exact (hs.sub hp).sub hu

def dew (R:Realm G e U) (m N:ℕ): Layers ℝ (Cloth (Hinge G (loose R.draws m).L)):= spurs (loose R.draws m) R.draws.clock.kernel R.paid (leftF R.draws m N) (middleF R.draws m N) (actionW R.draws R.paid N (m+1))
def vapor (R:Realm G e U)(m:ℕ): Layers ℝ (Cloth (Hinge G (loose R.draws m).L)):=spurs (loose R.draws m) R.draws.clock.kernel R.paid (holdΓ R.draws m) (holdM R.draws m) (timeless R.draws R.paid (m+1))
lemma vapor_trail (h:R.anchor≤m)(p:k ≤ e)(n r:ℕ)(hv:t<(R.mint m h).s)(hg:0≤ t) : Cape (R.ωJ m) t (fun i=>dew R m i n k r) (vapor R m n k r):=by
   let I:= R.mint m h; have hp:= zero_le_one.trans I.credit
   let M (i:ℕ) : ropes Cover (Helms I.gear) (Helms I.gear):= stair (upper (leftF R.draws m i) 0) 0
   let N': ropes Cover (Helms I.gear) (Helms I.gear):=stair (upper (holdΓ R.draws m) 0) 0
   have he:=R.ωJ_nn h
   have hx:∀ᶠ n in atTop,Ballast I.s I.D (R.ωJ m n) (M n) N' := (eventually_gt_atTop m).mono fun i hi=> Ballast.staged (Ballast.up (stride_pegs R h hi le_rfl).2 (Ballast.zero.fee (he i) hp)) (Ballast.zero.fee (he i) hp)
   induction n using Nat.strong_induction_on generalizing t k r with
   | h n ih=>
     cases n with
     | zero=> simp_rw [dew,vapor,spurs,tide_zero]; exact coexistent _ h p r hv hg
     | succ n=>
       obtain ⟨w,H,HU⟩:= exists_between hv
       have hU:0≤ w:= hg.trans H.le
       have ht:∀ᶠ i in atTop,Ballast w I.D (R.ωJ m i) (M i) N':= hx.mono (fun i hi=>hi.mono HU.le)
       have hh:= Cape.helm (P:=fun i=>dew R m i n k) (F:=vapor R m n k) ht (ih _ n.lt_succ_self p (r+2) HU hU) he H hg
       have hz:Cape (R.ωJ m) t (fun i=>curlJ (M i) (dew R m i) (dew R m i) n k r) (curlJ N' (vapor R m) (vapor R m) n k r):=by
          simp_rw [curlJ,Finset.sum_apply]; apply Cape.sum; intro j hj; have hb:= Finset.mem_antidiagonal.mp hj; apply Cape.sum; intro i hi; have ht':= Finset.mem_antidiagonal.mp hi
          exact Cape.spoon (P:=fun v=>dew R m v j.2 i.2) (F:=vapor R m j.2 i.2) (K:=fun v=>dew R m v j.1 i.1) (H:=vapor R m j.1 i.1) ht (fun r=>ih j.2 (by omega) (by omega) r HU hU) (fun r=>ih j.1 (by omega) (by omega) r HU hU) he H hg
       simp_rw [dew,vapor,spurs,tide_rise]
       exact (hh.add hz).pond _
lemma eternal_phase (h:R.anchor≤m)(w:k≤ e)(r:ℕ): Cape (R.ωJ m) (R.mint m h).σ (fun i=> freshet R.draws R.paid i m k r) (eternal R.draws R.paid m k r):=by
    let I:=R.mint m h
    have he: ∀ᶠ b in atTop,Ballast I.σ I.D (R.ωJ m b) (rightF R.draws m b) (holdZ R.draws m):=by
       filter_upwards [eventually_ge_atTop m] with b hb
       exact ((peg R h hb le_rfl).mono I.win.le).partial (mul_le_mul_of_nonneg_right (Credit.thickens _ (R.depth _ h)) (trail_pos ..).le)
    have ht: Cape (R.ωJ m) I.σ (fun i=>flatPal (rightF R.draws m i) k r) (flatPal (holdZ R.draws m) k r):=⟨_,he.mono fun i hi=>kernel_pair hi k r⟩
    have hv (i:ℕ) := vapor_trail R h w i r I.win I.width.le
    let s:= Finset.range (3+3*k)
    have hp: Cape (R.ωJ m) I.σ (fun i=> sluice (∑ j∈s, dew R m i j k) r) (sluice (∑ j∈s,vapor R m j k) r):= by
        simp_rw [sluice,Finset.sum_apply]; exact Cape.scoop (P:=fun i=>∑ j∈s,dew R m i j k r) (Cape.sum (fun j _=>hv j))
    have hU:∃ C, Amber terrain I.σ C (uband (U:=YForest G) (perζ R.draws.clock.kernel R.paid) k r):=by
       unfold uband; by_cases hh:0=r
       · subst r; simp only [shine_lit]; refine ⟨‖coeff k (perζ R.draws.clock.kernel R.paid)‖,norm_nonneg _,fun i=>?_⟩; simp [soar,league]
       rw [shine_dark hh]; exact ⟨_,Amber.zero⟩
    obtain ⟨C,hC⟩:= hU
    exact (ht.sub hp).add (Cape.one hC (R.ωJ_nn h))
-- this gives paid rate independent of Realm
lemma inherited_phase (p:Trails G e U V i r)(hf:i≤ e)(R:Realm G e U)(h:R.anchor≤m)(q:m<b)(v:b≤N): PairA (R.mint m h).σ (R.cash V m) (R.tempC m b) (freshet R.draws R.paid N m i r) (eternal R.draws R.paid m i r):=by
    have hd:=p R m h b N N q v v
    have hu:= eternal_phase R h hf r
    have he:= hu.lit (R.ωJ_vanish m)
    refine ⟨hd.pose,⟨hd.nn,fun x=> le_of_tendsto (he x).norm ((eventually_ge_atTop b).mono fun M hv=> (p R m h b M M q hv hv).pose.2 x)⟩,⟨hd.visit.1,fun x=> le_of_tendsto (tendsto_const_nhds.sub (he x)).norm ?_⟩⟩
    exact (eventually_ge_atTop b).mono fun i ha=> (p R m h b N i q v ha).visit.2 x
end YM.WilsonCoeffUV.Bank
