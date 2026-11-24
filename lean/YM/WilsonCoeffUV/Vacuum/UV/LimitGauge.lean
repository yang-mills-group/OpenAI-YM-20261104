import YM.WilsonCoeffUV.Vacuum.UV.ExactLimit
/-!
# Global invariance on coefficients from arbitrary compact color ad,
plus axis translations and impulsive transversality. Value-null and affine jet
through the recalibration at ANY finite formal order.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Next.Free Extension.UV.Linear PathCost Realm PowerSeries
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{c:Side}{n N M e m i k r b j l:ℕ}{U V W :Credit}{A:Levels G}{Ñ:ChartRatio G}

section color
-- finite curry by byShade; deterministic site. extends independent indexing.
def mural {R:Type*}[AddCommGroup R][Module ℝ R](K:Ten R (YForest G) r): Prop:= ∀ (f:G.El) (v:Fin r→ Edge Cover)(x:Fin r→G.ColorIndex), K (fun i=>stone (v i) (x i))= ∑ u:Fin r→G.ColorIndex,(∏ i,gammaC f (u i) (x i)) • K (fun j=>stone (v j) (u j))
lemma shot_card (T:PChart G c)(h:rollTest (flash T) (flash T) 1 0){b:ℕ}(hp:shellK b T)(heP:∀ i,Pure (T i))(f:G.El)(e r:ℕ)(v:Fin r→Edge (Site c))(x:Fin r→G.ColorIndex): T e r (fun i=>entryS G c (v i,x i))=∑ i:Fin r→G.ColorIndex,(∏ j,gammaC f (i j) (x j)) • T e r (fun j=>entryS G c (v j,i j)):=by
   let D:= Fin r→Woods G c
   let b : (Fin r→G.ColorIndex)→D:= fun u i=>entryS G c (v i,u i)
   let V j (z:D):= shadeS f c (z j) (b x j)
   let F (z:D):= (∏ j,V j z) • T e r z
   have hx j (z): V j (b z)=gammaC f (z j) (x j):=by unfold V b shadeS; rw [Matrix.of_apply,Equiv.symm_apply_apply,Equiv.symm_apply_apply,if_pos rfl]; rfl
   have he: Injective b:= fun i j h=>funext fun x=>Prod.mk.inj ((entryS G c).injective (congr_fun h x)) |>.2
   calc
    _ = ∑ z:D,F z:= by
       conv_lhs=>rw [byShade h hp heP e f]
       rfl
    _ = ∑ z∈Finset.univ.image b, F z:= Eq.symm <| Finset.sum_subset (Finset.subset_univ _) (fun z _ q=>by
         by_contra H
         apply q
         let u (j:Fin r):= (entryS G c).symm (z j)
         have hp j: (u j).1=v j:=by
             by_contra H'; apply H; unfold F; rw [Finset.prod_eq_zero (Finset.mem_univ j),zero_smul]; unfold V; rw [shadeS,Matrix.of_apply,if_neg]; unfold b; rw [Equiv.symm_apply_apply]; exact H'
         refine Finset.mem_image.mpr ⟨fun j=>(u j).2,Finset.mem_univ _,funext fun i=>?_⟩
         change entryS G c (v i,(u i).2)=_
         rw [← hp]; exact (entryS G c).apply_symm_apply (z i))
    _ = _:= by rw [Finset.sum_image (fun x _ j _ p=> he p)]; apply Finset.sum_congr rfl; intro i hi; unfold F; simp_rw [hx]; rfl

lemma mural_sigma (T:Crude G)(M:Canvas G) {b} (h:∀ n,rollTest (flash (T n)) (flash (T n)) 1 0)(hp:∀ n,shellK b (T n))(ht:∀ n i,Pure (T n i))(e r:ℕ)(hx:Yields (fun n=>T n e r) (M e r)): mural (M e r):=by
   intro f v x
   let Q (w:Fin r→G.ColorIndex) := fun i=>stone (v i) (w i)
   let F n:= dilute (fun n=>T n e r) n
   let K i:= M e r (Q i)
   let Z (u:Fin r→G.ColorIndex):=∏ i,gammaC f (u i) (x i)
   have hh n :F n (foldUnder n ∘ Q x)=∑ u, Z u • F n (foldUnder n ∘ Q u):=by
        let W (z: Fin r→YForest G):=foldUnder n ∘ z; let g (i:Fin r): Edge (Site n):= (wrap n ((v i).1), (v i).2)
        have ht : T n e r (W (Q x))= ∑ u,Z u • T n e r (W (Q u)):= shot_card (T n) (h n) (hp n) (ht n) f e r g x
        simp_rw [F, dilute]; split
        · unfold W at ht; simp_rw [Pi.smul_apply, ht, Finset.smul_sum]; apply Finset.sum_congr rfl; intro i _; simp_rw [smul_eq_mul]; rw [mul_left_comm]
        exact ht
   have ht (i): Tendsto (fun n=> F n (foldUnder n ∘ Q i)) atTop (𝓝 (K i)):= hx.point _
   exact tendsto_nhds_unique (ht x) ((tendsto_finsetSum _ (fun i _=> (ht i).const_smul (Z i))).congr (fun i=> (hh i).symm))
lemma mural_finite {m N:ℕ}(hs:G.Simple)(h:LocalRatio Ñ)(p:m≤N)(e r:ℕ): mural (actionW A Ñ N m e r):=by
   let T:= old A Ñ hs h N m p
   exact mural_sigma _ _ (fun n=>(T.basis n).valid 1 0) (fun n=>(T.basis n).lamp) (fun n=>(T.basis n).shape) _ _ (T.patch e r)
end color

structure Doric (U:Canvas G)(K:ropes Cover (Hooks G) (Hooks G))(e:ℕ) : Prop where
    c : U 0= shine (orbQ K)
    lamp k: k≤ e → pillar U k
    lit k r: k≤ e → mural (U k r)
    s k: k≤ e → ∀ r s b x, U k r (tickW s b ∘ x) = (∏ i,rimSign s (x i).2)* U k r x
    tor k: k≤e → ∀ r, stroll (U k r)
    purePoints k: k≤ e → Pure (U k)
    holds k: k≤ e → ∀ r, k+2< r → U k r=0
    parityA k: k≤ e → ∀ r,k%2≠r%2→ U k r=0
    barren k: k≤e → U k 0=0
    zero_color k: k≤e → U k 1=0
    shineA k: k≤e → coeff k (Kstar U)=coeff k (1: Cost)
    shore k: k≤ e → Medium (U k 2)
    aware k: k≤e → 0<k → Aware (U k 2)
    spot k r: k≤e → ∃ σ A,0<σ ∧ Amber terrain σ A (U k r)

variable (R:Realm G e U)
theorem modern (h:R.anchor≤ m): Doric (timeless R.draws R.paid m) (holdZ R.draws m) e := by
   let Q n:=actionW R.draws R.paid n m; let W:= timeless R.draws R.paid m; let I:=R.mint m h
   obtain ⟨T,hT⟩:= full_vacuum G e U
   haveI:= colI R.hG
   have H n (hi:m≤ n): BulkP _ (Q n):=catchment R.draws R.paid R.hG R.green hi
   have he k (hk:k≤e) r x:Tendsto (fun i=> Q i k r x) atTop (𝓝 (W k r x)):= timeless_pt hk R h r x
   have hA k (hk:k≤e) r: Cape (R.tempC m) I.σ (fun i=>Q i k r) (W k r) := ⟨_,(eventually_ge_atTop m).mono fun n hn=> inherited (hT k hk r) R h hn le_rfl⟩
   have ha k (hk:k≤e) r: Amber terrain I.σ (R.cash T m) (W k r):= (inherited (hT k hk r) R h (b:=m) le_rfl (N:=m) le_rfl).vale
   have hz k (hk:k≤e) r (he':∀ n, m≤n → Q n k r=0): W k r=0:= funext fun x=> tendsto_nhds_unique (he k hk r x) (tendsto_const_nhds.congr' ((eventually_ge_atTop m).mono fun n hn=> congr_fun (he' n hn).symm x))
   have hs k (hk:k≤e) r s b x: W k r (tickW s b ∘ x)=(∏ i,rimSign s (x i).2)* W k r x:= tendsto_nhds_unique (he _ hk _ _) (((he k hk r x).const_mul _).congr' ((eventually_ge_atTop m).mono fun n hn=>((H n hn).signs s b k r x).symm))
   have hm k (hk:k≤ e): Medium (W k 2):= by
        intro x y; let i: G.ColorIndex:=Classical.arbitrary _
        let F:= (fun n=> Q n k 2 ![stone x i,stone y i])
        refine ⟨W k 2 ![stone x i,stone y i],fun a b=>?_⟩
        have hp n (p:m≤ n): Q n k 2 ![stone x a,stone y b]= if a=b then F n else 0:= by obtain ⟨u,h⟩:= (H n p).paintU k x y; simp [F,h]
        split <;> rename_i hg
        · exact tendsto_nhds_unique (he k hk _ _) ((he k hk 2 ![stone x i,stone y i]).congr' ((eventually_ge_atTop m).mono fun n hn=> ((hp n hn).trans (if_pos hg)).symm))
        exact tendsto_nhds_unique (he k hk _ _) (tendsto_const_nhds.congr' ((eventually_ge_atTop m).mono fun n hn=> ((hp n hn).trans (if_neg hg)).symm))
   have hl k (hk:k≤ e): coeff k (Kstar W)=coeff k (1:Cost):=by
        rw [stellar_read]; refine tendsto_nhds_unique (beacon (hA k hk 2) (PathCost.fade R.draws.S m) I.width) (tendsto_const_nhds.congr' ((eventually_ge_atTop m).mono fun n hn=>?_)); dsimp only; rw [← stellar_read, (H n hn).rise]
   change Doric W _ e
   refine ⟨?_,fun k hk=>perseveres R h hk,?_,hs,?_,?_,fun k hk r p=>hz k hk r (fun n hn=>(H n hn).rank k r (by omega)),fun k hk r p=>hz k hk r (fun n hn=> (H n hn).grade k r p),fun k hk=>hz k hk 0 (fun n hn=>?_),fun k hk=> hz k hk 1 (fun n hn=>(H n hn).vanishes k),hl,hm,?_,fun k r hk=>⟨_,_,I.width,ha k hk r⟩⟩
   · ext1 r; funext x
     have hz:Tendsto (fun n=>flatPal (rightF R.draws m n) 0 r x) atTop (𝓝 (flatPal (holdZ R.draws m) 0 r x)):=by
         let θ:=fun b=> R.cash (dome U) m * R.tempC m b
         have ht : Tendsto θ atTop (𝓝 0):=by simpa only [mul_zero] using (PathCost.fade R.draws.S m).const_mul (R.cash (dome U) m)
         exact Cape.lit ⟨(R.mint m h).D,(eventually_ge_atTop m).mono fun n hn=> kernel_pair (peg R h hn le_rfl) 0 r⟩ ht x
     exact tendsto_nhds_unique (he 0 (by omega) r x) (hz.congr' ((eventually_ge_atTop m).mono fun n hn=> congr_fun (congr_fun (H n hn).readout.symm r) x))
   · intro k r hk f v x; let z (x:Fin r→G.ColorIndex):= fun i=>stone (v i) (x i)
     let K (u:Fin r→G.ColorIndex):=∏ i,gammaC f (u i) (x i)
     refine tendsto_nhds_unique (he k hk _ _) ((tendsto_finsetSum _ (fun i _=> (he k hk r (z i)).const_smul (K i))).congr' ((eventually_ge_atTop m).mono fun n hn=>?_)); exact (mural_finite (A:=R.draws) R.hG R.green hn _ _ f v x).symm
   · intro k hk r i u; exact tendsto_nhds_unique (he k hk r _) ((he k hk r u).congr' ((eventually_ge_atTop m).mono fun n hn=> ((H n hn).center k r i u).symm))
   · intro k hk r s b; exact tendsto_nhds_unique (he k hk r _) ((he k hk r b).congr' ((eventually_ge_atTop m).mono fun n hn=> ((H n hn).pureU k r s b).symm))
   · exact (congr_fun (congr_fun (H n hn).empty.symm k) 0)
   intro k hk hg
   have he' x (c:G.ColorIndex): windsL x c (W k 2)=0:= by
       funext i; have ht: Tendsto (fun n=>windsL x c (Q n k 2) i) atTop (𝓝 (windsL x c (W k 2) i)):= by
           simp_rw [windsL,Finset.sum_apply, Pi.sub_apply,prune]; exact tendsto_finsetSum _ fun j _=> (he k hk _ _).sub (he k hk _ _)
       exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' ((eventually_ge_atTop m).mono fun n hn=> congr_fun (west_floor (H n hn).separate (H n hn).pureU (H n hn).vanishes k x c).symm i))
   apply aware_of_reset (hs k hk 2) (ha k hk 2) I.width he' (hm k hk); rw [←stellar_read,hl k hk]; simp [hg.ne']
end YM.WilsonCoeffUV.Bank
