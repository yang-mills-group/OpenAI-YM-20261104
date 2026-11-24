import YM.WilsonCoeffUV.Root.Gain.Subtracted
/-! # Full line `A0`. Uses reel for each source point; pierces.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n c:Side}{U V:Type*}{r h D l j e k:ℕ} {G:Gauge}{F:Labels.Frame G h}{s t A X Z D':ℝ}

lemma nectar (P:Patch)(w:Site P.L) (Q:Drip P G)(b:Leg G) (g: Wages b) (hp: dragCup Bank.terrain s X Q)(e:0<s) (x:YForest G): Summable fun y=> ‖sip P Q w y x*b y‖ := by
   let F (y:Fin 1→ YForest G):= sip P Q w (y 0) x
   let k:=(panel P.L (Hooks G)).symm (lift w+x.1,x.2); let M:ℝ:= Real.exp (s*size k.1); have hm:0≤ M:= by unfold M; positivity
   let H:= (X*M)
   have he x' (u:Fin 1→YForest G) (hz:x'=u 0) : port_d 0 u=size x'.1:=by
       apply le_antisymm; · refine (vessels u).trans_eq ?_; simp only [Fin.sum_univ_one,hz]
       rw [hz]; exact port_size ..
   have hh: Twig 0 s H F:=by
      refine ⟨mul_nonneg hp.1 hm,fun u=>(hp.2 k (u 0)).trans ?_⟩
      unfold H; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ hp.1; unfold M; rw [← Real.exp_add,Real.exp_le_exp,he (u 0) u rfl]; have ht' : size (u 0).1 ≤ Bank.terrain.gap k.1 (u 0).1 + size k.1:=by
           change _ ≤ size ((u 0).1-k.1) + size k.1; exact le_trans (Nat.le_of_eq (Eq.symm (congr_arg size (sub_add_cancel ..)))) (size_add ..)
      have ht : (size (u 0).1:ℝ) ≤ Bank.terrain.gap k.1 (u 0).1 + (size k.1:ℝ):=by exact_mod_cast ht'
      nlinarith only [mul_le_mul_of_nonneg_left ht e.le]
   apply Summable.congr (f:=fun y=> ‖pressOn F (fun _=>b) (fun _=>y)‖) ((pluck_profit hh e (fun i=>g)).comp_injective (fun a b e=>congr_fun e 0)); intro i; unfold pressOn; rw [Fin.prod_univ_succ]; simp [F,mul_comm]
lemma parent_cell (L:Side)(x: Cover): parentC L x=Carrier.cellar L x:=by
    let P:= (Carrier.cellar L x,wrap L x,()); have he:= Carrier.balance L x; have hh : panel L Unit P=(x,()):= by rw [castE]; exact Prod.ext (Eq.trans (add_comm ..) he.symm) rfl
    exact (show parentC L x=P.1 by rw [parentC,←hh,Equiv.symm_apply_apply])

abbrev Agate (P:Patch)(M: Carrier.Lines P.L)(G:Gauge): Drip P G:= shuttleM (gaugedA G P M)
lemma fountain_bit (P:Patch)(M: Carrier.Lines P.L)(w:Site P.L)(x y:Cover)(i d:Axis)(a b:G.ColorIndex):
    sip P (Agate P M G) w (waive y d b) (waive x i a)= if a=b then Carrier.member M (lift w+x) i d (y-Carrier.cellar P.L (lift w+x)) else 0 :=by
   unfold sip spring Agate; rw [Matrix.submatrix_apply,patchwork]; change (coloration _ _ _ _ _ _ (y-parentC P.L (lift w+x)))=_; rw [parent_cell]; unfold coloration; split<;>rename_i h; · rw [if_pos (show a=b from h)]; rw [parent_cell]; rfl
   rw [if_neg (show ¬a=b from h)]
def nativ (P:Patch)(w:Site P.L)(f:Place.Potential G): Place.Potential G:= fun x=> f (x+Place.seat (lift w))
lemma irrigate (P:Patch)(M:Carrier.Lines P.L)(w:Site P.L)(x:YForest G)(f f':Place.Potential G)(p:applyLine M (verdict f)=verdict f') (g:f ∈ rangeLt _ k) (ha:Whole M)(hp:dragCup Bank.terrain s X (Agate P M G))(hs:0<s): assay (nativ P w f') x= ∑' u, sip P (Agate P M G) w u x * assay f u:=by
   obtain ⟨⟨x,i⟩,a,rfl⟩:=every_stone x; let S:= Agate P M G; let K:=booths G
   let b:= assay f; let V u:= sip P S w u (waive x i a)*b u; let c:= lift w+x; let v:= Carrier.cellar P.L c; let d:=verdict f
   have he (T:Place.Potential G)(x:Cover)(i j): assay T (waive x i j)= (verdict T x i) j:=by unfold assay waive; rw [feather_at]; rfl
   change assay _ (waive x i a)= ∑' u, V u
   have hg:= K.summable_iff.mpr ((nectar _ w S b (pays_assay _ g) hp hs (waive x i a)).of_norm : Summable V)
   unfold Function.comp at hg
   rw [he,←K.tsum_eq V,hg.tsum_prod,tsum_fintype,Fintype.sum_prod_type,Finset.sum_eq_single a]
   · let L': G.Color→L[ℝ]ℝ:= Fountain.colorL a
     have hm : verdict (nativ P w f') x i=verdict f' c i:=by unfold verdict nativ; rw [show Place.seat c=_ from Place.seat_add ..,add_comm (Place.seat x)];
     rw [hm,← p]; change L' (applyLine M d c i)= _; unfold applyLine; rw [map_sum]; apply Finset.sum_congr rfl; intro j _; let A:=Carrier.member M c i j
     change L' (stream A v (fun y=> d y j)) = ∑' y,V (K ((a,j),y)); obtain ⟨t,D,H,h⟩:=ha; obtain ⟨B,t0,u⟩:= royalties _ _ g
     rw [stream,L'.map_tsum (stream_income H (show Width t D A from h _ _) v k t0 (fun y=> show ‖d y j‖ ≤ _ from u y j)).2.1.of_norm,←(Equiv.addLeft v).tsum_eq (fun y=> V (K ((a,j),y)))]; refine tsum_congr fun y=>?_
     change L' (A y • d (v+y) j) = V (waive (v+y) j a); unfold V b; rw [he,show sip _ _ _ _ _= _ from fountain_bit P M w x (v+y) i j a a,if_pos rfl,L'.map_smul,show v+y-_=y from add_sub_cancel_left ..]; rfl
   · intro b hb H; apply Finset.sum_eq_zero; intro j _; trans ∑' _ : Cover,(0:ℝ); refine tsum_congr fun y=> ?_
     · dsimp only; rw [show K _=waive y j b from rfl,show sip _ _ _ _ _= _ from fountain_bit P M w x y i j a b,if_neg (Ne.symm H),zero_mul]
     rw [tsum_zero]
   simp
lemma pluck_roller (P:Patch)(M: Carrier.Lines P.L)(w:Site P.L)(T:Fin r→Place.Potential G)(q q':Fin r→ℕ)(u: Fin r→Place.Potential G)(p:∀ i, T i ∈ rangeLt _ (q i))(z:∀ i, u i∈ rangeLt _ (q' i))(h:∀ i,applyLine M (verdict (T i))=verdict (u i))(g:Whole M)(hp:dragCup Bank.terrain s X (Agate P M G))(hs:0<s)
  (Y:ChamberTen G (Vote D) r)(x:Twig 0 t A Y)(hv:s/P.L.val≤t): pluck (pulseS P w (Agate P M G) Y) (assay ∘ T) = soprano P w D (pluck Y (fun i=> assay (nativ P w (u i)))):=
   pluck_pulse P w _ hp hs hv _ x _ _ (fun i=>pays_assay _ (p i)) (fun i=>pays_assay _ (Place.band_shift (z i) _)) (fun i x=> irrigate P M w x _ _ (h i) (p i) g hp hs) (fun i y=> nectar _ _ _ _ (pays_assay _ (p i)) hp hs y)
end YM.WilsonCoeffUV.Cosmos
