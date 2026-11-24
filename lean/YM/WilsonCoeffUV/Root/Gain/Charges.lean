import YM.WilsonCoeffUV.Root.Gain.UnitStubs
/-! # Ledger term prices. Per preimage outright powers. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n c:Side}{U V:Type*}{r h D l j e k:ℕ} {G:Gauge}{F:Labels.Frame G h}{s t A X Z D':ℝ}
lemma vessels (x:Fin r→YForest G): port_d 0 x ≤ ∑ i,size (x i).1:=by
    let v:Fin (r+1)→Cover:=Fin.cons 0 (Prod.fst ∘ x)
    have hu i: size (v i)≤∑ i,size (x i).1:=by refine Fin.cases ?_ (fun i=> Finset.single_le_sum (f:=fun i:Fin r=>size (x i).1) (fun _ _=> Nat.zero_le _) (Finset.mem_univ i)) i; simp [v,size]
    apply league_le Bank.terrain v; intro i j; by_cases h:i=j; · rw [h,Bank.terrain.self]; omega
    apply (size_add (v j) (-v i)).trans ?h
    case h=>
       rw [size_neg]; revert h; refine Fin.cases (fun _=>by simpa [v,size] using hu j) (fun i hij=>?_) i
       revert hij; refine Fin.cases (fun _=>by simpa [v,size] using hu i.succ) (fun j hij=>?_) j
       let s :Fin r→ℕ:=fun i=> size (x i).1; have he : j≠i:= fun h=>hij (Fin.succ_injective r|>.eq_iff.mpr h.symm)
       rw [←Finset.add_sum_erase Finset.univ s (Finset.mem_univ i)]; change s j+s i ≤ _; rw [add_comm (s j)]; exact Nat.add_le_add_left (Finset.single_le_sum (fun i _=> Nat.zero_le _) (Finset.mem_erase.mpr ⟨he,Finset.mem_univ j⟩)) _

def rentM (P:Patch)(s A:ℝ)(m:ℕ)(x:YForest G):= A*speck P^m*Real.exp (-s*size x.1)
def mMarked (i:Fin r→Fin j) := ∑ u,(1+(i u).val)
lemma term_money (P:Patch)(s A:ℝ)(q:0≤s)(p:0≤A)(x:Fin r→YForest G)(i:Fin r→Fin j): ∏ k,rentM P s A ((i k).val+1) (x k) ≤ A^r*speck P^(mMarked i)*Real.exp (-s*port_d 0 x):=by
   simp only [rentM,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,Finset.prod_pow_eq_pow_sum, ←Real.exp_sum]; rw [show (∑ k,((i k).val+1))= mMarked i from Finset.sum_congr rfl fun _ _=>Nat.add_comm ..]
   apply mul_le_mul_of_nonneg_left _ (by positivity [speck_pos P]); apply Real.exp_monotone; rw [←Finset.mul_sum]; apply mul_le_mul_of_nonpos_left _ (by linarith); rw [← Nat.cast_sum]; exact Nat.cast_le.mpr (vessels x)

private def Purl (s:ℝ)(n:ℕ)(x:ℕ): ℝ:= (1+x:ℝ)^n*Real.exp (s*x)
private lemma term_remainder (n:ℕ)(x:Fin r→YForest G)(g:0≤s)(p:r*s≤t) : ∏ i,Purl s n (size (x i).1) ≤ Purl t (n*r) (port_d 0 x):=by
    let Q:= port_d 0 x; have he: (∏ i,Purl s n (size (x i).1))≤ ∏ _i:Fin r, Purl s n Q:= Finset.prod_le_prod (fun _ _=>by unfold Purl; positivity) (fun i _=>by unfold Purl; have ht:= port_size x i; gcongr)
    refine he.trans ?_; rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin]; unfold Purl; rw [mul_pow,pow_mul,← Real.exp_nat_mul]; apply mul_le_mul_of_nonneg_left _ (by positivity); apply Real.exp_monotone; rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right p (by positivity)

abbrev Chunk (h):= Option (Embroider.Spiral h)
def rateC : Chunk h→ℕ
    | none=>h+1
    | some i=>i.val.card
def jotC (P:Patch)(w:Site P.L)(F:Scroll D): Chunk h→Volume D
    | some i=> halo P w i.val F • wallope i.val D
    | none=> page D (growWord P w D F-flowering h (growWord P w D F))
lemma chunks (P:Patch)(w:Site P.L)(F:Scroll D)(h:ℕ): foldWord P w D (page D F)=∑ i:Chunk h,jotC P w F i:=by
    rw [Fintype.sum_option]; unfold jotC; rw [map_sub, observed,flower_hint,map_sum]; simp_rw [map_smul]; exact Eq.symm (sub_add_cancel ..)
lemma chunk_prep (j:Chunk h)(p:h<D): ∃ C:ℝ, 0≤ C∧ ∀ (P:Patch)(w:Site P.L)(F:Scroll D), ‖jotC P w F j‖≤C*(speck P^(rateC j)* ‖page D F‖):=by
    cases j with
    | none=> exact ⟨4^(h+1),by positivity,fun P w F=>tiling P w F p⟩
    | some i=> exact ⟨‖wallope i.val D‖,norm_nonneg _,fun P w F=> by unfold jotC; rw [norm_smul,mul_comm]; exact mul_le_mul_of_nonneg_left (halo_bound P w F i.val (le_trans i.property p.le)) (norm_nonneg _)⟩
lemma portion_rug (G:Gauge)(D h:ℕ)(r:ℕ)(i: Fin r→Fin (h+2))(C s η:ℝ)(p:0<s)(q:0<η) : ∃ T:ℝ, 0≤ T∧∀ (P:Patch)(Q:Drip P G)(w:Site P.L)(x:Fin r→YForest G)(Y:ChamberTen G (Vote D) r)(A:ℝ), Crank Q (h+1) s C → r*(s/P.L.val)≤η/2 → Twig 0 η A Y→
    ‖pluck Y (fun j=>splint P Q w (x j) (h+1) (i j))‖≤ T*A*(speck P)^(mMarked i)*Real.exp (-s*port_d 0 x):=by
   obtain ⟨B,hb,H⟩:=break_money G (h+1) s p
   by_cases g:0≤ C; swap; · exact ⟨0,le_rfl,fun _ _ _ _ _ _ h=> (g h.1).elim⟩
   let z:= η/2; have hv: z<η:=by unfold z; linarith
   let n:= (h+1)*r; let V:=ceilPoly n ((η-z)/2); let E:=tiePay (Hooks G) r ((η-z)/2)
   have he :0≤E:=by
      by_cases hx:r=0; · simp [E,tiePay,hx]
      exact pow_nonneg (boardPay_nn (by positivity)) r
   have he':0≤ V:= (ceilPoly_pos ..).le
   refine ⟨(B*C)^r*V*E,by positivity,fun P Q w x Y A b u a=>?_⟩
   let f (j:Fin r):= splint P Q w (x j) (h+1) (i j); let W(y:Fin r→YForest G):= pressOn Y f y; let K:=(B*C)^r*(speck P)^(mMarked i)*Real.exp (-s*port_d 0 x); have hK : 0≤ K:= by unfold K; positivity [speck_pos P]
   have ht:= cap_scale (shrub _ Y a hv n) hK
   have he y: ‖W y‖≤K* (Purl z n (port_d 0 y)*‖Y y‖) := by
       have hg :‖(∏ j,f j (y j))‖≤∏ j,rentM P s (B*C) ((i j).val+1) (x j)*Purl (s/P.L.val) (h+1) (size (y j).1):=by
          rw [norm_prod]; exact Finset.prod_le_prod (fun _ _=> norm_nonneg _) (fun j _=> H P Q C b w (x j) (i j) (y j))
       unfold W; rw [pressOn,norm_smul,←mul_assoc]; refine mul_le_mul_of_nonneg_right (hg.trans ?_) (norm_nonneg _); rw [Finset.prod_mul_distrib]; exact mul_le_mul (term_money P s (B*C) p.le (by positivity) x i) (term_remainder (h+1) y (by positivity) u) (Finset.prod_nonneg (fun _ _=>by unfold Purl; positivity)) hK
   have hg:= budget_minor ht (fun y=>norm_nonneg (W y)) he
   exact (norm_tsum_le_tsum_norm hg.2.1).trans (hg.2.2.trans_eq (by unfold K V E; ring))
lemma tumbles (F:Labels.Frame G h)(H:Hol G) (i: Fin r→Fin (h+2))(b: Embroider.Spiral h)(e:mMarked i+b.val.card≤h)(D:ℕ)(s C:ℝ)(p:0<s)(ht:0<t):
    ∃ T:ℝ,0≤ T∧∀ (P:Patch)(w:Site P.L)(Q:Drip P G)(x:Fin r→YForest G)(Y:ChamberTen G (Vote D) r)(A M:ℝ), Crank Q (h+1) s C→Smooth Y→ mural Y→ Twig 0 t A Y→ Wing 0 t M Y→ Hears F h M Y →
       ‖pluck Y (fun j=> splint P Q w (x j) (h+1) (i j)) (wallope b.val D)‖≤ T*M*Real.exp (-s*port_d 0 x):=by
    by_cases c:0≤C; swap; · exact ⟨0, le_rfl,fun _ _ _ _ _ _ _ H=> (c H.1).elim⟩
    let n j:= 1+(i j).val
    obtain ⟨T,hT,hp⟩:= laurels H F n b.val e le_rfl D ht
    choose E hE hu using fun j=> break_charge G (i j).val
    let B:= ∑ i,E i; have hB :0≤ B:= Finset.sum_nonneg (fun i _=>hE i)
    refine ⟨T*(B*C)^r,by positivity,fun P w Q x Y A M g a v u l k=>?_⟩
    let f j:= breaks P Q w (x j) (i j).val
    have he (j:Fin r): (i j).val<h+1:=by
        have hx: n j≤ h:= (Finset.single_le_sum (s:=Finset.univ) (f:=n) (fun _ _=>Nat.zero_le _) (Finset.mem_univ j)).trans ((Nat.le_add_right _ _).trans e); unfold n at hx; omega
    have hx j: f j∈rangeLt _ (n j):=by unfold n; rw [add_comm]; exact breaks_in P Q w (x j) _
    simp_rw [splint,if_pos (he _)]; refine (hp Y A M u v a k l f hx).trans ?_; have hh:= Wing.pn l
    have H : (∏ i, slideRank (n i) (f i))≤ (B*C)^r*Real.exp (-s*port_d 0 x):=by
       refine (Finset.prod_le_prod (s:= Finset.univ) (fun _ _=> slide_nn _ _) (fun j _=> (show slideRank (n j) (f j)≤ rentM P s (B*C) ((i j).val+1) (x j) from ?_))).trans ((term_money P s (B*C) p.le (by positivity) x i).trans ?_)
       · unfold n; rw [add_comm]; apply (hu j P (h+1) C s Q (he j).le g w _).trans; unfold rentM; have hg:E j ≤ B:= Finset.single_le_sum (fun i _=> hE i) (Finset.mem_univ j); have := speck_pos P; gcongr
       gcongr; exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (speck_pos P).le (speck_le P))
    exact (mul_le_mul_of_nonneg_left H (by positivity)).trans_eq (by ring)
end YM.WilsonCoeffUV.Cosmos
