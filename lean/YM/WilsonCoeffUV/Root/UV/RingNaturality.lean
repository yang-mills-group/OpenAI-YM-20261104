import YM.WilsonCoeffUV.Root.UV.RawSemi
/-!
# PathProof. Raw imprint semilinearity (finite and cover via Bends). Supplies forward equality after reset. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n f:Side}{U V:Type*}{r h D l e j k a N M m b i:ℕ} {G:Gauge}{F:Labels.Frame G h}{H:Hol G}
lemma affix_μ [AddCommGroup U][Module ℝ U](A:Cost)(c:ℝ)(P:Pal U V): affix A (c•P)=c• affix A P:=by ext1 i; simp only [affix, Pi.smul_apply,Finset.smul_sum]; exact Finset.sum_congr rfl fun i _=> smul_comm ..
lemma lootT {V:Type*}{E:Type}[AddGroup E](P:Patch)(k:Site P.L)(p:E)(A:Cost)(Y:Pal (Vote D) (E×V)): gatherT P k p (affix A Y)= affix A (gatherT P k p Y):=by funext i r x; simp only [gatherT, revolve, Function.comp_apply,affix,Finset.sum_apply,Pi.smul_apply,map_sum,map_smul]
variable (A:Levels G)(Ñ:ChartRatio G)
lemma ropeT (Y:Vell G (n*(ll A m).L) D)(T:Cost)(g:G.Simple)(p:m<N)(hj: LocalRatio Ñ)(hs:shellK h Y)(ht:∀ i,Pure (Y i)) : cloakP A Ñ N m h n (affix T Y) = affix (Bank.reel (ratioHigh A Ñ N m) T) (cloakP A Ñ N m h n Y):=by
    let P:= ll A m; let s:=A.clock.kernel; let k:= n*P.L; let V:= (old A Ñ g hj N (m+1) p).basis k
    let B:= ((story A Ñ N (m+1)).1 k); let H:= freeForms A N (m+1); let X:= roam A N m; let ν:=collarT P s Ñ H X h D (n:=n) B
    have hx w : bellOne P s Ñ H X h D (n:=n) w B (affix T Y)= affix T (bellOne P s Ñ H X h D w B (n:=n) Y):= by unfold bellOne; rw [lootT]; apply reedAcross _ _ _ _ _ _ _ _ _ hj; exact (A.blocks m 0).branches; exact age_sym A ..; exact gather_mark _ _ _ _ hs; exact fun i=> gather_pure _ _ _ _ (ht i); exact V.lamp; exact V.shape
    unfold cloakP; rw [show collarT _ _ _ _ _ _ _ _ _= _ from (show ν (affix T Y)= affix T (ν Y) from (by unfold ν collarT; simp_rw [affix_μ, affix_sum,hx]))]; apply mixAcross; exact pin_test P s Ñ H X h h hj _ _ V.lamp hs; exact pin_valid P s Ñ H X h _ _ ht
lemma masking_port {P: Island F D}(i:Side): (Cosmos.descend A Ñ N m P).1 i= fun j=> cloakP A Ñ N m h i (P.1 (i*(ll A m).L) j):=rfl
lemma bender {P: Island F D}(u: Coil F)(v:Chain F P.1 P.2)(g:G.Simple)(p:m<N)(hj:LocalRatio Ñ): Cosmos.descend A Ñ N m (imprint P u) = imprint (Cosmos.descend A Ñ N m P) (Chars F (ratioHigh A Ñ N m) u):=by
    let V:= ratioHigh A Ñ N m; let K:= ll A m; let Q:= imprint P u; let X:= Cosmos.descend A Ñ N m Q; let R:= Cosmos.descend A Ñ N m P; let B:= imprint R (Chars F V u)
    -- shell may arbitrary slot after A not trample, but ≤h. propagates. spirit not needed.
    have hx : X.1=B.1:=by
       funext n i; change cloakP A Ñ N m h n (∑ k',affix (u k' i) _) = ∑ k',affix _ _; have hf : ∑ k':Alma F, affix (u k' i) (P.1 (n*K.L) k') = ∑ k':Alma F, (1:ℝ) • affix (u k' i) (P.1 (n*K.L) k'):=by simp
       change cloakP A Ñ N m h n (∑ k':Alma F, affix (u k' i) _) = ∑ k:Alma F,_; rw [hf, cloakP_sum]; refine Finset.sum_congr rfl fun i' _=>?_; rw [one_smul]; let S:=v.solo i'; exact ropeT A Ñ _ (u i' i) g p hj (shell_mon (S.launch (n*K.L)) (valence_cap ..)) (S.evenS _)
    have hQ (i:Alma F) j r : Bends 0 (fun n=>Q.1 n i j r) (Q.2 i j r):= by
       unfold Q imprint impose; dsimp only; simp only [affix, Finset.sum_apply]; apply anzas (P:=fun k (n:Side)=>∑ j'∈Finset.antidiagonal j, coeff j'.1 (u k i) • P.1 n k j'.2 r); exact fun k _=> anzas (P:=fun (j':ℕ×ℕ) (n:Side)=>coeff j'.1 (u k i) • P.1 n k j'.2 r) _ (fun j' _=> ((v.solo k).shore j'.2 r).μ _)
    let T:= (story A Ñ N (m+1)).1; let s:=A.clock.kernel; let H:= freeForms A N (m+1); let L:=roam A N m
    have hX (i:Alma F) j r:Bends 0 (fun n=>X.1 n i j r) (X.2 i j r):=by
       apply whirlB (P:=fun n=> collarT K s Ñ H L h D (n:=n) (T (n*K.L)) (Q.1 (n*K.L) i)); intro w h'; exact bells_period K s Ñ H L h (A.blocks m 0).branches hj (old A Ñ g hj N (m+1) p).patch (resin A N m p) (U:=fun n=> Q.1 n i) (hQ i) w h'
    have he: Chain F R.1 R.2:= running A Ñ p g hj v
    have hB (i: Alma F) j r: Bends 0 (fun n=>B.1 n i j r) (B.2 i j r):=by
       let M:= Chars F V u; change Bends 0 (fun n=> impose (R.1 n) M i j r) (impose R.2 M i j r); simp only [impose,Finset.sum_apply,affix]; exact anzas (P:=fun k (n:Side)=>∑ j'∈Finset.antidiagonal j,coeff j'.1 (M k i) • R.1 n k j'.2 r) _ fun k _=> anzas (P:=fun (j':ℕ×ℕ) (n:Side)=> coeff j'.1 (M k i) • R.1 n k j'.2 r) _ (fun j' _=> ((he.solo k).shore j'.2 r).μ _)
    refine Prod.ext hx (funext fun i=> funext fun j=> funext fun k=>?_); change X.2 i j k= B.2 i j k; rw [hx] at hX; exact (hX i j k).exten (hB i j k)
end YM.WilsonCoeffUV.Cosmos
