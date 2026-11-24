import YM.WilsonCoeffUV.Product.I.Evaluated
/-!
# Conditional I before capture (no engineering scaling)

Era uses evaluated profiles with a single physical center, support relative to
capture/reference; permits amplitude vectors, explicitly retaining evaluation
at the SAME center of all factors. Careful: not claiming arbitrary sup-multi
estimated by sup-center products (when using separation gains).
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.WilsonCoeffUV.Mer
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Exterior Next.Free Tree Precision Power Embroider Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm Fountain PathCost Embroider.Canvas Shard PowerSeries
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n c:Side}{U α β V W E W' ι : Type*}{r h D k j l m e i:ℕ} {A:ℝ}{G:Gauge}

lemma coat0 (n:Side): lift (0:Site n)=(0:Cover):=by ext; simp [lift]

section
variable {N:ℕ}[NormedAddCommGroup V][NormedSpace ℝ V][NormedAddCommGroup W][NormedSpace ℝ W]
lemma bend_mixX {P:(n:Side)→Parcelized V G n} {Q: Bookend V G}(p:∀ i r,Bends 0 (fun n=>P n i r) (Q i r)) (A:Cost)(i r) : Bends 0 (fun n=>Blue.mix A (P n) i r) (Blue.mix A Q i r):=by
    simp_rw [Blue.mix]; exact anzas (P:=fun k n=>coeff (i-k) (A^k*(A⁻¹)^r) • P n k r) (Finset.range (i+1)) (fun i _=> Soil.Bends.μ (p ..) _)
lemma ply_mixX {P: Pal V U}(A:Cost)(L:V→ₗ[ℝ]W): ply L (Blue.mix A P)= Blue.mix A (ply L P):=by ext1 i; funext v x; rw [ply_v]; simp_rw [Blue.mix, Finset.sum_apply,Pi.smul_apply,map_sum,map_smul]; rfl

def verseI (A:Levels G)(Ñ:ChartRatio G)(m N k:ℕ)(P:Era G V): Era G V:=
 (fun n=> let p:=ll A m; let T:=freeForms A N (m+1); let K:= A.clock.kernel; let F:=(story A Ñ N (m+1)).1 (n*p.L); Blue.mix (ratioHigh A Ñ N m) (reed (stepAt p K n) (xree p K n) T (roam A N m n) Ñ F k (P.1 (n*p.L))), Blue.mix (ratioHigh A Ñ N m) (windsT (ll A m) A.clock.kernel Ñ (shuttleM (conditional A N m)) (shuttleM (feedA A N m)) (actionW A Ñ N (m+1)) k P.2))
variable [CompleteSpace V]
lemma Auth.verse (A:Levels G){Ñ:ChartRatio G} (p:m<N)(g:G.Simple)(q:LocalRatio Ñ){P:Era G V}(h:Auth k P): Auth k (verseI A Ñ m N k P):=by
   let t:= ll A m; let K:= A.clock.kernel; let G':=freeForms A N (m+1); let V':=freeForms A N m; let M:= roam A N m; let Y n:= (story A Ñ N (m+1)).1 (n*t.L); let R (n:Side):= reed (stepAt t K n) (xree t K n) G' (M n) Ñ (Y n) k (P.1 (n*t.L)); let b:=ratioHigh A Ñ N m
   have he:= old A Ñ g q N (m+1) p; have ht n: shellK k (R n):= reed_band _ _ _ _ k (he.basis _).lamp q (h.span _)
   refine ⟨fun i r=> bend_mixX (P:=R) (fun i r=>?_) b i r,fun n=> mix_length (ht n),fun n i=> mix_pure (P:=R n) (fun i=>reed_smooth _ _ _ _ k Ñ _ (h.pale _) i) i,fun n s=>?_⟩
   · exact river t K Ñ _ _ _ (A.blocks m 0).branches q (resin A N m p) he.patch k 0 (U:=P.1) (fun i r=>by rw [coat0]; exact h.wing i r) i r
   intro Z I z x x' H; rw [show ply s ((verseI A Ñ m N k P).1 n)= Blue.mix b (ply s (R n)) from ply_mixX ..]; refine rollMix ?_ (ply_shell s (ht n)) (ply_shell s (ht n)) (back_cc (angle_tilt g q p)) H
   have hu: ply s (R n)= reed _ _ _ _ Ñ (Y n) k (ply s (P.1 (n*t.L))):= reed_maps _ _ _ _ k s
   intro Z I z x x' H; rw [hu];
   have hQ:= he.basis (n*t.L)
   apply reed_turn (stepAt t K n) (xree t K n) _ (M n) V' hQ.lamp hQ.stem q _ (ply_shell _ (h.span _)) (ply_shell _ (h.span _)) (A.blocks m 0).branches (age_sym A ..) hQ.shape (fun i=> ply_pure _ (h.pale _ i)) (fun i=> ply_pure _ (h.pale _ i)) ((cond_laws A m N).1 n (n*t.L) rfl) (horizon_step A m N p n _ rfl) hQ.valid _ H
   rw [show (stepAt t K n).ratio.embed 0=0 from map_zero (stepAt t K n).ratio.root]; exact h.token (n*t.L) s
lemma ply_verse [CompleteSpace W] (A:Levels G){Ñ:ChartRatio G}(p:m<N)(g:G.Simple)(q:LocalRatio Ñ){P:Era G V}(h:Auth k P)(R:V→L[ℝ]W): tuftV R (verseI A Ñ m N k P)=verseI A Ñ m N k (tuftV R P):=by
   apply Auth.ext ((Auth.verse A p g q h).tuft _) (Auth.verse A p g q (h.tuft _))
   funext n; let K:= ll A m; let B:=A.clock.kernel; let u (Z:Era G V):=reed (stepAt K B n) (xree K B n) (freeForms A N (m+1)) (roam A N m n) Ñ ((story A Ñ N (m+1)).1 (n*K.L)) k (Z.1 (n*K.L)); let x:=ratioHigh A Ñ N m
   change ply R.toLinearMap (Blue.mix x (u P))= _; rw [ply_mixX]; exact congr_arg (Blue.mix x) (reed_maps _ _ _ _ k R.toLinearMap (w:=P.1 (n*K.L)))
-- truncated shell restriction, avoiding reassociation bookkeeping in product.
lemma verseExpand (A:Levels G){Ñ:ChartRatio G}(p:m<N)(g:G.Simple)(q:LocalRatio Ñ){P:Era G V}(h:Auth k P)(e:k≤l) : verseI A Ñ m N k P=verseI A Ñ m N l P:=by
   apply Auth.ext (Auth.verse A p g q h) (Auth.verse A p g q (h.tall e)); funext n
   let K:= ll A m; let X:=A.clock.kernel; let B:=ratioHigh A Ñ N m; let W j:= reed (stepAt K X n) (xree K X n) (freeForms A N (m+1)) (roam A N m n) Ñ ((story A Ñ N (m+1)).1 (n*K.L)) j (P.1 (n*K.L))
   change Blue.mix B (W k)= Blue.mix B (W l); congr 1; funext i; apply congr_arg (fade plug); apply Finset.sum_subset (by apply Finset.range_mono; omega); intro j hj h'; funext r; have ht:¬j<1+k+3*i:=by simpa only [Finset.mem_range] using h'
   exact srStops _ _ _ _ k ((old A Ñ g q N (m+1) p).basis _).lamp q (h.span _) j i r (Or.inr (by omega))
private lemma verseWalk (A:Levels G){Ñ:ChartRatio G}{P:U→ Era G V}[Fintype U] (g:G.Simple)(p:m<N)(q:LocalRatio Ñ)(h:∀ i,Auth k (P i))(d:U→ℝ): verseI A Ñ m N k (∑ i,d i • P i)=∑ i,d i • verseI A Ñ m N k (P i):=by
   apply Auth.ext (Auth.verse A p g q (Auth.sum (S:=Finset.univ) (fun i _=>(h i).μ (d i)))) (Auth.sum (S:=Finset.univ) (fun i _=>(Auth.verse A p g q (h i)).μ (d i))); funext n
   let t:= ll A m; let K:=A.clock.kernel; let V i:= reed (stepAt t K n) (xree t K n) (freeForms A N (m+1)) (roam A N m n) Ñ ((story A Ñ N (m+1)).1 (n*t.L)) k ((P i).1 (n*t.L)); let X:= ratioHigh A Ñ N m
   simp only [verseI,Prod.fst_sum,Finset.sum_apply,Prod.smul_fst,Pi.smul_apply]; rw [raft]; funext i j; change Blue.mix X (∑ i,d i • V i) i j=(∑ i,d i • Blue.mix X (V i)) i j; simp_rw [Blue.mix,Finset.sum_apply,Pi.smul_apply,Blue.mix,Finset.smul_sum]; rw [Finset.sum_comm]; exact Finset.sum_congr rfl (fun i _=> Finset.sum_congr rfl (fun _ _=> smul_comm ..))
lemma verse_sum (A:Levels G){Ñ:ChartRatio G}{P:U→ Era G V}(g:G.Simple)(p:m<N)(q:LocalRatio Ñ){S: Finset U}(h:∀ i∈ S,Auth k (P i))(d:U→ℝ): verseI A Ñ m N k (∑ i∈ S,d i • P i)=∑ i∈S,d i • verseI A Ñ m N k (P i):= by
    have hv:= verseWalk A g p q (P:=fun i:S=>P i.val) (fun i=> h _ i.property) fun i=> d i.val; rw [←Finset.sum_attach S (fun i=> d i • P i),←Finset.sum_attach S (fun i=>d i • verseI A Ñ m N k (P i))]; exact hv
lemma verse_lin (A:Levels G){Ñ:ChartRatio G}{P Q:Era G V}(g:G.Simple)(p:m<N)(q:LocalRatio Ñ)(h:Auth k P) (v:Auth k Q): verseI A Ñ m N k (P-Q)=verseI A Ñ m N k P-verseI A Ñ m N k Q:= by
   have hp(i:Fin 2): Auth k (![P,Q] i):=by fin_cases i; exact h; exact v
   simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, head_cons, Matrix.cons_val_fin_one,one_smul,neg_one_smul,sub_eq_add_neg] using verseWalk A g p q hp ![(1:ℝ),-1]
end
end YM.WilsonCoeffUV.Mer
