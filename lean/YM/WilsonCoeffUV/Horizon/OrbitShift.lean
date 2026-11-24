import YM.WilsonCoeffUV.Horizon.TurnLayouts
/-! # Root translations over the same Ward model

All cover algorithms may keep the capture center fixed at zero using these
identities. This symmetry refers to coarse native roots. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Motion
open Wheel.ScaleS Wheel.Mark Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Shard Realm PathCost Physical
open Fountain Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Wheel.Flooring Ticket
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {ι:Type}{S:Finset ι}{E W V:Credit}{m b N e h D' i a:ℕ}{G:Gauge}{A:Levels G}{R:Realm G (e+1) E}{Ñ: ChartRatio G}{T:ι→SealR G}{P:Patch}{n:Side}{u:Cover}{D K k:ι→ℕ}
variable {H:Hol G}
variable [DecidableEq ι]
def raised0 (w:Cover)(X:family G D): family G D:=fun S=>shifted (X S) w
abbrev steppedC (w:Cover)(p:ι → Cover):=fun i=> w+p i
def ramble (w:Cover)(X:Outerm G D):Prop:=∀ p,X (steppedC w p)=raised0 w (X p)
omit [DecidableEq ι] in
lemma transportPage (T: Era G (Pen D S))(p:Auth i T)(x:Cover)(A:Case D): readO A (shifted T x) n=loom (spear (jog (wrap n x) : Equiv.Perm (Woods G n))) (readO A T n):=by unfold readO; let w:= wrap n x; rw [show pPly A S ((shifted T x).1 n) = skewV w (pPly A S (T.1 n)) from ply_skew ..]; exact translate_value n w _ (ply_shell (touch A S).toLinearMap (p.span n))
lemma composed0 (P:family G D)(p:Eu k P)(w:P ∅=0)(d:Cover): levelsO (raised0 d P)=raised0 d (levelsO P):=by
    let Z:=raised0 d P; have he: Eu k Z:= fun i=>(p i).shifted _; have hv: Z ∅=0:=by unfold Z raised0; rw [w]; rfl
    funext S; apply read_ext _ _ (placedO _ he S) ((placedO P p _).shifted _); intro A n
    let K:= spear (jog (wrap n d) : Equiv.Perm (Woods G n)); let T s:= feeble Z A n s; have h:=levels_exp Z he hv A n; have hz:= levels_exp P p w A n; have ht j: T j=loom K (feeble P A n j):=transportPage (P j) (p j) d A
    have hQ:= mapEquation _ _ (loom K) hz; rw [← show T=(fun j=>loom K (feeble P A n j)) from funext ht] at hQ
    rw [transportPage _ (placedO _ p _)]; exact congr_fun (Equation.prod_u _ _ _ h hQ) S
lemma recovered0 (P:family G D)(p:Eu k P)(Q Z:family G D)(q:Eu k Q)(z:Eu k Z)(x:Q ∅=puff D G)(y:Z ∅=puff D G)(T:Cover)(hx:Q=raised0 T Z)(g:P=reverseO Q): P=raised0 T (reverseO Z):=by
    subst P; funext S; apply read_ext _ _ (p S) ((counted _ z _).shifted _); intro A n
    let K:= spear (jog (wrap n T) : Equiv.Perm (Woods G n)); have he:= levels_log Z z y A n; have hV:= mapEquation _ _ (loom K) he
    have hv: feeble Q A n=(fun j=>loom K (feeble Z A n j)):=funext fun j=> (by rw [hx]; exact transportPage _ (z _) _ A)
    rw [←hv] at hV; rw [transportPage _ (counted _ z _)]; exact congr_fun (Equation.unique _ _ _ (levels_log Q q x A n) hV) S
lemma alongShift {M:Outerm G D}(r: Wellness k M)(q:m<N)(g:G.Simple)(v:LocalRatio Ñ)(f:ramble ((A.S.block m).val • u) M)(p:ι→ Cover): logO A Ñ m N (M (steppedC ((A.S.block m).val • u) p)) k=raised0 u (logO A Ñ m N (M p) k):=by
    let w:= steppedC ((A.S.block m).val • u) p; apply recovered0 _ (step_L _ _ _ _ _ _ q g v (r.level' w)) _ _ (vol _ _ _ _ _ _ q g v (r.level' w)) (vol _ _ _ _ _ _ q g v (r.level' p)) (edV_e _ _ _ _ _ _ q g v) (edV_e _ _ _ _ _ _ q g v) u _ rfl
    unfold w; rw [f p]; funext S; unfold edV; rw [composed0 _ (r.level' p) (r.quiet' p)]; exact outing _ q g v (placedO _ (r.level' p) _) u
lemma splitStep (w:Cover)(p:ι → Cover)(X: backRow P.L S): splitQ P (steppedC w p) S X=steppedC (P.L.val • w) (splitQ P p S X):=by
    funext i; change P.L.val • (w+p i) +_ = P.L.val • w+(P.L.val • p i+_); rw [nsmul_add,add_assoc]
omit [DecidableEq ι] in
lemma shiftedSum {U V: Type}[NormedAddCommGroup V][NormedSpace ℝ V] (w:Cover)(F:U→ Era G V)(A: Finset U): shifted (∑ i∈A,F i) w=∑ i∈A,shifted (F i) w:=by
    apply Prod.ext
    · funext n i j x; dsimp only [shifted,skewV,revolve]; simp_rw [Prod.fst_sum, Finset.sum_apply]; rfl
    funext i j x; dsimp only [shifted,skewV,revolve]; simp_rw [Prod.snd_sum,Finset.sum_apply]; rfl
lemma rambleStep {M:Outerm G D}(r:Wellness k M)(q:m<N)(g:G.Simple)(v:LocalRatio Ñ)(f:ramble ((A.S.block m).val • u) M): ramble u (stout A Ñ m N K k M):=by
   intro p; funext S; unfold stout unite raised0; rw [shiftedSum]; apply Finset.sum_congr rfl; intro i _; unfold portV; rw [splitStep]; dsimp only; rw [show logO A Ñ m N (M (steppedC ((ll A m).L.val • u) (splitQ _ _ _ _))) _= _ from alongShift r q g v f (splitQ (ll A m) p S i)]; rfl
lemma rising (X:Outerm G D)(t:m≤ b)(z:b≤ N)(q:G.Simple)(v:LocalRatio Ñ)(u:Wellness k X)(h:∀ w,ramble w X): ∀ w,ramble w (Gears A Ñ K k N b m X):=by
    induction t using Nat.decreasingInduction with
    | self=> rw [gearTop]; exact h
    | of_succ m hp ih=> intro w; rw [gearUp A Ñ X hp]; exact rambleStep (Cog _ _ z X u q v hp) (hp.trans_le z) q v (ih _)
lemma coatShift (u:Cover)(X:(i:ι)→ Verse (T i).F): ramble u (coatA A Ñ N m T X):=by
    intro p; funext S; unfold raised0; by_cases e:S.card=1
    · obtain ⟨i,rfl⟩:= Finset.card_eq_one.mp e; rw [coatLeaf,coatLeaf,cn,steppedC, shifted_add]; rfl
    rw [coatLazy _ _ _ _ _ _ _ _ e,coatLazy _ _ _ _ _ _ _ _ e]; rfl
theorem allShifts (L: Tribe R H W V T)(X:(i:ι) → Verse (T i).F)(u:R.anchor ≤ m)(v:m≤ N)(q:b≤N):
     let p i:=(T i).h; let P:=Gears R.draws R.paid p p N N b (coatA R.draws R.paid N m T X); (∀ w,ramble w P)∧∀ w,ramble w (AuthSum P) :=by
    intro p P; have ht:=cloister L X u v; have he:∀ w,ramble w P:= rising _ q le_rfl R.hG R.green ht (fun w=>coatShift w X); refine ⟨he,fun w s=>?_⟩
    have hv: Wellness p P:= Cog _ _ le_rfl _ ht R.hG R.green q; unfold AuthSum; rw [he w]; exact composed0 (P s) (hv.level' s) (hv.quiet' s) w
end YM.WilsonCoeffUV.Wheel.Motion
