import YM.WilsonCoeffUV.Product.Connected.Miss
/-!
# Period calculus for join
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Gauge Power PathCost Precision Embroider Fountain Cosmos Shard Realm
open PowerSeries
open scoped Topology BigOperators
variable {n c:Side}{U V α β:Type*}{r h D j e i l k:ℕ}{A B C s:ℝ}{G:Gauge}
section
open Wilson Tree AnalyticNext.QuarticMatch.Sheets Exterior
open Embroider Precision PathCost Gauge
variable (P:Patch)(K:KernelChoices)(Ñ:ChartRatio G)(H:FaceRow)(Q:(n:Side)→Matrix (Body 1 (n*P.L)) (Body 1 n) ℝ)(Γ:ropes Cover (Larvae G P.L) (Larvae G P.L))(M:ropes Cover (Larvae G P.L) (Hooks G))(W:Canvas G)

def boilC (X Y:Bookend ℝ G):= gorge (stair (β:=Hooks G) (upper (β:=Hooks G) Γ 0) 0) (spurs P K Ñ Γ M W) (puck P K Ñ Γ M W X) (puck P K Ñ Γ M W Y)
abbrev hotC (k:ℕ)(X Y: Bookend ℝ G) (e:ℕ): Gen ℝ (Cloth (Hooks G)):= sluice (finallyA k (boilC P K Ñ Γ M W X Y) e)
variable {Γ M W Q H}
lemma gorgeThermo (b:P.Branches K G)(t:LocalRatio Ñ)(g:PaintKit P K G H Q Γ M){F:Crude G} (z:∀ n,Interlace H (F n))(e:∀ i r,Yields (fun n=>F n i r) (W i r)) (X Y:Era G ℝ)(p:Auth i X)(q:Auth j Y)(i k r:ℕ):
    Bends 0 (fun n=>bend (weaveH (ratioN P.L n) G) (boiling (stepAt P K n) (xree P K n) H (Q n) Ñ (F (n*P.L)) (X.1 (n*P.L)) (Y.1 (n*P.L)) i k) r) (boilC P K Ñ Γ M W X.2 Y.2 i k r):=by
   let O (n:Side):= xree P K n; let s (n:Side):= stepAt P K n; let I n:= weaveFine (ratioN P.L n) G; let T n:= weaveH (ratioN P.L n) G; let R (n:Side):= teller G P K Q n; let Z (n:Side):= F (n*P.L); let U (n:Side) := fillSlots (Woods G n) (mer P K H n (G:=G)); let d n:=xray (s n) (O n) H (Q n) Ñ (Z n); let u (n:Side) := allotM (T n) (T n) (U n); let V':= stair (α:=Larvae G P.L) (β:=Hooks G) (upper (β:=Hooks G) Γ 0) 0
   let J (L:Era G ℝ)(n:Side) := srCold (L.1 (n*P.L)) (R n); let A n:= J X n; let B n:=J Y n; let W':=spurs P K Ñ Γ M W; let X':=puck P K Ñ Γ M W X.2; let Y':=puck P K Ñ Γ M W Y.2; let Q' n:=boiling (s n) (O n) H (Q n) Ñ (Z n) (X.1 (n*P.L)) (Y.1 (n*P.L)); let V:=boilC P K Ñ Γ M W X.2 Y.2
   have ht : Pilots u V':=by
      rw [show u=fun n:Side=> stair (upper (allotM (I n) (I n) (mer P K H n (G:=G))) (β:=Hooks G) 0) (β:=Hooks G) 0 from funext fun n=>lamp_chart ..]; exact ((g.toll.deck (Pilots.silent (β:=Hooks G))).deck' (Pilots.silent (α:=Hooks G)))
   let T' n j k:=bend (T n) (d n j k)
   have hv a j r:Yields (fun n=> T' n a j r) (W' a j r):=spurs_enter P K Ñ H F Q b t e g a j r
   let dV n (v:Pal ℝ (Joint G (n*P.L) n)) a j:= bend (T n) (bul (U n) (d n) v a j)
   have hx L l (p:Auth l L) (a j r:ℕ): Bends 0 (fun n=>dV n (J L n) a j r) (puck P K Ñ Γ M W L.2 a j r):=by
      let Y n (a):= bend (T n) (J L n a)
      have he i r:Bends 0 (fun n=> Y n i r) (slidesJ P M L.2 i r):=by
         have hφ:Bends (lift (0:Site P.L)) (fun n=> L.1 n i r) (L.2 i r):=by rw [coat0]; exact p.wing i r
         apply Bends.congr (solo_flash (P:=tiles P.L (L.2 i)) (Q:=fun n=>bend (I n) (L.1 (n*P.L) i)) (Pilots.one.deck g.mark) (hφ.ciphers 0))
         refine Eventually.of_forall fun n=>?_ ; unfold Y J srCold; rw [bend_fade (I n) (T n), show allotM (I n) (T n) _=upper 1 _ from cam_chart _ _]
      exact (heap_period ht hv he a j r).congr (Q:=fun n=>dV n (J L n) a j r) (Eventually.of_forall fun n=> congr_fun (sprint (T n) (U n) (d n) (J L n) a j).symm r)
   let A' n:=dV n (A n); let B' n:=dV n (B n); let S (n:Side) i j:=bend (T n) (Q' n i j)
   change Bends 0 (fun n=> S n i k r) (gorge V' W' X' Y' i k r)
   induction i using Nat.strong_induction_on generalizing k r with
   | h i ih=>
     cases i with
     | zero=>
        rw [gorge]; apply Soil.Bends.congr Bends.zero; refine Eventually.of_forall fun n=>?_ ; unfold S Q' boiling; rw [estuary_base]; rfl
     | succ i=>
        have hY (n:Side): S n (i+1) k=((i+1:ℕ):ℝ)⁻¹ • (ripple (u n) (S n i k)+ ravel (u n) (T' n) (S n) i k+ravel (u n).transpose (T' n) (S n) i k+ravel (u n) (A' n) (B' n) i k+ravel (u n).transpose (A' n) (B' n) i k):=by
           have hZ: Interlace H (Z n):= z _; let D:=F (n*P.L)
           have he: ∀ h e r,r>2+e ∨ r+2*h>3*e → (d n) h e r=0:= span_abr (U n) (pack_band (s n) hZ.lamp) (pack_zero (s n) t)
           have hm h e : Pure (d n h e):= pure_abr _ (pack_pure (s n) t b hZ.shape) h e
           have hf:= estuary_next (U n) (d n) (A n) (B n) he (fade_shell (camber G _) (p.span _)) (fade_shell (camber G _) (q.span _)) hm (fun i=> fade_pure (p.pale _ i) _) (fun i=> fade_pure (q.pale _ i) _) i k
           change bend (T n) (estuary (U n) (d n) (A n) (B n) (i+1) k)=_; dsimp only at hf; rw [hf,bend_smul]; congr 1; simp only [bend_add,bend_ripple,bend_ravel]; rfl
        rw [riseG]
        let ha {M Z} (z:Pilots M (Z:ropes Cover (Hinge G P.L) (Hinge G P.L))):= spans_bracket (P:=S) (R:=gorge V' W' X' Y') (Q:=T') z (v:=i) (e:=k) (fun _ _ _ _ _=>hv ..) (fun j l k _ r=> ih j (by omega) ..) r
        have hI:= ih i (by omega) k (r+2)
        have hR:= rime_period (Q:=fun n=>S n i k) (P:=gorge V' W' X' Y' i k) ht hI; simp_rw [hY]; exact (((((hR.add (ha ht)).add (ha (capit ht))).add (tow_ravel (P:=A') (Q:=B') ht (hx X _ p) (hx Y _ q) i k r)).add (tow_ravel (P:=A') (Q:=B') (capit ht) (hx X _ p) (hx Y _ q) i k r)).μ (((i+1:ℕ):ℝ)⁻¹))
end
end YM.WilsonCoeffUV.Mer
