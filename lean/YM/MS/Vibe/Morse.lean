import YM.MS.Vibe.Kind
/-!
# Limit singular carrier at naked-t vertex

Classical seeds independent of ζ; equality tested on all stable dimensions. Optional off Course extensions.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Emit
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train Dock
open Signal Book Convolve Garment.Wave Garment.Wick
open scoped Topology ContDiff Interval
variable {I:Type}{G:Gauge}{X Y F: T (Flats G)}{J N L:Flats G}{f g p:T (Coat G)}{b c:Bool}{t r:ℤ}{a h n m k ℓ:ℕ}{i:ℂ}{s y:ℝ}
abbrev plainQ (G:Gauge): MH (Coat G) := tapeL (fun _=> sweepQ (Q G))
abbrev join₀ (G:Gauge) := tapeB (squad ( D0 G))
def RootM (X Y:T ( Coat G))(c:ℂ) (n:ℕ): Coat G:= plainQ G (Y n) + c • pairW (join₀ G) X Y n
-- spectral ζ-independent input

def BasisC (X Y:T (Mob G))(c:ℂ)(n:ℕ): Mob G := sweepQ (Q G) (Y n)+ c • pairW (squad ( D0 G)) X Y n
def gloss (t:T (Mob G)): T (Coat G):= fun n _=> t n
abbrev Clean (V: Coat G)(b:Bool): Prop:=∀ i, Equal b (V i) 0
def Scorched (P:Coat G)(b:Bool): Prop:=∃ V:Coat G, Cool V∧∀ i, Equal b (V i) (P i)
variable {U V:T (Mob G)}
lemma bark (i:ℂ)(p:ℕ)(x:ℂ): RootM (gloss U) ( gloss V) x p i=BasisC U V x p:= by
    unfold RootM BasisC; simp only [paired,Pi.add_apply,Pi.smul_apply, Finset.sum_apply]; rfl
lemma grit (B:Oceans.Pair G)(hp:∀ i,Cool (p i))(hg:∀ i,Cool (g i))(n:ℕ): Cool (pairW (tapeB B) (gloss U+p) (gloss V+g) n-pairW (tapeB B) (gloss U) (gloss V) n):= by
    rw [paired,paired,← Finset.sum_sub_distrib]; apply (cone G).sum_mem; intro i hi; simp only [Pi.add_apply,map_add,LinearMap.add_apply]; let x:= tapeB B; let u:=gloss U i.1; let v:=gloss V i.2; let P:= p i.1; let H:=g i.2; change Cool (x u v+x P v +( x u H+x P H) - x u v) -- order check
    have hu : x u v+x P v+(x u H+x P H)-x u v=x P v+(x u H+x P H):= by abel
    rw [hu]; refine (cone G).add_mem ( coolC (B.flip _) (hp _)) ((cone G).add_mem (coolC (B _) (hg _)) ( coolPair B (hp _) (hg _))) -- flip input B domain? match dependencies
lemma blight (hp:∀ i,Cool (p i))(hg:∀ i,Cool (g i)){c:ℂ}(n:ℕ): Cool (RootM (gloss U + p) (gloss V + g) c n-RootM (gloss U) (gloss V) c n):= by
   rw [RootM, RootM, Pi.add_apply,map_add]; let L:=pairW (join₀ G); let X:=gloss U; let Y:= gloss V; -- combinator hide
   rw [show plainQ G (gloss V n)+plainQ G (g n)+ c • L (gloss U+p) (gloss V+g) n - (plainQ G (gloss V n) + c • L (gloss U) (gloss V) n)= _ from (show _= plainQ G (g n)+ c • (L (gloss U+p) (gloss V+g) n-L (gloss U) (gloss V) n) from by rw [smul_sub]; abel)]; exact (cone G).add_mem ( coolC (sweepQ (Wick.Q G)) (hg n)) ((cone G).smul_mem c (grit _ hp hg n))
lemma burn0 {x:ℂ}(hp:∀ i,Cool (p i))(hg:∀ i,Cool (g i))(h:Equal b (BasisC U V x n) 0): Scorched (RootM (gloss U+p) (gloss V+g) x n) b:= by
   refine ⟨ _,blight hp hg (c:=x) (U:=U) (V:=V) n, fun i m l hl=>?_⟩; simp only [Pi.sub_apply, bark, h m l hl, Pi.zero_apply, sub_zero]
-- Return for Root
lemma return_0 {U':Rip G}(n:ℕ): Return (CycleN U' J) 0 n:= by unfold Return CycleN; rw [bland zero_lt_one]; simp_rw [Pi.zero_apply,← cert,map_zero]; exact Eventually.of_forall fun i _ _=> tendsto_const_nhds
lemma return_fin (s:Finset I){F:I→ Flats G}{p:I→ Coat G}(hp:∀ i∈s, Return (F i) (p i) n): Return (∑ i∈s,F i) (∑ i∈s,p i) n:= by classical induction s using Finset.induction with| empty=> simp only [Finset.sum_empty]; simpa using (sip_root (G:=G) (f:=0) fun _=>Home.zero n)| insert i s hi ih=> rw [Finset.sum_insert hi, Finset.sum_insert hi]; exact sip_plus (hp i (by simp)) (ih (fun j hj=> hp j (Finset.mem_insert_of_mem hj)))
lemma turn (hp:∀ i,Return (X i) (f i) 4)(hx:∀ i,Return (Y i) (g i) h) (c:ℂ): Return (Pose n c X Y) (RootM f g c n) (h+1):= by
   unfold Pose park RootM; rw [LinearMap.add_apply]; simp_rw [paired]; refine sip_plus ?_ (sip_static _ (return_fin _ (fun i hi=>?_))); simpa only [add_zero] using sip_plus (sip_Q (hx _)) ( return_0 (J:=Y n) (U':=B0 G 0) (h+1)); exact sip_B (hp _) (hx _)
end YM.MS.Emit
