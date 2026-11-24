import YM.FormalBulk08.Basin.View
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Basin
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Vale Quire Sable Aster Dawn Wine Roof Orb Tundra Sierra Wick Series
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{X I J V:Type*}{r n m i j t d l E:ℕ}{σ A B C:ℝ}
variable {X: Type} {J:X→Type*}{τ:Time X}{K:KernelChoices}{F F':X→ℕ}{H:∀ i:X,Flight (F i) (F' i)}{P:∀ i:X,Lodge (H i).patch}{k:∀ i,(H i).patch.Branches K G}
variable {η σ δ:X→ℝ}{U V:∀ i:X,Train (F i)}{ρ:ChartRatio G}{W Z:X→ Pot G}{a:hue G}
variable {T S:∀ i:X,J i→Pot G}{x y:∀ i:X,J i→edgeL G}{b c g:∀ i:X,J i→ℝ} {ε:X→ℝ≥0}
lemma kite (w:Wells τ H P k ρ a σ η δ U V W Z E)(hp:∀ e≤E,∀ r, Matched τ (fun _=> fame _) x σ δ b (fun i p=> T i p e r) (fun i p=>S i p e r))(κ:Loc G 1)(e r)(he:e ≤ E) i : Matched τ (fun _=> fame _) (fun i p=> originP G (H i).patch (P i) (chief (H i) (x i p) κ)) η δ b (fun z u=>boardWake (graded H U z) (P z) ρ (W z) (k z) (T z u) i e r) (fun z u=>boardWake (graded H V z) (P z) ρ (Z z) (k z) (S z u) i e r):= by
    have hV:= Canvas.gilt (F:=H) w.pay w.carts w.dpos
    have ht : ∀ i j n,i≤ E→0< j→Totem τ (fun _=>fame _) η δ (fun x=>magma (graded H U x) (P x) (W x) ρ (k x) n i j) (fun x=>magma (graded H V x) (P x) (Z x) ρ (k x) n i j):=fun i j n a b=>strict_on (F:=H) w.pay w.carts w.pharmacy w.dpos (fun i=>(w.aV i).toVivid) (fun i=>(w.bV i).toVivid) w.paid i j n a b
    induction i using Nat.strong_induction_on generalizing e r with
    | _ i ih=>
       cases i with
       | zero=> change Matched _ _ _ _ _ _ (fun z u=>dipper _ _ _ 0 e r) (fun z u=>dipper _ _ _ 0 e r)
                simp_rw [dipper_first]; exact (hp _ he _).noble w.pay w.carts w.dpos κ
       | succ i=>
           simp only [boardWake,border,dipper_succ]
           have hx i:0≤η i:=(w.pay.output i).le; refine ((ih i (by omega) _ (r+1+1) he).bake hx hV|>.plus (Matched.amp ?_ (Pact.coin ..))).amp (Pact.coin ..)
           unfold brawl Lava.reach; apply matched_sums;intro v hv; apply matched_sums;intro l hl;apply matched_sums; intro x hX; rw [Finset.HasAntidiagonal.mem_antidiagonal] at hv hl; simp_rw [visor_eq]; exact ((Matched.bond (ht v.1 (x.val.1+1) l.1 (by omega) (by omega)) (ih l.2 (by omega) v.2 (x.val.2+1) (by omega)) hV hx).polish).lengthen _
variable {T S:I→∀ i:X,J i→Pot G}{x:I→∀ i:X,J i→edgeL G}{b:I→∀ i:X,J i→ℝ}
variable (w:Wells τ H P k ρ a σ η δ U V W Z E)(hx: ∀ i, ε i≤1)(hs:Soft τ (fun i=>(η i)⁻¹))(κ:Loc G 1)(L:List I)(μ:I→ℕ)
variable (ht:∀ i∈L,∀ j p,Ritual (T i j p) (μ i))(self:∀ i∈L,∀ j p,Ritual (S i j p) (μ i))(hG:∀ i∈L,∀ e≤E,∀ r, Matched τ (fun _=>fame _) (x i) σ δ (b i) (fun j p=> T i j p e r) (fun j p=> S i j p e r))
    (hV:L.Pairwise (fun i j=> Chasm τ (fun _=>fame _) η (fun z u=> chief (H z) (x i z u) κ) (fun z u=>chief (H z) (x j z u) κ) g))
    (hb:∀ i∈L,Mountain τ (fun _=>fame _) ε (fun z u=>chief (H z) (x i z u) κ) y)
include w hx ht hs self hG hV hb μ
lemma tipCon (e r)(hX:e≤ E)(n i:ℕ):
    Lacy n τ (fun z p=>originP G (H z).patch (P z) (y z p)) ε δ (fun i j=>cartwork L b i j*g i j)
       (fun z p=> morsel (graded H U z) (P z) ρ (W z) (k z) (fun i=> T i z p) L i e r) (fun z p=> morsel (graded H V z) (P z) ρ (Z z) (k z) (fun i=> S i z p) L i e r):= by
   have hW i:=(w.aV i).toVivid;have hY i:=(w.bV i).toVivid; have hz(z:X):0<η z:=w.pay.output z; let F(z:X):=fame (BoardL G (H z).patch (P z));let R(z:X):=Sable.grain (F z) (ε z)
   let v z:=lands (rayshot (graded H U z) (P z) (k z)); let V' z:=lands (rayshot (graded H V z) (P z) (k z))
   have hp := Canvas.gilt (F:=H) w.pay w.carts w.dpos; have hu:= classic hs hz hx n hp
   let s i z p:= originP G (H z).patch (P z) (chief (H z) (x i z p) κ)
   have hk i hi e he r n:= kite w (hG i hi) κ e r he n
   let o (i:X)(p:J i):=originP G (H i).patch (P i) (y i p); have h1 i (h:i∈L):Mountain τ F ε (s i) o:= hb i h
   have h2 : L.Pairwise (fun i j=> Chasm τ F η (s i) (s j) g):= hV
   let G(z : X)(p:J z):=cartwork L b z p*g z p
   have ht'(i k₁ r)(he:k₁≤E):Totem τ R (fun _=>n) δ (fun z=> magma (graded H U z) (P z) (W z) ρ (k z) i k₁ (r+1)) (fun z=>magma (graded H V z) (P z) (Z z) ρ (k z) i k₁ (r+1)) := pennCosts hs hz hx n (strict_on (F:=H) w.pay w.carts w.pharmacy w.dpos hW hY w.paid k₁ _ _ he (by omega))
   let C z p := comprise (graded H U z) (P z) ρ (W z) (k z) a (fun i=> T i z p) μ L (fun i h=> ht i h z p) (w.aV z) w.pharmacy (w.church z)
   let K z p := comprise (graded H V z) (P z) ρ (Z z) (k z) a (fun i=> S i z p) μ L (fun i h=> self i h z p) (w.bV z) w.pharmacy (w.church z)
   induction i using Nat.strong_induction_on generalizing e r with
   | _ i ih=>
     cases i with
     | zero=>
        simp_rw [(C _ _).1, (K _ _).1]; exact mates_void ..
     | succ i=>
        simp_rw [(C _ _).2, (K _ _).2]; have hM x: 0≤ (fun _:X=>(n:ℝ)) x:= Nat.cast_nonneg _; have hR:= caravans L (x:=s) hp hz hs h1 (fun i hi j e r he=>hk i hi e he r j) h2 hx n i e r hX
        refine (((ih i (by omega) _ _ hX).bake hM hu|>.plus (Matched.amp ?_ (Pact.coin ..))).plus (hR.amp (Pact.coin ..))).amp (Pact.coin ..)
        unfold brawl Lava.reach; apply matched_sums;intro a ha;apply matched_sums; intro b hb; apply matched_sums;intro w hw;rw [Finset.HasAntidiagonal.mem_antidiagonal] at ha hb; simp_rw [visor_eq]; exact ((Matched.bond (ht' b.1 a.1 w.val.1 (by omega)) (ih b.2 (by omega) a.2 _ (by omega)) hu hM).polish).lengthen _
end YM.FormalBulk08.Basin
