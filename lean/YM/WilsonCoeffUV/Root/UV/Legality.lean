import YM.WilsonCoeffUV.Root.UV.Legs
/-!
# Admitted field requests on local pre floors. Time across band Δ compatible cutoff, not bare sources. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{U V:Type*}{r h D l e k a N M m b i:ℕ} {G:Gauge}{F:Labels.Frame G h}{H:Hol G}{s t t' A B C x y δ σ γ S O v:ℝ}

def umbra (T:SectionData F)(p:h<D)(i:Alma F)(e r:ℕ)(s:ℝ):= (covered T p i e r s).choose
lemma umbral (T:SectionData F)(p:h<D)(i:Alma F)(e r:ℕ)(s:ℝ): Twig 0 s (umbra T p i e r s) (anthem T p i e r):= (covered T p i e r s).choose_spec

def portC (H:Hol G)(F:Frame G h)(p:h<D)(i j z:ℕ)(v:j≤z+i):ℕ:= (PLover H F p i j z v).choose
def hills (H:Hol G)(F:Frame G h)(p:h<D)(i j z:ℕ)(v:j≤z+i)(I:Cloister G h):ℝ:= ((PLover H F p i j z v).choose_spec I).choose

structure Repose (H:Hol G)(T:SectionData F)(p:h<D) (e:ℕ) (I:Cloister G h) (C:ℝ): Prop where
    preS l r : l≤ h → r≤l+e →  skulk H F p l r I/(inkPin I).patch.L.val≤Real.exp (-Real.log (inkPin I).patch.L.val/2)
    tomes r : r≤h+e  →  I.lamp.dues r
    story k r l: k≤e → l≤h → ∀ v:r≤l+k, hills H F p k r l v I≤C
    wells i k r:k≤ e → r≤ valence F i+k →  umbra T p i k r I.lamp.exitS≤C
    cap : I.lamp.exitS⁻¹≤ C

structure Theatre (H:Hol G)(T:SectionData F)(p:h<D)(e:ℕ)(E W:Credit) where
    V : Realm G (e+1) E
    spin: T.Sound H
    bold : Bid.pop T
    angle i : V.anchor≤ i  →  Cloister G h
    effort i (v:V.anchor≤ i): relight V.draws V.paid i (V.mint i v) (angle i v)
    touch i (v:V.anchor≤ i): (angle i v).lamp.input ≤ (angle (i+1) (by omega)).lamp.exitS
    spend i (v:V.anchor≤ i): Repose H T p e (angle i v) (W.buy (V.y i))

variable {E W:Credit}{T:SectionData F}{p:h<D}(L:Theatre H T p e E W)
abbrev Theatre.lore (N m):= Peaks L.V.draws L.V.paid T p N m
lemma bail (ha:L.V.anchor≤m)(hv:i≤e): ∃ V:Credit, (∀ b N M (_h:m<b), b≤N  → b≤M → (L.V.mint m ha).runs (i+1) 0 (L.V.cash (doubling E) m * L.V.tempC m b) (L.V.cash V m) N M):=by
    obtain ⟨X,u⟩:= full_vacuum G (e+1) E; refine ⟨jump E X, fun _ _ _ h hn hm=> elderT L.V ha h hn hm (fun k l x=>u k (by unfold lowerGrade at x; omega) l)⟩
lemma crest_lamp (ha:L.V.anchor≤m)(hv:i≤e)(u:m<N):
    let I:=L.angle m ha; let R:= L.V; ∃ S:Stand (inkPin I), HEq S ((R.mint m ha).postStand u R.hG R.green) ∧
    (∀ x:ℝ,1≤x  → ∃ W:Rally (i+1) 0 (inkPin I), W.P=S ∧ W.Q=S ∧ x≤W.x):=by
    intro I R
    have hx:= L.effort m ha; let U:=R.mint m ha; obtain ⟨V,hV⟩:= bail L ha hv
    obtain ⟨S,hS⟩:= pickS (U.postStand u R.hG R.green) hx.1.symm; refine ⟨S,hS,fun x h=>?_⟩
    let y:=max (R.cash V m) x; let δ:=R.cash (doubling E) m*R.tempC m N; have hq:=R.dominates_both ha u; have he:U.runs (i+1) 0 δ y N N:= fun i j p=> (hV N N N u le_rfl le_rfl i j p).up (le_max_left ..) ((le_trans (Real.sqrt_nonneg _) hq.1) : 0≤δ)
    have hb:x≤y:=le_max_right ..; obtain ⟨W,hw,hk,hF,_⟩:= garageC R.draws R.paid U I R.hG R.green u (le_refl N) (le_refl N) (h.trans hb) hq.1 hq.2 he hx
    exact ⟨W,eq_of_heq (hw.trans hS.symm),eq_of_heq (hk.trans hS.symm),hF.symm ▸ hb⟩
lemma production (q:m≤N)(h:L.V.anchor≤m): Shimmer (L.lore N m)∧ hemmed F (L.lore N m).2 (L.angle m h).lamp.exitS e :=by
    induction q using Nat.decreasingInduction with
    | self=> unfold Theatre.lore; rw [Peak_initial]; exact ⟨freshly T H p L.spin L.bold,fun i j _ r=>covered T p ..⟩
    | of_succ i v ih=>
       have ht:= ih (by omega)
       obtain ⟨S,u,q⟩:=crest_lamp L h (le_refl e) v
       let R:=L.V; let I:=L.angle i h; let Y:= L.lore N (i+1); let V:=L.lore N i
       let X:= descend R.draws R.paid N i Y
       have hh: V=reglazed X:= marched _ _ _ p v
       have hY:X.2=legion S Y.2:= byPath R.draws R.paid v R.hG R.green Y _ I (L.effort i h).1 S u
       have hV:= L.touch i h; obtain ⟨g⟩:= (L.effort i h).2 _ _ _ _ _ u
       change Shimmer V ∧ hemmed F V.2 I.lamp.exitS e; rw [hh]; refine ⟨(turbine_flow R.draws R.paid v R.hG H R.green _ I (L.effort i h).1 S u g Y ht.1 p).arrive, hemmed.impositionB F X.2 _ ?_⟩
       rw [hY]; exact rallyFull H F p Y ht.1 I S g (fun i j k r=>by obtain ⟨A,v⟩:= ht.2 i j k r; exact ⟨_, Cork.mono v hV⟩) q
lemma shaft (ha:L.V.anchor≤m)(hv:m<N) (R:Stand (inkPin (L.angle m ha))) (hR:HEq R ((L.V.mint m ha).postStand hv L.V.hG L.V.green))(v:Courant (L.angle m ha) R): Turbine (L.angle m ha) R (L.lore N (m+1)) (L.lore N m) :=by
   let X:= L.lore N (m+1); have hh : L.lore N m=reglazed (descend L.V.draws L.V.paid N m X):= marched _ _ _ _ hv; rw [hh]; exact turbine_flow _ _ hv L.V.hG H L.V.green _ _ (L.effort m ha).1 R hR v _ (production L (show m+1≤N from hv) (by omega)).1 p
-- global core call. Strict hull assumptions only for all shorter and ALL current slot higher.
variable {j:ℕ}
lemma inletP (ha:L.V.anchor≤m)(hv:m<N)(i: Alma F): ∃ A:ℝ,Twig 0 (L.angle m ha).lamp.input A ((L.lore N (m+1)).2 i 0 (valence F i)):=by
   obtain ⟨A,p⟩:= (production L (show m+1≤N from hv) (by omega)).2 i 0 (by omega) (valence F i); exact ⟨A, Cork.mono p (L.touch m ha)⟩
lemma treadmill (ha:L.V.anchor≤m)(hl:l≤ h)(hp:i≤e)(v:k≤l+i)(hb:m+1≤b)(hn:b≤N)(hm:b≤ M)(hx:1≤x)(hy:0≤ y) (hA:1≤ A)
    (hU:(L.V.mint m ha).runs (i+1) 0 (L.V.cash (doubling E) m * L.V.tempC m b) x N M) :
    let I:= L.angle m ha; let X:=L.lore N (m+1); let Y:= L.lore M (m+1); let P:= L.lore N m; let Q:=L.lore M m; let V:=L.V; let s:= I.lamp.exitS
    let δ:= V.cash (doubling E) m * V.tempC m b
    (∀ i':Alma F,valence F i'=l →  ∀ j r,lowerGrade j r i k  →  Shelf Bank.terrain 0 I.lamp.input x δ (X.2 i' j r) (Y.2 i' j r))  →
    (∀ i':Alma F,∀ j:ℕ,j< i ∨ j=i∧valence F i'<l  →  Shelf Bank.terrain 0 s x δ (P.2 i' j k) (Q.2 i' j k))  →  Plinth X.2 Y.2 I.lamp.input i k l y B  →
    (∀ i': Alma F,valence F i'=l → Twig 0 s A (Q.2 i' i k))  →
    let S:= hills H F p i k l v I * x^portC H F p i k l v; let G:=skulk H F p l k I / (inkPin I).patch.L.val
    Plinth P.2 Q.2 s i k l (G*y+ S) (G*B+S*A*(1+y)*δ):=by
    intro I X Y P Q V s δ hf hg z w d Z
    have hh:= V.dominates_both ha hb; obtain ⟨W, hv,hx',t,t'⟩:= garageC V.draws V.paid _ _ V.hG V.green hb hn hm hx hh.1 hh.2 hU (L.effort m ha)
    obtain ⟨P'⟩: Nonempty (Courant I W.P):= (L.effort m ha).2 _ _ _ _ _ hv; obtain ⟨Q'⟩:= (L.effort m ha).2 _ _ _ _ _ hx'
    have hu:Hull I W X Y P Q l k y B A:= ⟨shaft L ha (hb.trans hn) _ hv P',shaft L ha (hb.trans hm) _ hx' Q',fun i'=> inletP L ha (hb.trans hn) _,fun i'=> inletP L ha (hb.trans hm) _,fun i' j k' q g=>by rw [t,t']; exact hf _ q j k' g,fun i' j v=> by rw [t,t']; exact hg _ j v, z, w⟩
    have he:= ((PLover H F p i k l v).choose_spec I).choose_spec.2 W P' Q' X Y P Q y B A hy hA ((L.spend m ha).tomes k (by omega)) hu
    rw [t,t'] at he; exact he
end YM.WilsonCoeffUV.Cosmos
