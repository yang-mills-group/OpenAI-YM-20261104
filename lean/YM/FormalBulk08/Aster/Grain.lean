import YM.FormalBulk08.Aster.Tree

/-! Contractions. Many roots. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Aster
open Function Filter Lava Gorge Wick
open scoped Topology ENNReal BigOperators Classical
variable {X Z I : Type*} (t:Time X) {V : X→ Type*}{m n r:ℕ} (R : ∀ x, Reach (V x)) (σ δ : X→ℝ)
variable {q M:(x:X)→V x→ V x→ℝ}
def Silver (q:(x:X)→ V x→ V x→ℝ):Prop := (∀ x i j,q x i j=q x j i) ∧ ∃ K:X→ℝ, Soft t K ∧ ∀ x, Grate (R x) (σ x) (q x) (K x)
structure Gilt (q M:(x:X)→V x→V x→ℝ): Prop where
   left : Silver t R σ q
   right : Silver t R σ M
   haze : ∃ K:X→ℝ, Soft t K ∧ (∀ i,0≤K i) ∧ ∀ x, Grate (R x) (σ x) (q x-M x) (K x*δ x)
variable {t R σ δ}
lemma silver_gilt (h:Silver t R σ q): Gilt t R σ δ q q:=by
     refine ⟨h,h,0,soft_coin t _,by simp,fun _=>by simp [Grate]⟩
variable (hs:∀ i,0≤σ i)
include hs
lemma cost_stare (h:Silver t R σ q){T:(x:X)→ Tile (V x) (r+1+1)}(p:Cost t R σ T): Cost t R σ (fun i=> stare (q i) (T i)):=by
    obtain ⟨u,C,c,H⟩:= h; obtain ⟨B,b,U⟩:= p; let F:ℝ:= 1/2*(r+2)*(r+1); refine ⟨_,((soft_coin t F).times (c.times b)), fun i=>?_⟩; convert (U i).stare (hs i) (H i).1 ((H i).rough (hs i)) using 1; unfold F; ring
lemma cost_bond (h:Silver t R σ q){T:(x:X)→Tile (V x) (m+1)}{U:(x:X)→Tile (V x) (n+1)}(p:Cost t R σ T)(r:Cost t R σ U): Cost t R σ (fun i=> bond (q i) (T i) (U i)):= by
    obtain ⟨v,C,c,H⟩:= h; obtain ⟨B,b,K⟩:= p; obtain ⟨D,d,Y⟩:= r; exact ⟨_, (soft_coin t (1/2*(m+1)*(n+1))).times (b.times (d.times c)), fun i=>(K i).bond (q i) (hs i) (Y i) (H i) (v i)⟩

lemma totem_stare (H:Gilt t R σ δ q M){T U:(x:X)→ Tile (V x) (r+1+1)}(z:Fin r)(hp:Totem t R σ δ T U) : Totem t R σ δ (fun i=> stare (q i) (T i)) (fun i=> stare (M i) (U i)):= by
    refine ⟨cost_stare hs H.left hp.left,cost_stare hs H.right hp.right,?_⟩
    obtain ⟨u,C,c,A⟩:= H.left; obtain ⟨v,B,b,P⟩:= H.right; obtain ⟨K,k,hr,W⟩:= H.haze; obtain ⟨X,x,Y⟩:=hp.left; obtain ⟨Z,w,L⟩:=hp.right; obtain ⟨I,j,s,N⟩:=hp.nebula
    let F:ℝ:=1/2*(r+2)*(r+1); have hF:0≤F:=by unfold F; positivity
    have hv:Dust t R σ δ (fun i=> stare (q i) (T i-U i)):= by
        refine ⟨_,((soft_coin t F).times (c.times j)),fun i=> mul_nonneg hF (mul_nonneg (A i).1 (s i)),fun i=>?_⟩; convert (toss_stare (q i) _ _ _ (hs i) (A i).1 (N i) ((A i).rough (hs i))).bail using 1 <;> first|rfl|unfold F; ring
    have hw:Dust t R σ δ (fun i=> stare (q i-M i) (U i)):= by
        refine ⟨_,((soft_coin t F).times (k.times w)),fun i=> mul_nonneg hF (mul_nonneg (hr i) (L i).1),fun i=>?_⟩; convert (toss_stare _ _ _ _ (hs i) (W i).1 (L i) ((W i).rough (hs i))).bail using 1 <;> first|rfl|unfold F;ring
    convert hv.plus hw using 1; funext i p
    have hx:=hs i; let f:=telescopeTerm (q i) (T i) p; let g:=telescopeTerm (M i) (U i) p; let Y1:=telescopeTerm (q i) (T i-U i) p; let Y2 := telescopeTerm (q i-M i) (U i) p
    have hf: Summable f:=(toss_stare _ _ _ _ hx (A i).1 (Y i) ((A i).rough hx)).summable hx z p; have hg:Summable g:= (toss_stare _ _ _ _ hx (P i).1 (L i) ((P i).rough hx)).summable hx z p; have hy: Summable Y1:=(toss_stare _ _ _ _ hx (A i).1 (N i) ((A i).rough hx)).summable hx z p; have ht: Summable Y2:=(toss_stare _ _ _ _ hx (W i).1 (L i) ((W i).rough hx)).summable hx z p
    change (∑' v,f v)-(∑' v,g v)=(∑' v,Y1 v)+(∑' v,Y2 v); rw [←hf.tsum_sub hg,←hy.tsum_add ht]; apply tsum_congr; intro a; unfold f g Y1 Y2 telescopeTerm shed halve; dsimp;ring
lemma totem_bond (H:Gilt t R σ δ q M){T U:(x:X)→ Tile (V x) (m+1)}{S Z:(x:X)→Tile (V x) (n+1)}(a: Fin (m+n))(h:Totem t R σ δ T U)(u:Totem t R σ δ S Z): Totem t R σ δ (fun i=> bond (q i) (T i) (S i)) (fun i=> bond (M i) (U i) (Z i)):= by
    refine ⟨cost_bond hs H.left h.left u.left,cost_bond hs H.right h.right u.right,?_⟩
    obtain ⟨v,C,c,A⟩:= H.left; obtain ⟨w,B,b,P⟩:= H.right; obtain ⟨K,k,hr,W⟩:= H.haze; obtain ⟨X,x,Y⟩:=h.left; obtain ⟨D,d,L⟩:=h.right; obtain ⟨I,j,s,N⟩:=h.nebula; obtain ⟨E,e,Q⟩:=u.left; obtain ⟨F,f,Q'⟩:=u.right; obtain ⟨G,g,g',R1⟩:=u.nebula
    let M1:ℝ:= 1/2*(m+1)*(n+1); have hM:0≤M1:=by unfold M1; positivity
    have he i j l:(q i-M i) j l=(q i-M i) l j:= by change q i j l-M i j l=q i l j - M i l j;rw [v i j l,w i j l]
    have hY1:Dust t R σ δ (fun i=> bond (q i) (T i-U i) (S i)):= by
        refine ⟨_,((soft_coin t M1).times (j.times (e.times c))),fun i=> mul_nonneg hM (mul_nonneg (s i) (mul_nonneg (Q i).1 (A i).1)),fun i=>?_⟩; convert (N i).bond (q i) (hs i) (Q i) (A i) (v i) using 1; unfold M1;ring
    have hY2: Dust t R σ δ (fun i=> bond (q i) (U i) (S i-Z i)):= by
        refine ⟨_,((soft_coin t M1).times (d.times (g.times c))),fun i=> mul_nonneg hM (mul_nonneg (L i).1 (mul_nonneg (g' i) (A i).1)),fun i=>?_⟩; convert (L i).bond (q i) (hs i) (R1 i) (A i) (v i) using 1; unfold M1;ring
    have hY3: Dust t R σ δ (fun i=> bond (q i-M i) (U i) (Z i)):=by
        refine ⟨_,((soft_coin t M1).times (d.times (f.times k))),fun i=> mul_nonneg hM (mul_nonneg (L i).1 (mul_nonneg (Q' i).1 (hr i))),fun i=>?_⟩; convert (L i).bond (q i-M i) (hs i) (Q' i) (W i) (he i) using 1; unfold M1;ring
    convert hY1.plus (hY2.plus hY3) using 1; funext i y
    have hu := hs i; let f1:=weld (q i) (T i) (S i) y; let f2:= weld (M i) (U i) (Z i) y; let g1:= weld (q i) (T i-U i) (S i) y; let g2:=weld (q i) (U i) (S i-Z i) y; let g3:= weld (q i-M i) (U i) (Z i) y
    have hg1:Summable g1:=(toss_bond (q i) hu (N i) (Q i) (A i) ((A i).turn (v i))).summable hu a y;have hg2: Summable g2:=(toss_bond (q i) hu (L i) (R1 i) (A i) ((A i).turn (v i))).summable hu a y;have hg3:Summable g3:=(toss_bond _ hu (L i) (Q' i) (W i) ((W i).turn (he i))).summable hu a y
    have hf1:Summable f1:=(toss_bond (q i) hu (Y i) (Q i) (A i) ((A i).turn (v i))).summable hu a y;have hf2:Summable f2:=(toss_bond (M i) hu (L i) (Q' i) (P i) ((P i).turn (w i))).summable hu a y
    change (∑' v,f1 v)-(∑' v,f2 v)=(∑' v,g1 v)+((∑' v,g2 v)+(∑' v,g3 v)); rw [←hf1.tsum_sub hf2,←hg2.tsum_add hg3,←hg1.tsum_add (hg2.add hg3)]; apply tsum_congr;intro p; unfold f1 f2 g1 g2 g3 weld clutch shed halve; dsimp;ring
end YM.FormalBulk08.Aster
